/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.OpenRestriction.NearbyRestrictionGerm

/-!
# A stalk criterion for the open-restriction unit

The unit `F ⟶ j_*j^*F` is automatically an isomorphism on stalks over the open subspace.
Consequently it is enough to check its stalks on the complement in order to prove that the
unit is an isomorphism.  This is the formal local-to-global bridge behind extension of sections
across a closed complement; it does not assert that any complementary stalk map is invertible.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X)

/-- The stalk of the pushforward of the restriction maps back to the restricted stalk at a
point of the open subspace. -/
def nearbyStalkPushforward (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : U) :
    nearbySectionsStalk U F x.1 ⟶
      TopCat.Presheaf.stalk ((restriction U).obj F).obj x :=
  TopCat.Presheaf.stalkPushforward AddCommGrpCat (inclusion U)
    ((restriction U).obj F).obj x

instance nearbyStalkPushforward_isIso
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : U) :
    IsIso (nearbyStalkPushforward U F x) :=
  TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    AddCommGrpCat (inclusion_isOpenEmbedding U).isInducing
      ((restriction U).obj F).obj x

set_option backward.isDefEq.respectTransparency false in
/-- Over the open subspace, the open-restriction stalk unit followed by the canonical
pushforward-stalk comparison is the usual restriction-stalk isomorphism. -/
theorem nearbyStalkUnit_comp_nearbyStalkPushforward
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : U) :
    nearbyStalkUnit U F x.1 ≫ nearbyStalkPushforward U F x =
      (stalkIso U F x).hom := by
  apply F.presheaf.stalk_hom_ext
  intro V hxV
  rw [← Category.assoc, germ_nearbyStalkUnit]
  have hpush :
      ((nearbyExtension U).obj F).presheaf.germ V x.1 hxV ≫
          nearbyStalkPushforward U F x =
        ((restriction U).obj F).presheaf.germ (preimageOpen U V) x hxV := by
    exact TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat
      (inclusion U) ((restriction U).obj F).presheaf V x hxV
  rw [Category.assoc, hpush]
  exact (germ_stalkIso_hom_nearbyRestrictionUnit U F V x hxV).symm

/-- The open-restriction unit is automatically an isomorphism on every stalk over the open
subspace. -/
theorem nearbyStalkUnit_isIso_of_mem
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) (hx : x ∈ U) :
    IsIso (nearbyStalkUnit U F x) := by
  let xU : U := ⟨x, hx⟩
  have hcomp : IsIso
      (nearbyStalkUnit U F x ≫ nearbyStalkPushforward U F xU) := by
    rw [nearbyStalkUnit_comp_nearbyStalkPushforward U F xU]
    exact (stalkIso U F xU).isIso_hom
  exact (isIso_comp_right_iff
    (nearbyStalkUnit U F x) (nearbyStalkPushforward U F xU)).mp hcomp

/-- To prove `F ⟶ j_*j^*F` is an isomorphism it is enough to prove that its stalk maps are
isomorphisms at points outside the open subspace. -/
theorem nearbyRestrictionUnit_app_isIso_of_isIso_outside
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hout : ∀ (x : X), x ∉ U → IsIso (nearbyStalkUnit U F x)) :
    IsIso ((nearbyRestrictionUnit U).app F) := by
  have stalkwise : ∀ (x : X), IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((nearbyRestrictionUnit U).app F).hom) := by
    intro x
    change IsIso (nearbyStalkUnit U F x)
    by_cases hx : x ∈ U
    · exact nearbyStalkUnit_isIso_of_mem U F x hx
    · exact hout x hx
  haveI := stalkwise
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    ((nearbyRestrictionUnit U).app F)

/-- If the complementary stalk units are isomorphisms, restriction from global sections to the
open subspace is an isomorphism.  The forward map is the global component of
`F ⟶ j_*j^*F`, followed by the canonical identification of pushforward sections with sections
on the open. -/
def globalRestrictionIsoOfIsIsoOutside
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hout : ∀ (x : X), x ∉ U → IsIso (nearbyStalkUnit U F x)) :
    F.obj.obj (op (⊤ : Opens X)) ≅ F.obj.obj (op U) := by
  let _ : IsIso ((nearbyRestrictionUnit U).app F) :=
    nearbyRestrictionUnit_app_isIso_of_isIso_outside U F hout
  let _ : IsIso (((nearbyRestrictionUnit U).app F).hom) := by
    change IsIso ((TopCat.Sheaf.forget AddCommGrpCat X).map
      ((nearbyRestrictionUnit U).app F))
    infer_instance
  let _ : IsIso
      (((nearbyRestrictionUnit U).app F).hom.app (op (⊤ : Opens X))) := by
    infer_instance
  simpa only [Functor.id_obj, top_inf_eq] using
    (asIso (((nearbyRestrictionUnit U).app F).hom.app (op (⊤ : Opens X))) ≪≫
      nearbyExtensionObjIso U F (⊤ : Opens X))

end TopCat.Sheaf.OpenRestriction
