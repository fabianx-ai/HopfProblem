/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.OpenRestriction
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of open restrictions

Restricting a sheaf to an open subspace does not change its stalk at a point of that subspace.
The germ compatibility theorem identifies a restricted germ with the literal ambient germ over
the direct-image open.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}}

/-- The ambient stalk is canonically isomorphic to the stalk of the presheaf obtained by
composing with the direct-image functor on opens. -/
def presheafStalkIso (U : Opens X) (F : TopCat.Presheaf AddCommGrpCat.{0} X) (x : U) :
    F.stalk ((inclusion U) x) ≅
      TopCat.Presheaf.stalk (X := TopCat.of U) ((openImage U).op ⋙ F) x :=
  TopCat.Presheaf.stalkPullbackIso AddCommGrpCat (inclusion U) F x ≪≫
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat x).mapIso
      ((inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso F)

/-- The ambient stalk is canonically isomorphic to the stalk of the open restriction. -/
def stalkIso (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : U) :
    F.presheaf.stalk ((inclusion U) x) ≅
      ((restriction U).obj F).presheaf.stalk x :=
  presheafStalkIso U F.presheaf x

/-- A point of an open in the subspace lies in its direct image in the ambient space. -/
theorem inclusion_mem_openImage (U : Opens X) (V : Opens U) (x : U) (hx : x ∈ V) :
    (inclusion U) x ∈ (openImage U).obj V :=
  ⟨x, hx, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse stalk comparison carries the germ of a restricted section to the literal
ambient germ on the image open. -/
theorem stalkIso_inv_germ
    (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (V : Opens U) (x : U) (hx : x ∈ V)
    (s : F.obj.obj (Opposite.op ((openImage U).obj V))) :
    (stalkIso U F x).inv
        (((restriction U).obj F).presheaf.germ V x hx s) =
      F.presheaf.germ ((openImage U).obj V) ((inclusion U) x)
        (inclusion_mem_openImage U V x hx) s := by
  change (presheafStalkIso U F.presheaf x).inv
      (TopCat.Presheaf.germ (X := TopCat.of U)
        ((openImage U).op ⋙ F.presheaf) V x hx s) = _
  dsimp [presheafStalkIso]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [← ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_stalkPullbackInv]
  let e := (inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso F.presheaf
  have he : e.inv.app (Opposite.op V) ≫
        TopCat.Presheaf.germToPullbackStalk
          AddCommGrpCat (inclusion U) F.presheaf V x hx =
      F.presheaf.germ ((openImage U).obj V) ((inclusion U) x)
        (inclusion_mem_openImage U V x hx) := by
    apply (cancel_epi (e.hom.app (Opposite.op V))).mp
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    dsimp [e, IsOpenMap.pullbackObjIso,
      TopCat.Presheaf.pullbackObjObjOfImageOpen,
      TopCat.Presheaf.germToPullbackStalk]
    apply ((Opens.map (inclusion U)).op
      |>.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.presheaf (Opposite.op V)).hom_ext
    intro j
    rw [Limits.IsColimit.fac,
      Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      Limits.coconeOfDiagramTerminal_ι_app]
    dsimp
    symm
    apply TopCat.Presheaf.germ_res'
  exact ConcreteCategory.congr_hom he s

end TopCat.Sheaf.OpenRestriction
