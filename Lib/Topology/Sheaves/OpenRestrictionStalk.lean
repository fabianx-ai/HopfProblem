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
# Stalks of the restriction to an open subspace

Restriction to an open subspace does not change stalks: `(F|_U)_x ≅ F_x` for `x ∈ U`
(Hartshorne, *Algebraic Geometry*, II §1; Mathlib `TopCat.Presheaf.stalkPullbackIso`).  The germ
compatibility statement identifies the germ of a section of `F|_U` with the germ of the same
section of `F` over the corresponding open of `X`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf.OpenRestriction

universe u

variable {X : TopCat.{u}}

/-- For `x ∈ U`, the stalk of a presheaf `F` on `X` at `x` is canonically the stalk at `x` of the
presheaf `V ↦ F(j(V))` on `U`. -/
def presheafStalkIso (U : Opens X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) (x : U) :
    F.stalk ((inclusion U) x) ≅
      TopCat.Presheaf.stalk (X := TopCat.of U) ((openImage U).op ⋙ F) x :=
  TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} (inclusion U) F x ≪≫
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} x).mapIso
      ((inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso F)

/-- Restriction to an open subspace preserves stalks: `F_x ≅ (F|_U)_x` for `x ∈ U`. -/
def stalkIso (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : U) :
    F.presheaf.stalk ((inclusion U) x) ≅
      ((restriction U).obj F).presheaf.stalk x :=
  presheafStalkIso U F.presheaf x

/-- A point of an open `V` of the subspace `U` lies in the corresponding open of `X`. -/
theorem inclusion_mem_openImage (U : Opens X) (V : Opens U) (x : U) (hx : x ∈ V) :
    (inclusion U) x ∈ (openImage U).obj V :=
  ⟨x, hx, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the stalk comparison carries the germ of a section of `F|_U` over `V` to the
germ of the same section of `F` over the corresponding open of `X`. -/
theorem stalkIso_inv_germ
    (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
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
          AddCommGrpCat.{u} (inclusion U) F.presheaf V x hx =
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
