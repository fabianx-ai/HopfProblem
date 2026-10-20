/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.OpenRestrictionStalk
public import Lib.Topology.Sheaves.OpenRestriction.StalkUnit

/-!
# Germs of the open-restriction unit

This file identifies the transported sheaf pullback unit with the literal presheaf pullback
unit on sections.  It then records the resulting compatibility between ambient germs and the
canonical stalk isomorphism for restriction to an open subspace.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf.OpenRestriction

set_option backward.isDefEq.respectTransparency false in
/-- On sections, the sheaf pullback unit transported to literal open restriction is the
presheaf pullback unit followed by the open-map pullback comparison. -/
theorem nearbyRestrictionUnit_app
    {X : TopCat.{u}} (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : Opens X) :
    ((nearbyRestrictionUnit U).app F).hom.app (op V) =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (inclusion U)).unit.app
        F.presheaf).app (op V) ≫
        ((inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso F.presheaf).hom.app
          (op (preimageOpen U V)) := by
  let adj₁ := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (inclusion U)
  let _ : (Opens.map (inclusion U)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of U)) := by
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map (inclusion U)
    · exact coverPreserving_opens_map (inclusion U)
  let adj₂ := CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map (inclusion U)) AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of U))
  have hleft := adj₁.unit_leftAdjointUniq_hom_app adj₂ F
  have hconstruction := Adjunction.map_restrictFullyFaithful_unit_app
    (((Opens.map (inclusion U)).op.lanAdjunction AddCommGrpCat.{u}).comp
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of U))
        AddCommGrpCat.{u}))
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (Functor.FullyFaithful.id _)
    (L := CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
      (Opens.map (inclusion U)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of U)))
    (R := (Opens.map (inclusion U)).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of U)))
    (Iso.refl _) (Iso.refl _) F
  have hconstructionApp := congrArg (fun k ↦ k.app (op V)) hconstruction
  change (adj₂.unit.app F).hom.app (op V) = _ at hconstructionApp
  have hleft' :
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (inclusion U)).unit.app F ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion U)).map
            (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
                (inclusion U)).leftAdjointUniq adj₂).hom.app F) =
        adj₂.unit.app F := by
    simpa only [adj₁] using hleft
  unfold TopCat.Sheaf.pullbackPushforwardAdjunction at hleft'
  unfold adj₂ at hleft'
  simp only [Functor.id_obj, Functor.comp_obj, pushforward_obj_val,
    TopCat.Presheaf.pushforward_obj_obj, nearbyRestrictionUnit, pullbackRestrictionIso,
    Topology.IsOpenEmbedding.sheafPullbackIso, TopCat.Sheaf.pullbackIso,
    CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso,
    Functor.whiskeringLeft_obj_obj, Iso.trans_hom, Functor.whiskerRight_comp,
    NatTrans.comp_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.app_hom, Functor.FullyFaithful.preimageIso_hom,
    ObjectProperty.ι_obj, Iso.symm_hom, isoSheafify_inv, Functor.map_comp,
    Functor.op_obj, IsOpenMap.pullbackObjIso_hom_app]
  unfold TopCat.Sheaf.pullbackPushforwardAdjunction
  rw [← Category.assoc, ← Category.assoc, hleft']
  rw [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  rw [hconstructionApp]
  dsimp [CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Topology.IsOpenEmbedding.sheafPullback,
    CategoryTheory.Functor.sheafPushforwardContinuous, TopCat.Sheaf.forget]
  simp only [Category.comp_id, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.comp_obj,
    Functor.lanAdjunction_unit]
  unfold TopCat.Presheaf.pullbackPushforwardAdjunction
  rw [Functor.lanAdjunction_unit]
  let P := (Opens.map (inclusion U)).op.lan.obj F.presheaf
  let e := (inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso F.presheaf
  have hsheaf :
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of U))
          AddCommGrpCat.{u}).unit.app P ≫
          ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of U))
            AddCommGrpCat.{u}).map e.hom).hom ≫
          sheafifyLift (Opens.grothendieckTopology (TopCat.of U))
            (𝟙 ((restriction U).obj F).obj) ((restriction U).obj F).property =
        e.hom := by
    simp
    exact Category.comp_id e.hom
  have hsheafApp := congrArg
    (fun k ↦ k.app (op (preimageOpen U V))) hsheaf
  have he :
      ((inclusion_isOpenEmbedding U).isOpenMap.pullbackIso
        (C := AddCommGrpCat.{u})).hom.app F.presheaf = e.hom := by
    rfl
  rw [he]
  simpa only [P, e, NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Functor.op_obj, Category.assoc,
    NatIso.ofComponents_hom_app, IsOpenMap.pullbackObjIso_hom_app,
    IsOpenMap.pullbackIso_hom_app_app] using
      congrArg
        (fun k ↦ ((Opens.map (inclusion U)).op.lanUnit.app F.presheaf).app
          (op V) ≫ k) hsheafApp

set_option backward.isDefEq.respectTransparency false in
/-- An ambient germ followed by the canonical open-restriction stalk comparison is represented
by applying the open-restriction unit on the same ambient neighborhood. -/
theorem germ_stalkIso_hom_nearbyRestrictionUnit
    {X : TopCat.{u}} (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : Opens X) (x : U) (hx : (inclusion U) x ∈ V) :
    F.presheaf.germ V ((inclusion U) x) hx ≫ (stalkIso U F x).hom =
      ((nearbyRestrictionUnit U).app F).hom.app (op V) ≫
        ((restriction U).obj F).presheaf.germ (preimageOpen U V) x hx := by
  let f := inclusion U
  let P := (TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf
  let e := (inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso F.presheaf
  let a := TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f F.presheaf x
  let b := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map e.hom
  have h₁ := TopCat.Presheaf.germ_stalkPullbackHom
    AddCommGrpCat.{u} f F.presheaf x V hx
  have h₂ := TopCat.Presheaf.stalkFunctor_map_germ
    ((Opens.map f).obj V) x hx e.hom
  have hraw :
      (F.presheaf.germ V (f x) hx ≫ a) ≫ b =
        (((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
          F.presheaf).app (op V) ≫ e.hom.app (op ((Opens.map f).obj V))) ≫
          TopCat.Presheaf.germ
            ((openImage U).op ⋙ F.presheaf :
              TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U))
            ((Opens.map f).obj V) x hx := by
    calc
      _ = ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            F.presheaf).app (op V) ≫ P.germ ((Opens.map f).obj V) x hx)) ≫ b := by
        exact congrArg (fun k ↦ k ≫ b) h₁
      _ = ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            F.presheaf).app (op V) ≫
          (P.germ ((Opens.map f).obj V) x hx ≫ b) := Category.assoc _ _ _
      _ = ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            F.presheaf).app (op V) ≫
          (e.hom.app (op ((Opens.map f).obj V)) ≫
            TopCat.Presheaf.germ
              ((openImage U).op ⋙ F.presheaf :
                TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U))
              ((Opens.map f).obj V) x hx) := by
        exact congrArg
          (fun k ↦ ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            F.presheaf).app (op V) ≫ k) h₂
      _ = _ := (Category.assoc _ _ _).symm
  rw [nearbyRestrictionUnit_app U F V]
  change _ =
    (((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (inclusion U)).unit.app F.presheaf).app (op V) ≫
      ((inclusion_isOpenEmbedding U).isOpenMap.pullbackObjIso
        F.presheaf).hom.app (op (preimageOpen U V))) ≫
      TopCat.Presheaf.germ
        ((openImage U).op ⋙ F.presheaf :
          TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U))
        (preimageOpen U V) x hx
  simpa [f, P, e, a, b, stalkIso, presheafStalkIso,
    TopCat.Presheaf.stalkPullbackIso] using hraw

set_option backward.isDefEq.respectTransparency false in
/-- The inverse stalk comparison carries the restricted germ of the open-restriction unit back
to the original ambient germ. -/
theorem stalkIso_inv_germ_nearbyRestrictionUnit
    {X : TopCat.{u}} (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : Opens X) (x : U) (hx : (inclusion U) x ∈ V)
    (s : F.obj.obj (op V)) :
    (stalkIso U F x).inv
        (((restriction U).obj F).presheaf.germ (preimageOpen U V) x hx
          (((nearbyRestrictionUnit U).app F).hom.app (op V) s)) =
      F.presheaf.germ V ((inclusion U) x) hx s := by
  have hhom := ConcreteCategory.congr_hom
    (germ_stalkIso_hom_nearbyRestrictionUnit U F V x hx) s
  simp only [ConcreteCategory.comp_apply] at hhom
  calc
    _ = (stalkIso U F x).inv
        ((stalkIso U F x).hom
          (F.presheaf.germ V ((inclusion U) x) hx s)) := by
      exact congrArg (fun y ↦ (stalkIso U F x).inv y) hhom.symm
    _ = _ := ConcreteCategory.congr_hom
      (stalkIso U F x).hom_inv_id _

end TopCat.Sheaf.OpenRestriction
