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
# The open-restriction unit on stalks

For an open subspace `U ⊆ X`, this file transports the pullback-pushforward adjunction unit to
the literal open restriction functor.  At a point of the complement its target is the filtered
colimit of sections on punctured neighborhoods.  This is the sheaf-theoretic interface often
called a generization map on a stratified `T₁` space; it is not a specialization map between the
stalks at two distinct points.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X)

/-- Generic sheaf pullback along the open inclusion is canonically the literal restriction. -/
def pullbackRestrictionIso :
    TopCat.Sheaf.pullback AddCommGrpCat (inclusion U) ≅ restriction U :=
  (inclusion_isOpenEmbedding U).sheafPullbackIso AddCommGrpCat

/-- Restrict to the open subspace and push forward to the ambient space. -/
abbrev nearbyExtension :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  restriction U ⋙ TopCat.Sheaf.pushforward AddCommGrpCat (inclusion U)

/-- The canonical unit `F ⟶ j_* j^* F`, transported from generic pullback to literal open
restriction. -/
def nearbyRestrictionUnit : 𝟭 (TopCat.Sheaf AddCommGrpCat.{0} X) ⟶ nearbyExtension U :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (inclusion U)).unit ≫
    Functor.whiskerRight (pullbackRestrictionIso U).hom
      (TopCat.Sheaf.pushforward AddCommGrpCat (inclusion U))

/-- The value of `j_*j^*F` on an ambient open `V` is canonically the value of `F` on
`V ∩ U`. -/
def nearbyExtensionObjIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) (V : Opens X) :
    ((nearbyExtension U).obj F).obj.obj (op V) ≅ F.obj.obj (op (V ⊓ U)) := by
  change F.obj.obj (op ((openImage U).obj (preimageOpen U V))) ≅ _
  rw [show (openImage U).obj (preimageOpen U V) = V ⊓ U from
    TopologicalSpace.Opens.functor_map_eq_inf U V]

/-- The nearby-sections diagram over all ambient neighborhoods of `x`. -/
abbrev nearbyNeighborhoodDiagram
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) :=
  (OpenNhds.inclusion x).op ⋙ ((nearbyExtension U).obj F).obj

/-- The target of the open-restriction unit on the stalk at `x`: the filtered colimit of
`F(V ∩ U)` over ambient neighborhoods `V` of `x`. -/
abbrev nearbySectionsStalk
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) : AddCommGrpCat.{0} :=
  TopCat.Presheaf.stalk ((nearbyExtension U).obj F).obj x

theorem nearbySectionsStalk_eq_colimit
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) :
    nearbySectionsStalk U F x = colimit (nearbyNeighborhoodDiagram U F x) :=
  rfl

/-- The canonical map from the ambient stalk to the punctured-neighborhood/nearby-sections
stalk. -/
def nearbyStalkUnit (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) :
    TopCat.Presheaf.stalk F.obj x ⟶ nearbySectionsStalk U F x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((nearbyRestrictionUnit U).app F).hom

/-- The open-restriction stalk unit is natural in the sheaf. -/
theorem nearbyStalkUnit_natural
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom ≫
        nearbyStalkUnit U G x =
      nearbyStalkUnit U F x ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((nearbyExtension U).map f).hom) := by
  change
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((nearbyRestrictionUnit U).app G).hom =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((nearbyRestrictionUnit U).app F).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((nearbyExtension U).map f).hom)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  have h := congrArg (fun k ↦ k.hom) ((nearbyRestrictionUnit U).naturality f)
  change f.hom ≫ ((nearbyRestrictionUnit U).app G).hom =
    ((nearbyRestrictionUnit U).app F).hom ≫ ((nearbyExtension U).map f).hom at h
  exact h

/-- On a germ from an ambient neighborhood, the stalk unit is represented by the corresponding
component of `F ⟶ j_*j^*F`. -/
theorem germ_nearbyStalkUnit
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X)
    (V : Opens X) (hx : x ∈ V) :
    TopCat.Presheaf.germ F.obj V x hx ≫ nearbyStalkUnit U F x =
      ((nearbyRestrictionUnit U).app F).hom.app (op V) ≫
        TopCat.Presheaf.germ ((nearbyExtension U).obj F).obj V x hx :=
  TopCat.Presheaf.stalkFunctor_map_germ V x hx
    ((nearbyRestrictionUnit U).app F).hom

end TopCat.Sheaf.OpenRestriction
