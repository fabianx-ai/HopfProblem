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
# The unit `F ⟶ j_*j^*F` on stalks

For the inclusion `j : U → X` of an open subspace, the adjunction unit `F ⟶ j_*j^*F` induces a
map on stalks.  At a point `x` its target is the filtered colimit of `F(V ∩ U)` over the
neighbourhoods `V` of `x`, so for `x ∉ U` it is the group of sections of `F` near `x` but away
from the complement of `U` (Iversen, *Cohomology of Sheaves*, II.6; Godement II.2.9).

## Main results

* `nearbyRestrictionUnit`: the unit `F ⟶ j_*j^*F`.
* `nearbyExtensionObjIso`: `(j_*j^*F)(V) ≅ F(V ∩ U)`.
* `nearbyStalkUnit`: the induced map `F_x ⟶ colim_{V ∋ x} F(V ∩ U)`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace TopCat.Sheaf.OpenRestriction

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- Sheaf pullback `j^*` along the inclusion of an open subspace is canonically restriction to
that subspace. -/
def pullbackRestrictionIso :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (inclusion U) ≅ restriction U :=
  (inclusion_isOpenEmbedding U).sheafPullbackIso AddCommGrpCat.{u}

/-- The functor `F ↦ j_*j^*F`: restrict to the open subspace `U` and push forward again. -/
abbrev nearbyExtension :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  restriction U ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion U)

/-- The adjunction unit `F ⟶ j_*j^*F` for the inclusion `j : U → X` of an open subspace. -/
def nearbyRestrictionUnit : 𝟭 (TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ nearbyExtension U :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (inclusion U)).unit ≫
    Functor.whiskerRight (pullbackRestrictionIso U).hom
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion U))

/-- The value of `j_*j^*F` on an ambient open `V` is canonically the value of `F` on
`V ∩ U`. -/
def nearbyExtensionObjIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    ((nearbyExtension U).obj F).obj.obj (op V) ≅ F.obj.obj (op (V ⊓ U)) := by
  change F.obj.obj (op ((openImage U).obj (preimageOpen U V))) ≅ _
  rw [show (openImage U).obj (preimageOpen U V) = V ⊓ U from
    TopologicalSpace.Opens.functor_map_eq_inf U V]

/-- The diagram `V ↦ F(V ∩ U)` over the neighbourhoods `V` of `x`. -/
abbrev nearbyNeighborhoodDiagram
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) :=
  (OpenNhds.inclusion x).op ⋙ ((nearbyExtension U).obj F).obj

/-- The target of the open-restriction unit on the stalk at `x`: the filtered colimit of
`F(V ∩ U)` over ambient neighborhoods `V` of `x`. -/
abbrev nearbySectionsStalk
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) : AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalk ((nearbyExtension U).obj F).obj x

/-- The stalk of `j_*j^*F` at `x` is by definition the filtered colimit of `F(V ∩ U)` over the
neighbourhoods `V` of `x`. -/
theorem nearbySectionsStalk_eq_colimit
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) :
    nearbySectionsStalk U F x = colimit (nearbyNeighborhoodDiagram U F x) :=
  rfl

/-- The map `F_x ⟶ (j_*j^*F)_x = colim_{V ∋ x} F(V ∩ U)` induced by the unit on stalks. -/
def nearbyStalkUnit (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) :
    TopCat.Presheaf.stalk F.obj x ⟶ nearbySectionsStalk U F x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((nearbyRestrictionUnit U).app F).hom

/-- The stalk map induced by the unit `F ⟶ j_*j^*F` is natural in `F`. -/
theorem nearbyStalkUnit_natural
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom ≫
        nearbyStalkUnit U G x =
      nearbyStalkUnit U F x ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((nearbyExtension U).map f).hom) := by
  change
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((nearbyRestrictionUnit U).app G).hom =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((nearbyRestrictionUnit U).app F).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((nearbyExtension U).map f).hom)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  have h := congrArg (fun k ↦ k.hom) ((nearbyRestrictionUnit U).naturality f)
  change f.hom ≫ ((nearbyRestrictionUnit U).app G).hom =
    ((nearbyRestrictionUnit U).app F).hom ≫ ((nearbyExtension U).map f).hom at h
  exact h

/-- On the germ of a section over a neighbourhood `V` of `x`, the stalk map of the unit is the
component of `F ⟶ j_*j^*F` at `V`. -/
theorem germ_nearbyStalkUnit
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X)
    (V : Opens X) (hx : x ∈ V) :
    TopCat.Presheaf.germ F.obj V x hx ≫ nearbyStalkUnit U F x =
      ((nearbyRestrictionUnit U).app F).hom.app (op V) ≫
        TopCat.Presheaf.germ ((nearbyExtension U).obj F).obj V x hx :=
  TopCat.Presheaf.stalkFunctor_map_germ V x hx
    ((nearbyRestrictionUnit U).app F).hom

end TopCat.Sheaf.OpenRestriction
