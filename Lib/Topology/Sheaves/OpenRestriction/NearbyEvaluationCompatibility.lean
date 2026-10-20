/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.CofinalNeighborhoodEvaluation
public import Lib.Topology.Sheaves.OpenRestriction.StalkUnit

/-!
# Compatible neighbourhood evaluations and the unit `F ⟶ j_*j^*F`

A stalk is a filtered colimit over neighbourhoods, so a map out of a stalk is the same thing as a
compatible family of maps out of the sections over each neighbourhood, and two such maps agree as
soon as their families agree after shrinking each neighbourhood once (Mathlib
`TopCat.Presheaf.stalk_hom_ext`, `TopCat.Presheaf.stalkFunctor_map_germ`).  This file records that
extensionality principle and the compatibility of such evaluations with a presheaf morphism, and
applies both to the unit `F ⟶ j_*j^*F` of an open subspace.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

universe u u'

variable {C : Type u} [Category.{u', u} C] [HasColimits C]
  {X : TopCat.{u'}} (F : TopCat.Presheaf C X) {x : X} {A : C}

/-- Cofinal germ extensionality for arbitrary maps out of a stalk.  It is enough to compare the
two maps after shrinking each neighborhood once. -/
theorem stalk_hom_ext_of_cofinal {f g : F.stalk x ⟶ A}
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V),
        F.germ V x hxV ≫ f = F.germ V x hxV ≫ g) :
    f = g := by
  apply F.stalk_hom_ext
  intro U hxU
  obtain ⟨V, hVU, hxV, hV⟩ := hlocal U hxU
  let i : V ⟶ U := homOfLE hVU
  have hpre := congrArg (fun k ↦ F.map i.op ≫ k) hV
  rw [← Category.assoc, F.germ_res i x hxV,
    ← Category.assoc, F.germ_res i x hxV] at hpre
  exact hpre

end TopCat.Presheaf

namespace TopCat.Presheaf.CompatibleNeighborhoodEvaluation

universe u

variable {X : TopCat.{u}} {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
  {x : X} {A : AddCommGrpCat.{u}}

/-- Morphism-level form of the defining germ equation for a compatible neighborhood
evaluation. -/
@[simp]
theorem germ_comp_stalkMap (D : CompatibleNeighborhoodEvaluation F x A)
    (U : Opens X) (hx : x ∈ U) :
    F.germ U x hx ≫ stalkMap F x A D = D.app ⟨U, hx⟩ := by
  ext s
  exact stalkMap_germ F x A D U hx s

/-- Pull a compatible neighborhood evaluation back along a presheaf morphism. -/
def precomp (D : CompatibleNeighborhoodEvaluation G x A) (f : F ⟶ G) :
    CompatibleNeighborhoodEvaluation F x A where
  app U := f.app (op U.1) ≫ D.app U
  naturality := by
    intro U V i
    have hf : F.map i.op ≫ f.app (op U.1) =
        f.app (op V.1) ≫ G.map i.op :=
      f.naturality (X := op V.1) (Y := op U.1) i.op
    rw [← Category.assoc, hf, Category.assoc, D.naturality i]

set_option backward.isDefEq.respectTransparency false in
/-- Taking the stalk of a presheaf morphism and then a compatible evaluation is the stalk map
of the pulled-back evaluation. -/
theorem stalkFunctorMap_comp_stalkMap
    (D : CompatibleNeighborhoodEvaluation G x A) (f : F ⟶ G) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f ≫
        stalkMap G x A D =
      stalkMap F x A (D.precomp f) := by
  apply F.stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, germ_comp_stalkMap, germ_comp_stalkMap]
  rfl

/-- Cofinal extensionality for stalk maps induced by compatible neighborhood evaluations. -/
theorem stalkMap_eq_of_cofinal_app
    (D E : CompatibleNeighborhoodEvaluation F x A)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V),
        D.app ⟨V, hxV⟩ = E.app ⟨V, hxV⟩) :
    stalkMap F x A D = stalkMap F x A E := by
  apply F.stalk_hom_ext
  intro U hxU
  obtain ⟨V, hVU, hxV, hVE⟩ := hlocal U hxU
  let i : (⟨V, hxV⟩ : OpenNhds x) ⟶ ⟨U, hxU⟩ := homOfLE hVU
  have hDE : D.app ⟨U, hxU⟩ = E.app ⟨U, hxU⟩ := by
    rw [← D.naturality i, ← E.naturality i, hVE]
  rw [germ_comp_stalkMap, germ_comp_stalkMap, hDE]

end TopCat.Presheaf.CompatibleNeighborhoodEvaluation

namespace TopCat.Sheaf.OpenRestriction

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- Pull a compatible neighbourhood evaluation of `j_*j^*F` back along the unit `F ⟶ j_*j^*F`. -/
def pullbackNearbyEvaluation
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (A : AddCommGrpCat.{u})
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation
      ((nearbyExtension U).obj F).obj x A) :
    TopCat.Presheaf.CompatibleNeighborhoodEvaluation F.obj x A :=
  D.precomp ((nearbyRestrictionUnit U).app F).hom

/-- The stalk map of the unit followed by the stalk map of an evaluation of `j_*j^*F` is the
stalk map of that evaluation pulled back to `F`. -/
theorem nearbyStalkUnit_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (A : AddCommGrpCat.{u})
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation
      ((nearbyExtension U).obj F).obj x A) :
    nearbyStalkUnit U F x ≫
        TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap
          ((nearbyExtension U).obj F).obj x A D =
      TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap F.obj x A
        (pullbackNearbyEvaluation U F x A D) := by
  apply F.presheaf.stalk_hom_ext
  intro V hx
  rw [← Category.assoc, germ_nearbyStalkUnit, Category.assoc,
    TopCat.Presheaf.CompatibleNeighborhoodEvaluation.germ_comp_stalkMap,
    TopCat.Presheaf.CompatibleNeighborhoodEvaluation.germ_comp_stalkMap]
  rfl

/-- Germ-level form of `nearbyStalkUnit_comp_stalkMap`. -/
theorem germ_nearbyStalkUnit_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (A : AddCommGrpCat.{u})
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation
      ((nearbyExtension U).obj F).obj x A)
    (V : Opens X) (hx : x ∈ V) :
    TopCat.Presheaf.germ F.obj V x hx ≫ nearbyStalkUnit U F x ≫
        TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap
          ((nearbyExtension U).obj F).obj x A D =
      ((nearbyRestrictionUnit U).app F).hom.app (op V) ≫ D.app ⟨V, hx⟩ := by
  rw [← Category.assoc, germ_nearbyStalkUnit, Category.assoc,
    TopCat.Presheaf.CompatibleNeighborhoodEvaluation.germ_comp_stalkMap]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of the unit, followed by a presheaf morphism out of `j_*j^*F` and a compatible
evaluation of the target, is the stalk map of that evaluation pulled back to `F`. -/
theorem nearbyStalkUnit_comp_map_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (A : AddCommGrpCat.{u})
    (G : TopCat.Presheaf AddCommGrpCat.{u} X)
    (f : ((nearbyExtension U).obj F).obj ⟶ G)
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation G x A) :
    nearbyStalkUnit U F x ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f ≫
        TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap G x A D =
      TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap F.obj x A
        (pullbackNearbyEvaluation U F x A (D.precomp f)) := by
  rw [TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkFunctorMap_comp_stalkMap]
  exact nearbyStalkUnit_comp_stalkMap U F x A (D.precomp f)

set_option backward.isDefEq.respectTransparency false in
/-- Germ-level form of `nearbyStalkUnit_comp_map_comp_stalkMap`: on the germ over a neighbourhood
`V` of `x`, the composite is the component of the unit at `V` followed by the morphism and the
evaluation at `V`. -/
theorem germ_nearbyStalkUnit_comp_map_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (A : AddCommGrpCat.{u})
    (G : TopCat.Presheaf AddCommGrpCat.{u} X)
    (f : ((nearbyExtension U).obj F).obj ⟶ G)
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation G x A)
    (V : Opens X) (hx : x ∈ V) :
    TopCat.Presheaf.germ F.obj V x hx ≫ nearbyStalkUnit U F x ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f ≫
        TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap G x A D =
      ((nearbyRestrictionUnit U).app F).hom.app (op V) ≫ f.app (op V) ≫
        D.app ⟨V, hx⟩ := by
  calc
    _ = TopCat.Presheaf.germ F.obj V x hx ≫ nearbyStalkUnit U F x ≫
        TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap
          ((nearbyExtension U).obj F).obj x A (D.precomp f) := by
      rw [TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkFunctorMap_comp_stalkMap]
    _ = ((nearbyRestrictionUnit U).app F).hom.app (op V) ≫
        (D.precomp f).app ⟨V, hx⟩ :=
      germ_nearbyStalkUnit_comp_stalkMap U F x A (D.precomp f) V hx
    _ = _ := rfl

end TopCat.Sheaf.OpenRestriction
