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
# Compatible neighborhood evaluations and the open-restriction unit

This file isolates the formal filtered-colimit part of a special-to-nearby compatibility
argument.  A compatible evaluation after applying a presheaf morphism can be pulled back to
the source presheaf, and the induced stalk map is the composite of the stalk map of the
presheaf morphism with the original evaluation.  For the open-restriction unit, this says that
the two composites agree already on every neighborhood germ.

It also records a cofinal extensionality principle: to identify two maps out of a stalk that
come from compatible neighborhood evaluations, it suffices to identify their evaluations
after a sufficiently small shrinking of every neighborhood.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

universe u

variable {C : Type u} [Category.{0, u} C] [HasColimits C]
  {X : TopCat.{0}} (F : TopCat.Presheaf C X) {x : X} {A : C}

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

variable {X : TopCat.{0}} (U : Opens X)

/-- Pull a compatible evaluation of nearby sections back along the open-restriction unit. -/
def pullbackNearbyEvaluation
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) (A : AddCommGrpCat.{0})
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation
      ((nearbyExtension U).obj F).obj x A) :
    TopCat.Presheaf.CompatibleNeighborhoodEvaluation F.obj x A :=
  D.precomp ((nearbyRestrictionUnit U).app F).hom

/-- The nearby-stalk unit followed by a compatible nearby evaluation is the stalk map of the
evaluation pulled back along the open-restriction unit. -/
theorem nearbyStalkUnit_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) (A : AddCommGrpCat.{0})
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
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) (A : AddCommGrpCat.{0})
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
/-- Naturality of compatible puncture evaluation after first mapping the nearby extension to a
geometric model. -/
theorem nearbyStalkUnit_comp_map_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) (A : AddCommGrpCat.{0})
    (G : TopCat.Presheaf AddCommGrpCat.{0} X)
    (f : ((nearbyExtension U).obj F).obj ⟶ G)
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation G x A) :
    nearbyStalkUnit U F x ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f ≫
        TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap G x A D =
      TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkMap F.obj x A
        (pullbackNearbyEvaluation U F x A (D.precomp f)) := by
  rw [TopCat.Presheaf.CompatibleNeighborhoodEvaluation.stalkFunctorMap_comp_stalkMap]
  exact nearbyStalkUnit_comp_stalkMap U F x A (D.precomp f)

set_option backward.isDefEq.respectTransparency false in
/-- Germ-level compatibility when the nearby extension is first mapped to another nearby
presheaf and only then evaluated.  This is the formal map-naturality statement needed when a
higher direct image is compared with a geometric local-system model before puncture
evaluation. -/
theorem germ_nearbyStalkUnit_comp_map_comp_stalkMap
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (x : X) (A : AddCommGrpCat.{0})
    (G : TopCat.Presheaf AddCommGrpCat.{0} X)
    (f : ((nearbyExtension U).obj F).obj ⟶ G)
    (D : TopCat.Presheaf.CompatibleNeighborhoodEvaluation G x A)
    (V : Opens X) (hx : x ∈ V) :
    TopCat.Presheaf.germ F.obj V x hx ≫ nearbyStalkUnit U F x ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f ≫
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
