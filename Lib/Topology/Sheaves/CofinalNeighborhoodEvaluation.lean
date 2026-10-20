/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks from cofinally bijective neighborhood evaluations

A compatible family of maps from sections over neighborhoods of a point to one fixed
coefficient object induces a map out of the stalk.  If the evaluation is bijective after a
cofinal shrinking of every neighborhood, then the induced stalk map is an isomorphism.

This is the elementary filtered-colimit lemma behind the textbook computation of a puncture
stalk of an open pushforward of a local system by local-monodromy invariants.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

universe u

variable {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
  (x : X) (A : AddCommGrpCat.{u})

/-- A restriction-compatible evaluation of sections over every neighborhood of `x` in one
fixed additive coefficient group. -/
structure CompatibleNeighborhoodEvaluation where
  app : (U : OpenNhds x) → F.obj (op U.1) ⟶ A
  naturality : ∀ {U V : OpenNhds x} (i : U ⟶ V),
    F.map i.op ≫ app U = app V

namespace CompatibleNeighborhoodEvaluation

variable (D : CompatibleNeighborhoodEvaluation F x A)

/-- The compatible evaluations form a cocone over the neighborhood diagram defining the
stalk. -/
def cocone : Cocone ((OpenNhds.inclusion x).op ⋙ F) where
  pt := A
  ι :=
    { app := fun U => D.app (unop U)
      naturality := by
        intro U V i
        change F.map i ≫ D.app (unop V) = D.app (unop U) ≫ 𝟙 A
        rw [Category.comp_id]
        exact D.naturality i.unop }

/-- The map from the stalk induced by compatible neighborhood evaluations. -/
def stalkMap : F.stalk x ⟶ A :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ F) (cocone F x A D)

@[simp]
theorem stalkMap_germ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) :
    stalkMap F x A D (F.germ U x hx s) = D.app ⟨U, hx⟩ s := by
  exact colimit.ι_desc_apply _ _ _

/-- A cofinal supply of neighborhoods on which evaluation is bijective makes the induced stalk
map bijective. -/
theorem stalkMap_bijective_of_cofinal
    (hlocal : ∀ (U : Opens X) (_hx : x ∈ U),
      ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V),
        Function.Bijective (D.app ⟨V, hxV⟩)) :
    Function.Bijective (stalkMap F x A D) := by
  constructor
  · intro a b hab
    obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq a
    obtain ⟨V, hxV, t, rfl⟩ := F.exists_germ_eq b
    rw [stalkMap_germ F x A D, stalkMap_germ F x A D] at hab
    obtain ⟨W, hWUV, hxW, hbij⟩ := hlocal (U ⊓ V) ⟨hxU, hxV⟩
    let iWU : W ⟶ U := homOfLE (hWUV.trans inf_le_left)
    let iWV : W ⟶ V := homOfLE (hWUV.trans inf_le_right)
    apply F.germ_ext W hxW iWU iWV
    apply hbij.injective
    change D.app ⟨W, hxW⟩ (F.map iWU.op s) =
      D.app ⟨W, hxW⟩ (F.map iWV.op t)
    calc
      D.app ⟨W, hxW⟩ (F.map iWU.op s) = D.app ⟨U, hxU⟩ s := by
        have hnat := congrArg
          (fun f : F.obj (op U) ⟶ A => f.hom s)
          (D.naturality (show (⟨W, hxW⟩ : OpenNhds x) ⟶ ⟨U, hxU⟩ from iWU))
        exact hnat
      _ = D.app ⟨V, hxV⟩ t := hab
      _ = D.app ⟨W, hxW⟩ (F.map iWV.op t) := by
        have hnat := congrArg
          (fun f : F.obj (op V) ⟶ A => f.hom t)
          (D.naturality (show (⟨W, hxW⟩ : OpenNhds x) ⟶ ⟨V, hxV⟩ from iWV))
        exact hnat.symm
  · intro a
    obtain ⟨V, _hVtop, hxV, hbij⟩ := hlocal ⊤ (by simp)
    obtain ⟨s, hs⟩ := hbij.surjective a
    refine ⟨F.germ V x hxV s, ?_⟩
    rw [stalkMap_germ F x A D, hs]

/-- The stalk map associated to a cofinally bijective neighborhood evaluation is an
isomorphism. -/
theorem stalkMap_isIso_of_cofinal
    (hlocal : ∀ (U : Opens X) (_hx : x ∈ U),
      ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V),
        Function.Bijective (D.app ⟨V, hxV⟩)) :
    IsIso (stalkMap F x A D) :=
  (ConcreteCategory.isIso_iff_bijective (stalkMap F x A D)).mpr
    (stalkMap_bijective_of_cofinal F x A D hlocal)

end CompatibleNeighborhoodEvaluation

/-! ## Stalks represented by one neighborhood -/

/-- A section over one neighborhood represents the stalk bijectively if restriction from that
neighborhood is bijective on a cofinal supply of smaller neighborhoods.  This form is useful
when the local section spaces are intrinsically constant but no preferred compatible coordinate
on all neighborhoods has been chosen. -/
theorem germ_bijective_of_cofinal_restriction
    (U : Opens X) (hxU : x ∈ U)
    (hlocal : ∀ (V : Opens X) (_hxV : x ∈ V),
      ∃ (W : Opens X) (_hWV : W ≤ V) (_hxW : x ∈ W) (hWU : W ≤ U),
        Function.Bijective (F.map (homOfLE hWU).op)) :
    Function.Bijective (F.germ U x hxU) := by
  constructor
  · intro s t hst
    obtain ⟨V, hxV, iVs, iVt, heq⟩ := F.germ_eq x hxU hxU s t hst
    obtain ⟨W, hWV, _hxW, hWU, hbij⟩ := hlocal V hxV
    apply hbij.injective
    have hrestricted := congrArg
      (fun a ↦ F.map (homOfLE hWV).op a) heq
    simp only [← ConcreteCategory.comp_apply, ← F.map_comp] at hrestricted
    have his : iVs.op ≫ (homOfLE hWV).op = (homOfLE hWU).op :=
      Subsingleton.elim _ _
    have hit : iVt.op ≫ (homOfLE hWV).op = (homOfLE hWU).op :=
      Subsingleton.elim _ _
    rw [his, hit] at hrestricted
    exact hrestricted
  · intro a
    obtain ⟨V, hxV, s, rfl⟩ := F.exists_germ_eq a
    obtain ⟨W, hWV, hxW, hWU, hbij⟩ := hlocal V hxV
    obtain ⟨t, ht⟩ := hbij.surjective (F.map (homOfLE hWV).op s)
    refine ⟨t, ?_⟩
    apply F.germ_ext W hxW (homOfLE hWU) (homOfLE hWV)
    exact ht

/-- Categorical form of `germ_bijective_of_cofinal_restriction`. -/
theorem germ_isIso_of_cofinal_restriction
    (U : Opens X) (hxU : x ∈ U)
    (hlocal : ∀ (V : Opens X) (_hxV : x ∈ V),
      ∃ (W : Opens X) (_hWV : W ≤ V) (_hxW : x ∈ W) (hWU : W ≤ U),
        Function.Bijective (F.map (homOfLE hWU).op)) :
    IsIso (F.germ U x hxU) :=
  (ConcreteCategory.isIso_iff_bijective (F.germ U x hxU)).mpr
    (germ_bijective_of_cofinal_restriction F x U hxU hlocal)

end TopCat.Presheaf
