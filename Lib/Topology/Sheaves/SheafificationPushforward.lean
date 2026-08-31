/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafification maps into pushforward sheaves

A presheaf map into the underlying presheaf of a genuine pushforward sheaf extends uniquely
through native sheafification.  This supplies the categorical lift used by singular-cochain
pullback, without any exactness hypothesis on pushforward.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SheafificationPushforward

/-- Additive sheafification on the open-set site of `X`. -/
abbrev sheafification (X : TopCat.{0}) :
    TopCat.Presheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Extend a presheaf map through sheafification to a pushforward sheaf. -/
def liftToPushforward {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (η : P ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F).obj) :
    (sheafification Y).obj P ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F :=
  ⟨CategoryTheory.sheafifyLift (Opens.grothendieckTopology Y) η
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F).property⟩

@[reassoc]
theorem toSheafify_liftToPushforward {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (η : P ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F).obj) :
    toSheafify (Opens.grothendieckTopology Y) P ≫ (liftToPushforward f F η).hom = η :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology Y) η
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F).property

theorem liftToPushforward_hom_ext {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {a b : (sheafification Y).obj P ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F}
    (h : toSheafify (Opens.grothendieckTopology Y) P ≫ a.hom =
      toSheafify (Opens.grothendieckTopology Y) P ≫ b.hom) : a = b := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology Y) a.hom b.hom
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F).property h

/-- A raw presheaf pullback induces a map of native sheafifications into pushforward. -/
def sheafifyPullback {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {Q : TopCat.Presheaf AddCommGrpCat.{0} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj Q) :
    (sheafification Y).obj P ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj ((sheafification X).obj Q) :=
  liftToPushforward f ((sheafification X).obj Q)
    (η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
      (toSheafify (Opens.grothendieckTopology X) Q))

@[reassoc]
theorem toSheafify_sheafifyPullback {P : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {Q : TopCat.Presheaf AddCommGrpCat.{0} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj Q) :
    toSheafify (Opens.grothendieckTopology Y) P ≫ (sheafifyPullback f η).hom =
      η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
        (toSheafify (Opens.grothendieckTopology X) Q) :=
  toSheafify_liftToPushforward f ((sheafification X).obj Q) _

/-- Sheafification pullback respects every commuting presheaf square. -/
theorem sheafifyPullback_naturality
    {P₁ P₂ : TopCat.Presheaf AddCommGrpCat.{0} Y}
    {Q₁ Q₂ : TopCat.Presheaf AddCommGrpCat.{0} X}
    (α : P₁ ⟶ P₂) (β : Q₁ ⟶ Q₂)
    (η₁ : P₁ ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj Q₁)
    (η₂ : P₂ ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj Q₂)
    (h : α ≫ η₂ = η₁ ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map β) :
    (sheafification Y).map α ≫ sheafifyPullback f η₂ =
      sheafifyPullback f η₁ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          ((sheafification X).map β) := by
  apply liftToPushforward_hom_ext f
  let R := TopCat.Presheaf.pushforward AddCommGrpCat.{0} f
  have hα : toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      ((sheafification Y).map α).hom =
      α ≫ toSheafify (Opens.grothendieckTopology Y) P₂ :=
    (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology Y) α).symm
  have hβ : β ≫ toSheafify (Opens.grothendieckTopology X) Q₂ =
      toSheafify (Opens.grothendieckTopology X) Q₁ ≫
        ((sheafification X).map β).hom :=
    CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X) β
  have hu₁ : toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      (sheafifyPullback f η₁).hom =
      η₁ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₁) :=
    toSheafify_sheafifyPullback f η₁
  change toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      (((sheafification Y).map α).hom ≫ (sheafifyPullback f η₂).hom) =
    toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      ((sheafifyPullback f η₁).hom ≫ R.map ((sheafification X).map β).hom)
  have h₁ : toSheafify (Opens.grothendieckTopology Y) P₁ ≫
        (((sheafification Y).map α).hom ≫ (sheafifyPullback f η₂).hom) =
      α ≫ (η₂ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) := by
    rw [← Category.assoc, hα, Category.assoc, toSheafify_sheafifyPullback]
    rfl
  have h₂ : α ≫ (η₂ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) =
      η₁ ≫ (R.map β ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) := by
    rw [← Category.assoc, h, Category.assoc]
  have h₃ : η₁ ≫ (R.map β ≫
        R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) =
      η₁ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₁ ≫
        ((sheafification X).map β).hom) := by
    rw [← R.map_comp, hβ]
  have h₄ : η₁ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₁ ≫
        ((sheafification X).map β).hom) =
      η₁ ≫ (R.map (toSheafify (Opens.grothendieckTopology X) Q₁) ≫
        R.map ((sheafification X).map β).hom) := by
    rw [R.map_comp]
  have h₅ : η₁ ≫ (R.map (toSheafify (Opens.grothendieckTopology X) Q₁) ≫
        R.map ((sheafification X).map β).hom) =
      toSheafify (Opens.grothendieckTopology Y) P₁ ≫
        ((sheafifyPullback f η₁).hom ≫ R.map ((sheafification X).map β).hom) := by
    rw [← Category.assoc, ← hu₁]
    exact Category.assoc _ _ _
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end TopCat.SheafificationPushforward
