/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Lib.Topology.Sheaves.Sheafification
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafification maps into pushforward sheaves

Sheafification is left adjoint to the inclusion of sheaves into presheaves, so a presheaf map
`P ⟶ f_*F` into a sheaf extends uniquely along the unit `P ⟶ P⁺⁺` (Mathlib
`CategoryTheory.sheafifyLift`, `toSheafify_sheafifyLift`).  Applied to a presheaf map
`P ⟶ f_*Q`, this produces a canonical map `P⁺⁺ ⟶ f_*(Q⁺⁺)`, natural in commuting squares of
presheaf maps.  No exactness hypothesis on `f_*` is used.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SheafificationPushforward

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The unique extension of a presheaf map `P ⟶ f_*F` into a sheaf along the sheafification
unit. -/
def liftToPushforward {P : TopCat.Presheaf AddCommGrpCat.{u} Y}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (η : P ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).obj) :
    (TopCat.Sheaf.sheafification Y).obj P ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F :=
  ⟨CategoryTheory.sheafifyLift (Opens.grothendieckTopology Y) η
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).property⟩

/-- The extension of `P ⟶ f_*F` along the sheafification unit restricts to the original map. -/
@[reassoc]
theorem toSheafify_liftToPushforward {P : TopCat.Presheaf AddCommGrpCat.{u} Y}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (η : P ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).obj) :
    toSheafify (Opens.grothendieckTopology Y) P ≫ (liftToPushforward f F η).hom = η :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology Y) η
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).property

/-- Two maps `P⁺⁺ ⟶ f_*F` into a sheaf are equal as soon as they agree after the sheafification
unit. -/
theorem liftToPushforward_hom_ext {P : TopCat.Presheaf AddCommGrpCat.{u} Y}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    {a b : (TopCat.Sheaf.sheafification Y).obj P ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F}
    (h : toSheafify (Opens.grothendieckTopology Y) P ≫ a.hom =
      toSheafify (Opens.grothendieckTopology Y) P ≫ b.hom) : a = b := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology Y) a.hom b.hom
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).property h

/-- A presheaf map `P ⟶ f_*Q` induces a canonical map `P⁺⁺ ⟶ f_*(Q⁺⁺)` of the sheafifications. -/
def sheafifyPullback {P : TopCat.Presheaf AddCommGrpCat.{u} Y}
    {Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj Q) :
    (TopCat.Sheaf.sheafification Y).obj P ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj ((TopCat.Sheaf.sheafification X).obj Q) :=
  liftToPushforward f ((TopCat.Sheaf.sheafification X).obj Q)
    (η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
      (toSheafify (Opens.grothendieckTopology X) Q))

/-- The induced map `P⁺⁺ ⟶ f_*(Q⁺⁺)` restricts along the sheafification unit to the original
presheaf map followed by `f_*` of the unit on `Q`. -/
@[reassoc]
theorem toSheafify_sheafifyPullback {P : TopCat.Presheaf AddCommGrpCat.{u} Y}
    {Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    (η : P ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj Q) :
    toSheafify (Opens.grothendieckTopology Y) P ≫ (sheafifyPullback f η).hom =
      η ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
        (toSheafify (Opens.grothendieckTopology X) Q) :=
  toSheafify_liftToPushforward f ((TopCat.Sheaf.sheafification X).obj Q) _

/-- The construction `P ⟶ f_*Q ↦ P⁺⁺ ⟶ f_*(Q⁺⁺)` is natural: it carries every commuting square
of presheaf maps to a commuting square of sheaf maps. -/
theorem sheafifyPullback_naturality
    {P₁ P₂ : TopCat.Presheaf AddCommGrpCat.{u} Y}
    {Q₁ Q₂ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (α : P₁ ⟶ P₂) (β : Q₁ ⟶ Q₂)
    (η₁ : P₁ ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj Q₁)
    (η₂ : P₂ ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj Q₂)
    (h : α ≫ η₂ = η₁ ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map β) :
    (TopCat.Sheaf.sheafification Y).map α ≫ sheafifyPullback f η₂ =
      sheafifyPullback f η₁ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
          ((TopCat.Sheaf.sheafification X).map β) := by
  apply liftToPushforward_hom_ext f
  let R := TopCat.Presheaf.pushforward AddCommGrpCat.{u} f
  have hα : toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      ((TopCat.Sheaf.sheafification Y).map α).hom =
      α ≫ toSheafify (Opens.grothendieckTopology Y) P₂ :=
    (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology Y) α).symm
  have hβ : β ≫ toSheafify (Opens.grothendieckTopology X) Q₂ =
      toSheafify (Opens.grothendieckTopology X) Q₁ ≫
        ((TopCat.Sheaf.sheafification X).map β).hom :=
    CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X) β
  have hu₁ : toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      (sheafifyPullback f η₁).hom =
      η₁ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₁) :=
    toSheafify_sheafifyPullback f η₁
  change toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      (((TopCat.Sheaf.sheafification Y).map α).hom ≫ (sheafifyPullback f η₂).hom) =
    toSheafify (Opens.grothendieckTopology Y) P₁ ≫
      ((sheafifyPullback f η₁).hom ≫ R.map ((TopCat.Sheaf.sheafification X).map β).hom)
  have h₁ : toSheafify (Opens.grothendieckTopology Y) P₁ ≫
        (((TopCat.Sheaf.sheafification Y).map α).hom ≫ (sheafifyPullback f η₂).hom) =
      α ≫ (η₂ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) := by
    rw [← Category.assoc, hα, Category.assoc, toSheafify_sheafifyPullback]
    rfl
  have h₂ : α ≫ (η₂ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) =
      η₁ ≫ (R.map β ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) := by
    rw [← Category.assoc, h, Category.assoc]
  have h₃ : η₁ ≫ (R.map β ≫
        R.map (toSheafify (Opens.grothendieckTopology X) Q₂)) =
      η₁ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₁ ≫
        ((TopCat.Sheaf.sheafification X).map β).hom) := by
    rw [← R.map_comp, hβ]
  have h₄ : η₁ ≫ R.map (toSheafify (Opens.grothendieckTopology X) Q₁ ≫
        ((TopCat.Sheaf.sheafification X).map β).hom) =
      η₁ ≫ (R.map (toSheafify (Opens.grothendieckTopology X) Q₁) ≫
        R.map ((TopCat.Sheaf.sheafification X).map β).hom) := by
    rw [R.map_comp]
  have h₅ : η₁ ≫ (R.map (toSheafify (Opens.grothendieckTopology X) Q₁) ≫
        R.map ((TopCat.Sheaf.sheafification X).map β).hom) =
      toSheafify (Opens.grothendieckTopology Y) P₁ ≫
        ((sheafifyPullback f η₁).hom ≫ R.map ((TopCat.Sheaf.sheafification X).map β).hom) := by
    rw [← Category.assoc, ← hu₁]
    exact Category.assoc _ _ _
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end TopCat.SheafificationPushforward
