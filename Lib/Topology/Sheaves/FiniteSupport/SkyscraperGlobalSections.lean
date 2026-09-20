/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# Global sections of a sum of skyscraper sheaves

The skyscraper sheaf at a point `p` with coefficient group `A` has `Γ(X, skyscraper p A) = A`
(Hartshorne, *Algebraic Geometry*, II Ex. 1.17; Mathlib `skyscraperSheaf`).  Since global sections
are an additive functor, a sheaf isomorphic to a biproduct of two skyscrapers has global sections
the product of the two coefficient groups.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf.FiniteSupport

universe u

variable {X : TopCat.{u}}

/-- The skyscraper sheaf at `p` with coefficient group `A`, using classical decidability of
membership (Hartshorne II Ex. 1.17). -/
def skyscraperAt (p : X) (A : AddCommGrpCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X := by
  letI : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  exact skyscraperSheaf p A

/-- The global-sections functor `F ↦ Γ(X, F) = F(⊤)` on sheaves of abelian groups. -/
def topEvaluation (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- `Γ(X, skyscraper p A) = A` (Hartshorne II Ex. 1.17). -/
def skyscraperAtTopIso (p : X) (A : AddCommGrpCat.{u}) :
    (skyscraperAt p A).obj.obj (op (⊤ : Opens X)) ≅ A := by
  letI : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  apply eqToIso
  change (if p ∈ (⊤ : Opens X) then A else ⊤_ AddCommGrpCat.{u}) = A
  simp

/-- Sections over an open commute with biproducts: `(F ⊞ G)(U) ≅ F(U) ⊞ G(U)`. -/
def sectionsBiprodIso (F G : TopCat.Sheaf AddCommGrpCat.{u} X) (U : (Opens X)ᵒᵖ) :
    (F ⊞ G).obj.obj U ≅ F.obj.obj U ⊞ G.obj.obj U := by
  let E : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U
  letI : E.Additive := by
    constructor
    intro F G f g
    rfl
  letI : E.PreservesZeroMorphisms := inferInstance
  letI : PreservesFiniteBiproducts E :=
    Functor.preservesFiniteBiproductsOfAdditive E
  letI : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBiproducts E
  exact E.mapBiprod F G

/-- If `F ≅ skyscraper p A ⊞ skyscraper q B`, then `Γ(X, F) ≅ A × B`. -/
def globalSectionsIsoOfSkyscraperBiprodIso
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (p q : X) (A B : AddCommGrpCat.{u})
    (e : F ≅ skyscraperAt p A ⊞ skyscraperAt q B) :
    (topEvaluation X).obj F ≅ AddCommGrpCat.of (Prod (A : Type u) (B : Type u)) :=
  (topEvaluation X).mapIso e ≪≫
    sectionsBiprodIso (skyscraperAt p A) (skyscraperAt q B) (op ⊤) ≪≫
      biprod.mapIso (skyscraperAtTopIso p A) (skyscraperAtTopIso q B) ≪≫
        AddCommGrpCat.biprodIsoProd A B

/-- Additive form of `globalSectionsIsoOfSkyscraperBiprodIso`: `Γ(X, F) ≃+ A × B` for
`F ≅ skyscraper p A ⊞ skyscraper q B`. -/
def globalSectionsEquivOfSkyscraperBiprodIso
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (p q : X) (A B : AddCommGrpCat.{u})
    (e : F ≅ skyscraperAt p A ⊞ skyscraperAt q B) :
    ((F.obj.obj (op (⊤ : Opens X))) : Type u) ≃+ Prod (A : Type u) (B : Type u) :=
  (globalSectionsIsoOfSkyscraperBiprodIso p q A B e).addCommGroupIsoToAddEquiv

end TopCat.Sheaf.FiniteSupport

end
