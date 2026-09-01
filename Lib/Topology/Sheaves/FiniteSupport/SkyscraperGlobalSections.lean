/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# Global sections of a finite sum of skyscraper sheaves

This file isolates the elementary global-sections calculation for a sheaf supported at two
points.  An explicit sheaf isomorphism to the biproduct of skyscraper sheaves canonically
identifies the value on the top open with the product of the two coefficient groups.

The result does not construct a finite-support decomposition.  In applications, the geometric
work is precisely to construct that sheaf isomorphism and identify its coordinate maps.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf.FiniteSupport

variable {X : TopCat.{0}}

/-- A skyscraper sheaf with a canonical classical membership decision. -/
def skyscraperAt (p : X) (A : AddCommGrpCat.{0}) : TopCat.Sheaf AddCommGrpCat X := by
  letI : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  exact skyscraperSheaf p A

/-- Evaluation of an abelian sheaf on the top open. -/
def topEvaluation (X : TopCat.{0}) :
    TopCat.Sheaf AddCommGrpCat X ⥤ AddCommGrpCat :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)

/-- The value on the top open of a skyscraper sheaf is its coefficient object. -/
def skyscraperAtTopIso (p : X) (A : AddCommGrpCat.{0}) :
    (skyscraperAt p A).obj.obj (op (⊤ : Opens X)) ≅ A := by
  letI : ∀ U : Opens X, Decidable (p ∈ U) := fun _ ↦ Classical.dec _
  apply eqToIso
  change (if p ∈ (⊤ : Opens X) then A else ⊤_ AddCommGrpCat) = A
  simp

/-- Evaluation of a sheaf biproduct is canonically the biproduct of the evaluated objects. -/
def sectionsBiprodIso (F G : TopCat.Sheaf AddCommGrpCat X) (U : (Opens X)ᵒᵖ) :
    (F ⊞ G).obj.obj U ≅ F.obj.obj U ⊞ G.obj.obj U := by
  let E : TopCat.Sheaf AddCommGrpCat X ⥤ AddCommGrpCat :=
    TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj U
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

/-- A sheaf decomposition into two skyscrapers gives the corresponding categorical
global-section product. -/
def globalSectionsIsoOfSkyscraperBiprodIso
    {F : TopCat.Sheaf AddCommGrpCat X} (p q : X) (A B : AddCommGrpCat.{0})
    (e : F ≅ skyscraperAt p A ⊞ skyscraperAt q B) :
    (topEvaluation X).obj F ≅ AddCommGrpCat.of (Prod (A : Type) (B : Type)) :=
  (topEvaluation X).mapIso e ≪≫
    sectionsBiprodIso (skyscraperAt p A) (skyscraperAt q B) (op ⊤) ≪≫
      biprod.mapIso (skyscraperAtTopIso p A) (skyscraperAtTopIso q B) ≪≫
        AddCommGrpCat.biprodIsoProd A B

/-- Under a two-skyscraper decomposition, global sections are additively equivalent to the
product of the two coefficient groups. -/
def globalSectionsEquivOfSkyscraperBiprodIso
    {F : TopCat.Sheaf AddCommGrpCat X} (p q : X) (A B : AddCommGrpCat.{0})
    (e : F ≅ skyscraperAt p A ⊞ skyscraperAt q B) :
    ((F.obj.obj (op (⊤ : Opens X))) : Type) ≃+ Prod (A : Type) (B : Type) :=
  (globalSectionsIsoOfSkyscraperBiprodIso p q A B e).addCommGroupIsoToAddEquiv

end TopCat.Sheaf.FiniteSupport

end
