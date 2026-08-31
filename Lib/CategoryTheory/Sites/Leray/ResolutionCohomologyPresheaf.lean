/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.InjectiveResolutionHomology
public import Lib.CategoryTheory.Sites.Leray.HigherDirectImageSheafification
public import Lib.Topology.Sheaves.OpenRestriction.Cohomology

/-!
# Resolution cohomology as a presheaf

This file identifies the homology presheaf of an explicit injective resolution with Mathlib's
native Ext-defined cohomology presheaf in every strictly positive degree.  It then records the
same comparison after exact presheaf pushforward.

The endpoint is a natural isomorphism of presheaves, so restriction maps, germs, and stalks are
included.  No proper-base-change theorem or fibre-cohomology identification is asserted here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian CochainComplex.HomComplex
open CategoryTheory.InjectiveResolution

namespace CategoryTheory.Sheaf.Leray

section SheafSections

variable {X : TopCat.{0}}

open TopCat.Sheaf.OpenRestriction
/-- The free-open-sheaf functor occurring literally in Mathlib's
cohomology presheaf. -/
abbrev freeOpenFunctor (X : TopCat.{0}) :
    Opens X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

/-- Sections on an open as a functor of the coefficient sheaf. -/
abbrev sectionsFunctor (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  (TopCat.Sheaf.forget AddCommGrpCat X).flip.obj (op U)

/-- The free sheaf on an open represents its sections, naturally in
the coefficient sheaf. -/
def freeOpenSectionsIso (U : Opens X) :
    preadditiveCoyoneda.obj (op (freeOpen U)) ≅ sectionsFunctor U :=
  NatIso.ofComponents
    (fun G => (freeHomAddEquiv U G).toAddCommGrpIso)
    (fun g => by
      ext h
      exact freeHomEquiv_naturality U h g)

theorem sectionsFunctor_additive (U : Opens X) : (sectionsFunctor U).Additive where
  map_add := by intros; rfl

attribute [local instance] sectionsFunctor_additive

/-- Evaluation of an abelian presheaf at an open. -/
abbrev presheafEvaluation (U : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)

theorem presheafEvaluation_additive (U : Opens X) :
    (presheafEvaluation U).Additive where
  map_add := by intros; rfl

theorem presheafEvaluation_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (presheafEvaluation U) :=
  inferInstanceAs (PreservesFiniteLimits
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))

theorem presheafEvaluation_preservesFiniteColimits (U : Opens X) :
    PreservesFiniteColimits (presheafEvaluation U) :=
  inferInstanceAs (PreservesFiniteColimits
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))

attribute [local instance] presheafEvaluation_additive
  presheafEvaluation_preservesFiniteLimits presheafEvaluation_preservesFiniteColimits

/-- Representing Hom and sections give isomorphic evaluated complexes. -/
def homSectionsComplexIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (U : Opens X) :
    (((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).obj K) ≅
      (((sectionsFunctor U).mapHomologicalComplex _).obj K) :=
  (NatIso.mapHomologicalComplex (freeOpenSectionsIso U) _).app K

/-- The complex comparison commutes with restriction of opens. -/
@[reassoc]
theorem homSectionsComplexIso_hom_naturality_open
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    {U V : Opens X} (i : U ⟶ V) :
    (NatTrans.mapHomologicalComplex
        (preadditiveCoyoneda.map ((freeOpenFunctor X).map i).op) _).app K ≫
      (homSectionsComplexIso K U).hom =
    (homSectionsComplexIso K V).hom ≫
      (NatTrans.mapHomologicalComplex
        ((TopCat.Sheaf.forget AddCommGrpCat X).flip.map i.op) _).app K := by
  ext n h
  exact freeHomEquiv_naturality_open i (K.X n) h

/-- Exact evaluation commutes with homology, compatibly with the
restriction maps of the presheaf. -/
@[reassoc]
theorem evaluationHomologyIso_hom_naturality_open
    (L : CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ)
    {U V : Opens X} (i : U ⟶ V) (m : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) _).app L) m ≫
      (mapComplexHomologyIso L (presheafEvaluation U) m).hom =
    (mapComplexHomologyIso L (presheafEvaluation V) m).hom ≫
      (L.homology m).map i.op := by
  have h := ShortComplex.homologyMap_mapNatTrans (L.sc m)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op)
  exact (congrArg
    (fun a => a ≫ (mapComplexHomologyIso L (presheafEvaluation U) m).hom) h).trans
      (by
        let e := mapComplexHomologyIso L (presheafEvaluation U) m
        let a := (mapComplexHomologyIso L (presheafEvaluation V) m).hom
        let b := (L.homology m).map i.op
        change (a ≫ b ≫ e.inv) ≫ e.hom = a ≫ b
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Homology of the represented Hom complex is the value of the
actual homology presheaf at the open. -/
def homSectionsHomologyIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (U : Opens X) (m : ℕ) :
    ((((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).obj K).homology m) ≅
      (homologyPresheaf K m).obj (op U) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) m).mapIso
      (homSectionsComplexIso K U) ≪≫
    mapComplexHomologyIso (underlyingPresheafComplex K) (presheafEvaluation U) m

/-- Naturality in the open survives taking homology. -/
@[reassoc]
theorem homSectionsHomologyIso_hom_naturality_open
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    {U V : Opens X} (i : U ⟶ V) (m : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (preadditiveCoyoneda.map ((freeOpenFunctor X).map i).op) _).app K) m ≫
      (homSectionsHomologyIso K U m).hom =
    (homSectionsHomologyIso K V m).hom ≫ (homologyPresheaf K m).map i.op := by
  have h := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) m).map)
    (homSectionsComplexIso_hom_naturality_open K i)
  simp only [Functor.map_comp] at h
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) m
  let a := H.map (homSectionsComplexIso K V).hom
  let b := H.map (homSectionsComplexIso K U).hom
  let c := H.map ((NatTrans.mapHomologicalComplex
    (preadditiveCoyoneda.map ((freeOpenFunctor X).map i).op) _).app K)
  let d := H.map ((NatTrans.mapHomologicalComplex
    ((TopCat.Sheaf.forget AddCommGrpCat X).flip.map i.op) _).app K)
  let eU := mapComplexHomologyIso (underlyingPresheafComplex K)
    (presheafEvaluation U) m
  let eV := mapComplexHomologyIso (underlyingPresheafComplex K)
    (presheafEvaluation V) m
  have hd : d ≫ eU.hom = eV.hom ≫ (homologyPresheaf K m).map i.op :=
    evaluationHomologyIso_hom_naturality_open (underlyingPresheafComplex K) i m
  change c ≫ (b ≫ eU.hom) =
    (a ≫ eV.hom) ≫ (homologyPresheaf K m).map i.op
  calc
    _ = (c ≫ b) ≫ eU.hom := (Category.assoc _ _ _).symm
    _ = (a ≫ d) ≫ eU.hom := congrArg (fun t => t ≫ eU.hom) h
    _ = a ≫ (d ≫ eU.hom) := Category.assoc _ _ _
    _ = a ≫ (eV.hom ≫ (homologyPresheaf K m).map i.op) :=
      congrArg (fun t => a ≫ t) hd
    _ = _ := (Category.assoc _ _ _).symm

/-- The represented Hom-complex homology is the actual homology
presheaf, including restriction maps. -/
def representedHomologyPresheafIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) (m : ℕ) :
    (freeOpenFunctor X).op ⋙ coyonedaHomologyFunctor K m ≅
      homologyPresheaf K m :=
  NatIso.ofComponents (fun U => homSectionsHomologyIso K U.unop m)
    (fun i => homSectionsHomologyIso_hom_naturality_open K i.unop m)

/-- In every positive degree, an explicit injective resolution computes
Mathlib's native sheaf-cohomology presheaf. -/
def resolutionCohomologyPresheafIsoPositive
    {G : TopCat.Sheaf AddCommGrpCat.{0} X} (I : InjectiveResolution G) (n : ℕ) :
    homologyPresheaf I.cocomplex (n + 1) ≅
      CategoryTheory.Sheaf.cohomologyPresheaf G (n + 1) :=
  (representedHomologyPresheafIso I.cocomplex (n + 1)).symm ≪≫
    Functor.isoWhiskerLeft (freeOpenFunctor X).op
      (positiveHomologyExtNatIso I n)

end SheafSections

section Pushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Presheaf pushforward is literal precomposition with inverse image
on opens. -/
abbrev presheafPushforward : TopCat.Presheaf AddCommGrpCat.{0} X ⥤
    TopCat.Presheaf AddCommGrpCat.{0} Y :=
  TopCat.Presheaf.pushforward AddCommGrpCat f

theorem presheafPushforward_additive : (presheafPushforward f).Additive where
  map_add := by intros; rfl

theorem presheafPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (presheafPushforward f) :=
  inferInstanceAs (PreservesFiniteLimits
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj
      (Opens.map f).op))

theorem presheafPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (presheafPushforward f) :=
  inferInstanceAs (PreservesFiniteColimits
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj
      (Opens.map f).op))

attribute [local instance] presheafPushforward_additive
  presheafPushforward_preservesFiniteLimits presheafPushforward_preservesFiniteColimits

/-- Exact presheaf pushforward commutes with homology. -/
def homologyPresheafPushforwardIso
    (K : CochainComplex (AbelianSheaf X) ℕ) (m : ℕ) :
    homologyPresheaf (((pushforward f).mapHomologicalComplex _).obj K) m ≅
      (Opens.map f).op ⋙ homologyPresheaf K m :=
  mapComplexHomologyIso (underlyingPresheafComplex K) (presheafPushforward f) m

/-- Literal positive-degree R1 presheaf comparison: the pushed
resolution homology presheaf is the inverse-image-open cohomology
presheaf, with all restriction maps intact. -/
def pushedResolutionCohomologyPresheafIsoPositive
    {G : AbelianSheaf X} (I : InjectiveResolution G) (n : ℕ) :
    homologyPresheaf (pushedResolution f I) (n + 1) ≅
      (Opens.map f).op ⋙
        CategoryTheory.Sheaf.cohomologyPresheaf G (n + 1) :=
  homologyPresheafPushforwardIso f I.cocomplex (n + 1) ≪≫
    Functor.isoWhiskerLeft (Opens.map f).op
      (resolutionCohomologyPresheafIsoPositive I n)

end Pushforward

end CategoryTheory.Sheaf.Leray
