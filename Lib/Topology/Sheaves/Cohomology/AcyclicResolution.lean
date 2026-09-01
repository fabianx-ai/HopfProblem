/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactAugmentedCochainComplex
public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1

/-!
# Sheaf cohomology from an indexed acyclic resolution

This specializes the arbitrary-degree dimension-shifting theorem to additive sheaves.  Mathlib's
canonical degree-zero Ext comparison is applied degreewise, identifying the evaluated resolution
with its literal complex of global sections.  The construction is natural under maps of indexed
resolutions.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace TopCat.SheafCohomology.AcyclicResolution

variable {X : TopCat.{0}}

abbrev Resolution := Ext.AcyclicResolution
  (C := TopCat.Sheaf AddCommGrpCat.{0} X)

variable (R : Resolution (X := X))

/-- Literal global sections of the full indexed resolution complex. -/
abbrev globalComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((TopCat.SheafH1.globalSectionsFunctor X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj R.complex

/-- Positive-degree acyclicity of every resolution term for global sections. -/
def IsAcyclic : Prop :=
  ∀ (i q : ℕ), 0 < q →
    Subsingleton (CategoryTheory.Sheaf.H.{0} (R.X i) q)

theorem isAcyclicFor (h : IsAcyclic R) :
    R.IsAcyclicFor (TopCat.SheafH1.unitSheaf X) := h

/-- Degree-zero Ext and global sections agree as full cochain complexes. -/
def extZeroGlobalIso :
    R.evaluatedComplex (TopCat.SheafH1.unitSheaf X) ≅ globalComplex R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => TopCat.SheafH1.h0GlobalIso (R.X n)) (fun i j hij => by
      subst j
      rw [Functor.mapHomologicalComplex_obj_d, R.evaluatedComplex_d,
        Ext.AcyclicResolution.complex_d]
      exact (TopCat.SheafH1.h0GlobalIso_naturality (R.d i)).symm)

/-- Native Ext-defined sheaf cohomology in degree `n+1` is the corresponding homology of
literal global sections of an acyclic resolution. -/
def extIsoGlobalHomology (h : IsAcyclic R) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (R.Z 0) (n + 1)) ≅
      (globalComplex R).homology (n + 1) := by
  exact Iso.trans
    (R.extIsoHomology (TopCat.SheafH1.unitSheaf X) (isAcyclicFor R h) n)
    (HomologicalComplex.homologyMapIso (extZeroGlobalIso R) (n + 1))

namespace Hom

variable {R S T : Resolution (X := X)} (f : Ext.AcyclicResolution.Hom R S)

/-- The map of literal global-section complexes induced by a map of indexed resolutions. -/
def globalComplexMap : globalComplex R ⟶ globalComplex S :=
  ((TopCat.SheafH1.globalSectionsFunctor X).mapHomologicalComplex
    (ComplexShape.up ℕ)).map f.complexMap

@[simp]
theorem globalComplexMap_id (R : Resolution (X := X)) :
    globalComplexMap (Ext.AcyclicResolution.Hom.id R) = 𝟙 (globalComplex R) := by
  simp [globalComplexMap]

@[simp]
theorem globalComplexMap_comp (f : Ext.AcyclicResolution.Hom R S)
    (g : Ext.AcyclicResolution.Hom S T) :
    globalComplexMap (Ext.AcyclicResolution.Hom.comp f g) =
      globalComplexMap f ≫ globalComplexMap g := by
  simp [globalComplexMap]

/-- The degree-zero Ext/global-sections complex comparison is natural. -/
@[reassoc]
theorem extZeroGlobalIso_naturality :
    f.evaluatedComplexMap (TopCat.SheafH1.unitSheaf X) ≫ (extZeroGlobalIso S).hom =
      (extZeroGlobalIso R).hom ≫ globalComplexMap f := by
  apply HomologicalComplex.hom_ext
  intro n
  change (extFunctorObj (TopCat.SheafH1.unitSheaf X) 0).map (f.x n) ≫
      (TopCat.SheafH1.h0GlobalIso (S.X n)).hom =
    (TopCat.SheafH1.h0GlobalIso (R.X n)).hom ≫
      (TopCat.SheafH1.globalSectionsFunctor X).map (f.x n)
  exact TopCat.SheafH1.h0GlobalIso_naturality (f.x n)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the all-positive-degree sheaf-cohomology comparison. -/
theorem extIsoGlobalHomology_naturality
    (hR : IsAcyclic R) (hS : IsAcyclic S) (n : ℕ) :
    (extFunctorObj (TopCat.SheafH1.unitSheaf X) (n + 1)).map (f.z 0) ≫
        (extIsoGlobalHomology S hS n).hom =
      (extIsoGlobalHomology R hR n).hom ≫
        HomologicalComplex.homologyMap (globalComplexMap f) (n + 1) := by
  let a := (extFunctorObj (TopCat.SheafH1.unitSheaf X) (n + 1)).map (f.z 0)
  let r := (R.extIsoHomology (TopCat.SheafH1.unitSheaf X) (isAcyclicFor R hR) n).hom
  let s := (S.extIsoHomology (TopCat.SheafH1.unitSheaf X) (isAcyclicFor S hS) n).hom
  let eR := (HomologicalComplex.homologyMapIso (extZeroGlobalIso R) (n + 1)).hom
  let eS := (HomologicalComplex.homologyMapIso (extZeroGlobalIso S) (n + 1)).hom
  let b := HomologicalComplex.homologyMap
    (f.evaluatedComplexMap (TopCat.SheafH1.unitSheaf X)) (n + 1)
  let c := HomologicalComplex.homologyMap (globalComplexMap f) (n + 1)
  change a ≫ (s ≫ eS) = (r ≫ eR) ≫ c
  have h₁ : a ≫ s = r ≫ b :=
    f.extIsoHomology_naturality (TopCat.SheafH1.unitSheaf X)
      (isAcyclicFor R hR) (isAcyclicFor S hS) n
  have h₂ : b ≫ eS = eR ≫ c := by
    dsimp only [b, eS, eR, c]
    simpa only [HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMapIso_hom] using
      congrArg (fun k => HomologicalComplex.homologyMap k (n + 1))
        (extZeroGlobalIso_naturality f)
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

end Hom

end TopCat.SheafCohomology.AcyclicResolution
