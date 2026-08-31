/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorComparison
public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
public import Lib.Topology.Sheaves.OpenRestriction
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaf cohomology on an open subspace

The free abelian sheaf represented by an ambient open `U` computes the value at `U` of Mathlib's
cohomology presheaf.  Exact restriction to the open subspace identifies this Ext group, in every
degree, with ordinary sheaf cohomology on `U`.

Both sides are Mathlib's native Ext-defined groups.  No chart complex, singular comparison, or
proper-base-change assertion enters this result.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X)

/-- The native sheaf cohomology group on the open subspace, bundled through Mathlib's additive
cohomology functor. -/
abbrev restrictedCohomologyGroup
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) : AddCommGrpCat.{0} :=
  (@CategoryTheory.Sheaf.functorH
    (Opens (TopCat.of U)) inferInstance
    (Opens.grothendieckTopology (TopCat.of U)) inferInstance
    (IsGrothendieckAbelian.hasExt _) n).obj ((restriction U).obj F)

/-- The free abelian sheaf represented by the ambient open `U`. -/
abbrev freeOpen : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Sheafification, the free-group adjunction, and Yoneda identify maps from `freeOpen U` with
sections over `U`. -/
def freeHomEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (freeOpen U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv _ F).trans
    (((Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv _ F.obj).trans
      yonedaEquiv)

theorem freeHomEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen U ⟶ F) (g : F ⟶ G) :
    freeHomEquiv U G (h ≫ g) = g.hom.app (op U) (freeHomEquiv U F h) := rfl

/-- The representing-section equivalence as an additive equivalence. -/
def freeHomAddEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (freeOpen U ⟶ F) ≃+ F.obj.obj (op U) where
  __ := freeHomEquiv U F
  map_add' _ _ := rfl

theorem openImage_top : (openImage U).obj ⊤ = U := by
  apply Opens.ext
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, by simp, rfl⟩

/-- Global sections of the restriction are sections over the original open. -/
def restrictionGlobalEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    ((restriction U).obj F).obj.obj (op (⊤ : Opens U)) ≃+ F.obj.obj (op U) :=
  (F.obj.mapIso (eqToIso (congrArg op (openImage_top U)))).addCommGroupIsoToAddEquiv

theorem restrictionGlobalEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) (s : ((restriction U).obj F).obj.obj (op (⊤ : Opens U))) :
    restrictionGlobalEquiv U G (((restriction U).map g).hom.app (op ⊤) s) =
      g.hom.app (op U) (restrictionGlobalEquiv U F s) := by
  change G.obj.map (eqToHom (congrArg op (openImage_top U)))
      (g.hom.app (op ((openImage U).obj ⊤)) s) =
    g.hom.app (op U) (F.obj.map (eqToHom (congrArg op (openImage_top U))) s)
  exact (g.hom.naturality_apply (eqToHom (congrArg op (openImage_top U))) s).symm

/-- The representing-object comparison for open restriction. -/
def homRestrictionEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (freeOpen U ⟶ F) ≃
      (TopCat.ConstantSheaf.integralSheaf (TopCat.of U) ⟶ (restriction U).obj F) :=
  (freeHomEquiv U F).trans ((restrictionGlobalEquiv U F).toEquiv.symm.trans
    (TopCat.ConstantSheaf.integralHomGlobalEquiv
      (TopCat.of U) ((restriction U).obj F)).toEquiv.symm)

theorem homRestrictionEquiv_sections (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (h : freeOpen U ⟶ F) :
    restrictionGlobalEquiv U F
      (TopCat.ConstantSheaf.integralHomGlobalEquiv
        (TopCat.of U) ((restriction U).obj F) (homRestrictionEquiv U F h)) =
      freeHomEquiv U F h := by
  change restrictionGlobalEquiv U F
    ((TopCat.ConstantSheaf.integralHomGlobalEquiv
      (TopCat.of U) ((restriction U).obj F))
      ((TopCat.ConstantSheaf.integralHomGlobalEquiv
        (TopCat.of U) ((restriction U).obj F)).symm
        ((restrictionGlobalEquiv U F).symm (freeHomEquiv U F h)))) = _
  simp only [AddEquiv.apply_symm_apply]

theorem homRestrictionEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen U ⟶ F) (g : F ⟶ G) :
    homRestrictionEquiv U G (h ≫ g) =
      homRestrictionEquiv U F h ≫ (restriction U).map g := by
  apply (TopCat.ConstantSheaf.integralHomGlobalEquiv
    (TopCat.of U) ((restriction U).obj G)).injective
  apply (restrictionGlobalEquiv U G).injective
  rw [homRestrictionEquiv_sections,
    TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality,
    restrictionGlobalEquiv_naturality, homRestrictionEquiv_sections,
    freeHomEquiv_naturality]

/-- The canonical integral-sheaf map into the restriction of the represented open sheaf. -/
def representingUnit :
    TopCat.ConstantSheaf.integralSheaf (TopCat.of U) ⟶ (restriction U).obj (freeOpen U) :=
  homRestrictionEquiv U (freeOpen U) (𝟙 _)

theorem representingUnit_comp {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen U ⟶ F) :
    representingUnit U ≫ (restriction U).map h = homRestrictionEquiv U F h :=
  (homRestrictionEquiv_naturality U (𝟙 _) h).symm.trans
    (congrArg (homRestrictionEquiv U F) (Category.id_comp h))

theorem representingUnit_bijective (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    Function.Bijective
      (fun h : freeOpen U ⟶ F ↦ representingUnit U ≫ (restriction U).map h) := by
  have he : (fun h : freeOpen U ⟶ F ↦ representingUnit U ≫ (restriction U).map h) =
      homRestrictionEquiv U F := funext (representingUnit_comp U)
  rw [he]
  exact (homRestrictionEquiv U F).bijective

/-- Degree zero of the cohomology presheaf is the section group over `U`. -/
def zeroEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    CategoryTheory.Sheaf.H'.{0} F 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (C := TopCat.Sheaf AddCommGrpCat.{0} X)
    (X := freeOpen U) (Y := F)).trans (freeHomAddEquiv U F)

/-- The canonical exact-restriction map on Ext-defined cohomology. -/
def cohomologyForward (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} F n U →+
      restrictedCohomologyGroup U F n :=
  Ext.ExactFunctorComparison.map (restriction U) (representingUnit U) F n

/-- The open-restriction comparison is bijective in every degree. -/
theorem cohomologyForward_bijective (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    Function.Bijective (cohomologyForward U F n) :=
  Ext.ExactFunctorComparison.map_bijective (restriction U) (representingUnit U)
    (representingUnit_bijective U) F n

/-- Cohomology over `U` in the ambient cohomology presheaf is ordinary sheaf cohomology on the
open subspace. -/
def cohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} F n U ≃+
      restrictedCohomologyGroup U F n :=
  AddEquiv.ofBijective (cohomologyForward U F n) (cohomologyForward_bijective U F n)

theorem cohomologyEquiv_mk₀ {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen U ⟶ F) :
    cohomologyEquiv U F 0 (Ext.mk₀ h) =
      Ext.mk₀ (representingUnit U ≫ (restriction U).map h) :=
  Ext.ExactFunctorComparison.map_mk₀ (restriction U) (representingUnit U) h

/-- The comparison is natural in the coefficient sheaf. -/
theorem cohomologyEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) (n : ℕ) (x : CategoryTheory.Sheaf.H'.{0} F n U) :
    cohomologyEquiv U G n
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map g).app (op U) x) =
      CategoryTheory.Sheaf.H.map ((restriction U).map g) n
        (cohomologyEquiv U F n x) := by
  exact Ext.ExactFunctorComparison.map_naturality
    (restriction U) (representingUnit U) g x

end TopCat.Sheaf.OpenRestriction
