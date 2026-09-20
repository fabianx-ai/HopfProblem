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

For an open `U ⊆ X` and a sheaf `F` of abelian groups on `X`, the cohomology of `U` with
coefficients in `F` may be computed either as `Ext^n(ℤ_U, F)` on `X` or as `H^n(U, F|_U)` on the
subspace `U`, and the two agree in every degree (Godement, *Topologie algébrique et théorie des
faisceaux*, II.4; Hartshorne, *Algebraic Geometry*, III §6).  The comparison comes from exactness
of restriction to an open subspace, which carries the free sheaf `ℤ_U` to the free sheaf on `U`.

## Main results

* `freeHomEquiv`: maps out of the free sheaf on `U` are sections of `F` over `U`.
* `cohomologyEquiv`: `Ext^n(ℤ_U, F) ≅ H^n(U, F|_U)` in every degree.
* `cohomologyEquiv_naturality`: that comparison is natural in `F`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{u}} (U : Opens X)

/-- The sheaf cohomology group `H^n(U, F|_U)` of the open subspace `U`, as an object of
`AddCommGrpCat`. -/
abbrev restrictedCohomologyGroup
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) : AddCommGrpCat.{u} :=
  (@CategoryTheory.Sheaf.functorH
    (Opens (TopCat.of U)) inferInstance
    (Opens.grothendieckTopology (TopCat.of U)) inferInstance
    (IsGrothendieckAbelian.hasExt _) n).obj ((restriction U).obj F)

/-- The free abelian sheaf represented by the ambient open `U`. -/
abbrev freeOpen : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Sheafification, the free-group adjunction, and Yoneda identify maps from `freeOpen U` with
sections over `U`. -/
def freeHomEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (freeOpen U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv _ F).trans
    (((Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv _ F.obj).trans
      yonedaEquiv)

/-- The identification of maps out of the free sheaf on `U` with sections over `U` is natural in
the coefficient sheaf. -/
theorem freeHomEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (h : freeOpen U ⟶ F) (g : F ⟶ G) :
    freeHomEquiv U G (h ≫ g) = g.hom.app (op U) (freeHomEquiv U F h) := rfl

/-- The representing-section equivalence as an additive equivalence. -/
def freeHomAddEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (freeOpen U ⟶ F) ≃+ F.obj.obj (op U) where
  __ := freeHomEquiv U F
  map_add' _ _ := rfl

/-- The representing-section equivalence commutes with restriction along an inclusion of ambient
opens. -/
theorem freeHomEquiv_naturality_open {U V : Opens X} (i : U ⟶ V)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (h : freeOpen V ⟶ F) :
    freeHomEquiv U F
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map i ≫ h) =
      F.obj.map i.op (freeHomEquiv V F h) := by
  let e₁ := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat
  let e₂ := Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj
  have h₁ := e₁.homEquiv_naturality_left
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map i)) h
  have h₂ := e₂.homEquiv_naturality_left (yoneda.map i) (e₁.homEquiv _ F h)
  change yonedaEquiv (e₂.homEquiv _ F.obj
      (e₁.homEquiv _ F
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map i ≫ h))) =
    (F.obj ⋙ CategoryTheory.forget AddCommGrpCat).map i.op
      (yonedaEquiv (e₂.homEquiv _ F.obj (e₁.homEquiv _ F h)))
  exact (congrArg (fun a => yonedaEquiv (e₂.homEquiv _ F.obj a)) h₁).trans
    ((congrArg yonedaEquiv h₂).trans (yonedaEquiv_naturality _ i).symm)

/-- Additive form of naturality of represented sections under restriction of the ambient open. -/
theorem freeHomAddEquiv_naturality_open {U V : Opens X} (i : U ⟶ V)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (h : freeOpen V ⟶ F) :
    freeHomAddEquiv U F
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map i ≫ h) =
      F.obj.map i.op (freeHomAddEquiv V F h) :=
  freeHomEquiv_naturality_open i F h

/-- The image of the top open of the subspace `U` is `U` itself. -/
theorem openImage_top : (openImage U).obj ⊤ = U := by
  apply Opens.ext
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, by simp, rfl⟩

/-- Global sections of the restriction are sections over the original open. -/
def restrictionGlobalEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((restriction U).obj F).obj.obj (op (⊤ : Opens U)) ≃+ F.obj.obj (op U) :=
  (F.obj.mapIso (eqToIso (congrArg op (openImage_top U)))).addCommGroupIsoToAddEquiv

/-- The identification of global sections of `F|_U` with sections of `F` over `U` is natural in
the coefficient sheaf. -/
theorem restrictionGlobalEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) (s : ((restriction U).obj F).obj.obj (op (⊤ : Opens U))) :
    restrictionGlobalEquiv U G (((restriction U).map g).hom.app (op ⊤) s) =
      g.hom.app (op U) (restrictionGlobalEquiv U F s) := by
  change G.obj.map (eqToHom (congrArg op (openImage_top U)))
      (g.hom.app (op ((openImage U).obj ⊤)) s) =
    g.hom.app (op U) (F.obj.map (eqToHom (congrArg op (openImage_top U))) s)
  exact (g.hom.naturality_apply (eqToHom (congrArg op (openImage_top U))) s).symm

/-- The representing-object comparison for open restriction. -/
def homRestrictionEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (freeOpen U ⟶ F) ≃
      (TopCat.ConstantSheaf.integralSheaf (TopCat.of U) ⟶ (restriction U).obj F) :=
  (freeHomEquiv U F).trans ((restrictionGlobalEquiv U F).toEquiv.symm.trans
    (TopCat.ConstantSheaf.integralHomGlobalEquiv
      (TopCat.of U) ((restriction U).obj F)).toEquiv.symm)

/-- The representing-object comparison is computed on sections: it sends a map out of the free
sheaf on `U` to the map out of `ℤ_U` with the same section over `U`. -/
theorem homRestrictionEquiv_sections (F : TopCat.Sheaf AddCommGrpCat.{u} X)
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

/-- The representing-object comparison for open restriction is natural in the coefficient
sheaf. -/
theorem homRestrictionEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
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

/-- The unit `ℤ_U ⟶ (ℤ_U)|_U` exhibiting the restriction of the free sheaf on `U` as the constant
sheaf `ℤ` on the subspace `U`. -/
def representingUnit :
    TopCat.ConstantSheaf.integralSheaf (TopCat.of U) ⟶ (restriction U).obj (freeOpen U) :=
  homRestrictionEquiv U (freeOpen U) (𝟙 _)

/-- Composing with the representing unit recovers the representing-object comparison. -/
theorem representingUnit_comp {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (h : freeOpen U ⟶ F) :
    representingUnit U ≫ (restriction U).map h = homRestrictionEquiv U F h :=
  (homRestrictionEquiv_naturality U (𝟙 _) h).symm.trans
    (congrArg (homRestrictionEquiv U F) (Category.id_comp h))

/-- Composition with the representing unit is a bijection from maps out of the free sheaf on `U`
to maps out of the constant sheaf `ℤ` on the subspace `U`. -/
theorem representingUnit_bijective (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective
      (fun h : freeOpen U ⟶ F ↦ representingUnit U ≫ (restriction U).map h) := by
  have he : (fun h : freeOpen U ⟶ F ↦ representingUnit U ≫ (restriction U).map h) =
      homRestrictionEquiv U F := funext (representingUnit_comp U)
  rw [he]
  exact (homRestrictionEquiv U F).bijective

/-- Degree zero of the cohomology presheaf is the section group over `U`. -/
def zeroEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    CategoryTheory.Sheaf.H'.{u} F 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (C := TopCat.Sheaf AddCommGrpCat.{u} X)
    (X := freeOpen U) (Y := F)).trans (freeHomAddEquiv U F)

/-- The comparison map `Ext^n(ℤ_U, F) → H^n(U, F|_U)` induced by restriction to `U`. -/
def cohomologyForward (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u} F n U →+
      restrictedCohomologyGroup U F n :=
  Ext.ExactFunctorComparison.map (restriction U) (representingUnit U) F n

/-- The comparison `Ext^n(ℤ_U, F) → H^n(U, F|_U)` is bijective in every degree. -/
theorem cohomologyForward_bijective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Bijective (cohomologyForward U F n) :=
  Ext.ExactFunctorComparison.map_bijective (restriction U) (representingUnit U)
    (representingUnit_bijective U) F n

/-- `Ext^n(ℤ_U, F) ≅ H^n(U, F|_U)`: the value at `U` of the cohomology presheaf on `X` is sheaf
cohomology of the open subspace `U` (Godement II.4; Hartshorne III §6). -/
def cohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u} F n U ≃+
      restrictedCohomologyGroup U F n :=
  AddEquiv.ofBijective (cohomologyForward U F n) (cohomologyForward_bijective U F n)

/-- In degree zero the comparison sends the class of a map out of the free sheaf on `U` to the
class of the corresponding map on the subspace. -/
theorem cohomologyEquiv_mk₀ {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (h : freeOpen U ⟶ F) :
    cohomologyEquiv U F 0 (Ext.mk₀ h) =
      Ext.mk₀ (representingUnit U ≫ (restriction U).map h) :=
  Ext.ExactFunctorComparison.map_mk₀ (restriction U) (representingUnit U) h

/-- The comparison `Ext^n(ℤ_U, F) ≅ H^n(U, F|_U)` is natural in the coefficient sheaf `F`. -/
theorem cohomologyEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : F ⟶ G) (n : ℕ) (x : CategoryTheory.Sheaf.H'.{u} F n U) :
    cohomologyEquiv U G n
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map g).app (op U) x) =
      CategoryTheory.Sheaf.H.map ((restriction U).map g) n
        (cohomologyEquiv U F n x) := by
  exact Ext.ExactFunctorComparison.map_naturality
    (restriction U) (representingUnit U) g x

end TopCat.Sheaf.OpenRestriction
