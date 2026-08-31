/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgression
public import Lib.Topology.Sheaves.AddCommGrpPushforward
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Resolution transgressions for sheaf pushforward

For a continuous map `f : X ⟶ Y` and an abelian sheaf `F` on `X`, this file constructs the
two-step Ext transgression

`H⁰(Y, Rⁿ⁺¹f_*F) → H²(Y, Rⁿf_*F)`

from Mathlib's actual sheaf pushforward, its actual right-derived functors, and a chosen injective
resolution of `F`.

This is the resolution-level map underlying the expected Leray `d₂`.  This file does not
construct a Leray spectral sequence and does not prove independence from the chosen resolution or
identify this map with the differential of a spectral-sequence object.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray

/-- The small category of sheaves of abelian groups on a topological space. -/
abbrev AbelianSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X

/-- The integral constant sheaf used in Mathlib's definition of sheaf cohomology. -/
abbrev integralSheaf (X : TopCat.{0}) : AbelianSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

/-- Small abelian sheaves form a Grothendieck abelian category and hence have small Ext groups. -/
instance abelianSheafHasExt (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

/-- The additive structure on sheaf cohomology, exposed through its defining Ext group. -/
instance sheafCohomologyAddCommGroup {X : TopCat.{0}} (F : AbelianSheaf X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) :=
  Ext.instAddCommGroup

/-- The actual pushforward of abelian sheaves along a continuous map. -/
abbrev pushforward {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AbelianSheaf X ⥤ AbelianSheaf Y :=
  TopCat.Sheaf.pushforward AddCommGrpCat f

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Compatibility spelling for additivity of abelian-sheaf pushforward.

The canonical typeclass instance is `TopCat.Sheaf.pushforwardAdditive`; this theorem preserves the
previous qualified API without registering a second global instance. -/
theorem pushforwardAdditive : (pushforward f).Additive :=
  TopCat.Sheaf.pushforwardAdditive f

/-- The genuine right-derived sheaf pushforward `Rⁿf_*`. -/
abbrev higherDirectImage (n : ℕ) : AbelianSheaf X ⥤ AbelianSheaf Y :=
  (pushforward f).rightDerived n

/-- The genuine higher direct-image sheaf `Rⁿf_*F`. -/
abbrev higherDirectImageSheaf (F : AbelianSheaf X) (n : ℕ) : AbelianSheaf Y :=
  (higherDirectImage f n).obj F

/-- Any injective resolution computes the genuine higher direct-image sheaf. -/
def higherDirectImageResolutionIso (F : AbelianSheaf X) (I : InjectiveResolution F) (n : ℕ) :
    higherDirectImageSheaf f F n ≅
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj (pushforward f) n

/-- The pushed-forward cochain complex of a chosen injective resolution. -/
abbrev pushedResolution {F : AbelianSheaf X} (I : InjectiveResolution F) :
    CochainComplex (AbelianSheaf Y) ℕ :=
  ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

/-- The actual sheaf-cohomological group `Hᵃ(Y, Rᵇf_*F)`. -/
abbrev E₂ (F : AbelianSheaf X) (a b : ℕ) : Type :=
  CategoryTheory.Sheaf.H.{0} (higherDirectImageSheaf f F b) a

/-- Cohomology of resolution homology is cohomology of the corresponding higher direct image. -/
def resolutionCohomologyIso {F : AbelianSheaf X} (I : InjectiveResolution F) (q p : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushedResolution f I).homology q) p) ≅
      AddCommGrpCat.of (E₂ f F p q) :=
  (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).mapIso
    (higherDirectImageResolutionIso f F I q).symm

/-- Degree-zero cohomology of a higher direct image as morphisms from the integral sheaf into
resolution homology. -/
def resolutionExtZeroIso {F : AbelianSheaf X} (I : InjectiveResolution F) (q : ℕ) :
    AddCommGrpCat.of (E₂ f F 0 q) ≅
      AddCommGrpCat.of (integralSheaf Y ⟶ (pushedResolution f I).homology q) :=
  (Ext.addEquiv₀ (X := integralSheaf Y) (Y := higherDirectImageSheaf f F q)).toAddCommGrpIso ≪≫
    (preadditiveCoyoneda.obj (op (integralSheaf Y))).mapIso
      (higherDirectImageResolutionIso f F I q)

/-- The resolution-level two-step transgression
`H⁰(Y, Rⁿ⁺¹f_*F) → H²(Y, Rⁿf_*F)` as a morphism of additive groups. -/
def resolutionTransgressionMorphism (F : AbelianSheaf X) (n : ℕ) :
    AddCommGrpCat.of (E₂ f F 0 (n + 1)) ⟶ AddCommGrpCat.of (E₂ f F 2 n) :=
  let I := injectiveResolution F
  (resolutionExtZeroIso f I (n + 1)).hom ≫
    ExtTransgression.cochainTransgression (pushedResolution f I) n (integralSheaf Y) ≫
      (extFunctorObj (integralSheaf Y) 2).map ((pushedResolution f I).homologyπ n) ≫
        (resolutionCohomologyIso f I n 2).hom

/-- The resolution transgression as an additive homomorphism. -/
def resolutionTransgressionAdd (F : AbelianSheaf X) (n : ℕ) :
    E₂ f F 0 (n + 1) →+ E₂ f F 2 n :=
  (resolutionTransgressionMorphism f F n).hom

/-- The resolution transgression in integral-linear form. -/
def resolutionTransgression (F : AbelianSheaf X) (n : ℕ) :
    E₂ f F 0 (n + 1) →ₗ[ℤ] E₂ f F 2 n :=
  (resolutionTransgressionAdd f F n).toIntLinearMap

end CategoryTheory.Sheaf.Leray
