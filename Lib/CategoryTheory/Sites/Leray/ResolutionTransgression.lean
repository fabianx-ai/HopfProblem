/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgressionHomology
public import Lib.Topology.Sheaves.AddCommGrpPushforward
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup
public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
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

from Mathlib's sheaf pushforward `f_*`, its right-derived functors `Rⁿf_* = (f_*).rightDerived n`
(Hartshorne, *Algebraic Geometry*, III.8; Godement II.4.17), and a chosen injective resolution
of `F`.

On the Leray spectral sequence `E₂^{p,q} = Hᵖ(Y, Rᑫf_*F) ⇒ Hᵖ⁺ᑫ(X, F)` (Godement II.4.17.1;
Weibel, *An Introduction to Homological Algebra*, 5.8.6) the map constructed here is the
transgression `d₂ : E₂^{0,n+1} → E₂^{2,n}`; it is built here at the level of a resolution, and
this file neither constructs the spectral sequence nor proves independence of the chosen
resolution.

## Main definitions

* `AbelianSheaf X`, `pushforward f`, `higherDirectImage f n`: the sheaf `f_*` and its right
  derived functors `Rⁿf_*` (Hartshorne III.8).
* `E₂ f F p q`: the group `Hᵖ(Y, Rᑫf_*F)`.
* `resolutionTransgression f F n : E₂ f F 0 (n+1) →ₗ[ℤ] E₂ f F 2 n`: the two-step transgression.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray

universe u

/-- The small category of sheaves of abelian groups on a topological space. -/
abbrev AbelianSheaf (X : TopCat.{u}) := TopCat.Sheaf AddCommGrpCat.{u} X

/-- Compatibility spelling for the canonical integral constant sheaf. -/
abbrev integralSheaf (X : TopCat.{u}) : AbelianSheaf X :=
  TopCat.ConstantSheaf.integralSheaf X

/-- Compatibility spelling for the canonical `HasExt` instance on small abelian sheaves. -/
theorem abelianSheafHasExt (X : TopCat.{u}) : HasExt.{u} (AbelianSheaf.{u} X) :=
  IsGrothendieckAbelian.hasExt _

/-- Compatibility spelling for the canonical additive group on sheaf cohomology. -/
abbrev sheafCohomologyAddCommGroup {X : TopCat.{u}} (F : AbelianSheaf X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{u} F n) :=
  CategoryTheory.Sheaf.cohomologyAddCommGroup F n

/-- The actual pushforward of abelian sheaves along a continuous map. -/
abbrev pushforward {X Y : TopCat.{u}} (f : X ⟶ Y) :
    AbelianSheaf X ⥤ AbelianSheaf Y :=
  TopCat.Sheaf.pushforward AddCommGrpCat f

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

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
abbrev E₂ (F : AbelianSheaf X) (a b : ℕ) :=
  CategoryTheory.Sheaf.H.{u} (higherDirectImageSheaf f F b) a

/-- Cohomology of resolution homology is cohomology of the corresponding higher direct image. -/
def resolutionCohomologyIso {F : AbelianSheaf X} (I : InjectiveResolution F) (q p : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} ((pushedResolution f I).homology q) p) ≅
      AddCommGrpCat.of (E₂ f F p q) :=
  (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).mapIso
    (higherDirectImageResolutionIso f F I q).symm

/-- In Ext coordinates, the forward resolution-cohomology comparison is postcomposition with
the map from resolution homology to the genuine higher direct image. -/
@[simp]
lemma resolutionCohomologyIso_hom_apply {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q p : ℕ)
    (x : Ext.{u} (integralSheaf Y) ((pushedResolution f I).homology q) p) :
    (resolutionCohomologyIso f I q p).hom.hom x =
      x.comp (Ext.mk₀ (higherDirectImageResolutionIso f F I q).inv) (add_zero p) := by
  rfl

/-- In Ext coordinates, the inverse resolution-cohomology comparison is postcomposition with
the map from the genuine higher direct image to resolution homology. -/
@[simp]
lemma resolutionCohomologyIso_inv_apply {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q p : ℕ) (x : E₂ f F p q) :
    (resolutionCohomologyIso f I q p).inv.hom x =
      x.comp (Ext.mk₀ (higherDirectImageResolutionIso f F I q).hom) (add_zero p) := by
  rfl

/-- Degree-zero cohomology of a higher direct image as morphisms from the integral sheaf into
resolution homology. -/
def resolutionExtZeroIso {F : AbelianSheaf X} (I : InjectiveResolution F) (q : ℕ) :
    AddCommGrpCat.of (E₂ f F 0 q) ≅
      AddCommGrpCat.of (integralSheaf Y ⟶ (pushedResolution f I).homology q) :=
  (Ext.addEquiv₀ (X := integralSheaf Y) (Y := higherDirectImageSheaf f F q)).toAddCommGrpIso ≪≫
    (preadditiveCoyoneda.obj (op (integralSheaf Y))).mapIso
      (higherDirectImageResolutionIso f F I q)

/-- The forward degree-zero resolution coordinate is the represented morphism followed by the
higher-direct-image comparison. -/
@[simp]
lemma resolutionExtZeroIso_hom_apply {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q : ℕ) (x : E₂ f F 0 q) :
    (resolutionExtZeroIso f I q).hom.hom x =
      Ext.addEquiv₀ x ≫ (higherDirectImageResolutionIso f F I q).hom := by
  rfl

/-- The inverse degree-zero resolution coordinate is the degree-zero Ext class of the transported
morphism. -/
@[simp]
lemma resolutionExtZeroIso_inv_apply {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q : ℕ)
    (x : integralSheaf Y ⟶ (pushedResolution f I).homology q) :
    (resolutionExtZeroIso f I q).inv.hom x =
      Ext.mk₀ (x ≫ (higherDirectImageResolutionIso f F I q).inv) := by
  rfl

/-- The resolution-level two-step transgression associated to a specified injective resolution,
`H⁰(Y, Rⁿ⁺¹f_*F) → H²(Y, Rⁿf_*F)`, as a morphism of additive groups. -/
def resolutionTransgressionMorphismOfResolution {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) :
    AddCommGrpCat.of (E₂ f F 0 (n + 1)) ⟶ AddCommGrpCat.of (E₂ f F 2 n) :=
  (resolutionExtZeroIso f I (n + 1)).hom ≫
    ExtTransgression.cochainTransgression (C := AbelianSheaf Y)
        (pushedResolution f I) n (integralSheaf Y) ≫
      (extFunctorObj (integralSheaf Y) 2).map ((pushedResolution f I).homologyπ n) ≫
        (resolutionCohomologyIso f I n 2).hom

set_option backward.isDefEq.respectTransparency false in
/-- The resolution transgression is the positive connecting map of the canonical four-term
homology sequence, between the existing degree-zero and degree-two page coordinates. -/
lemma resolutionTransgressionMorphismOfResolution_eq_connectingTwo
    {F : AbelianSheaf X} (I : InjectiveResolution F) (n : ℕ) :
    resolutionTransgressionMorphismOfResolution f I n =
      (resolutionExtZeroIso f I (n + 1)).hom ≫
        (Ext.addEquiv₀ (X := integralSheaf Y)
          (Y := (pushedResolution f I).homology (n + 1))).toAddCommGrpIso.inv ≫
        AddCommGrpCat.ofHom
          ((ExtTransgression.homologyTwoStepResolution
            (C := AbelianSheaf Y) (pushedResolution f I) n).connectingTwo (integralSheaf Y)) ≫
        (resolutionCohomologyIso f I n 2).hom := by
  dsimp [resolutionTransgressionMorphismOfResolution]
  rw [← Category.assoc
    (ExtTransgression.cochainTransgression (C := AbelianSheaf Y)
      (pushedResolution f I) n (integralSheaf Y))
    ((extFunctorObj (integralSheaf Y) 2).map
      ((pushedResolution f I).homologyπ n))
    ((resolutionCohomologyIso f I n 2).hom)]
  rw [ExtTransgression.cochainTransgression_comp_homologyπ]
  simp only [Category.assoc]

/-- The resolution-level two-step transgression
`H⁰(Y, Rⁿ⁺¹f_*F) → H²(Y, Rⁿf_*F)` as a morphism of additive groups, using Mathlib's chosen
injective resolution. -/
def resolutionTransgressionMorphism (F : AbelianSheaf X) (n : ℕ) :
    AddCommGrpCat.of (E₂ f F 0 (n + 1)) ⟶ AddCommGrpCat.of (E₂ f F 2 n) :=
  resolutionTransgressionMorphismOfResolution f (injectiveResolution F) n

/-- The resolution transgression associated to a specified injective resolution, as an additive
homomorphism. -/
def resolutionTransgressionAddOfResolution {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) :
    E₂ f F 0 (n + 1) →+ E₂ f F 2 n :=
  (resolutionTransgressionMorphismOfResolution f I n).hom

set_option backward.isDefEq.respectTransparency false in
/-- Elementwise form of `resolutionTransgressionMorphismOfResolution_eq_connectingTwo`: the
resolution transgression is the native positive two-step homology class between the maintained
degree-zero and degree-two coordinates. -/
lemma resolutionTransgressionAddOfResolution_apply_eq_connectingTwo
    {F : AbelianSheaf X} (I : InjectiveResolution F) (n : ℕ)
    (x : E₂ f F 0 (n + 1)) :
    resolutionTransgressionAddOfResolution f I n x =
      (resolutionCohomologyIso f I n 2).hom.hom
        ((ExtTransgression.homologyTwoStepResolution
          (C := AbelianSheaf Y) (pushedResolution f I) n).connectingTwo (integralSheaf Y)
            (Ext.mk₀ ((resolutionExtZeroIso f I (n + 1)).hom.hom x))) := by
  change (resolutionTransgressionMorphismOfResolution f I n).hom x = _
  rw [resolutionTransgressionMorphismOfResolution_eq_connectingTwo]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A value of the resolution transgression is nonzero exactly when its positive Yoneda
two-step class is nonzero. -/
lemma resolutionTransgressionAddOfResolution_apply_ne_zero_iff_connectingTwo
    {F : AbelianSheaf X} (I : InjectiveResolution F) (n : ℕ)
    (x : E₂ f F 0 (n + 1)) :
    resolutionTransgressionAddOfResolution f I n x ≠ 0 ↔
      (ExtTransgression.homologyTwoStepResolution
        (C := AbelianSheaf Y) (pushedResolution f I) n).connectingTwo (integralSheaf Y)
          (Ext.mk₀ ((resolutionExtZeroIso f I (n + 1)).hom.hom x)) ≠ 0 := by
  rw [resolutionTransgressionAddOfResolution_apply_eq_connectingTwo]
  constructor
  · intro h hy
    apply h
    rw [hy, map_zero]
  · intro hy hmap
    apply hy
    apply (ConcreteCategory.bijective_of_isIso
      (resolutionCohomologyIso f I n 2).hom).1
    rw [hmap, map_zero]

/-- The resolution transgression as an additive homomorphism. -/
def resolutionTransgressionAdd (F : AbelianSheaf X) (n : ℕ) :
    E₂ f F 0 (n + 1) →+ E₂ f F 2 n :=
  (resolutionTransgressionMorphism f F n).hom

/-- The resolution transgression associated to a specified injective resolution, in
integral-linear form. -/
def resolutionTransgressionOfResolution {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) :
    E₂ f F 0 (n + 1) →ₗ[ℤ] E₂ f F 2 n :=
  (resolutionTransgressionAddOfResolution f I n).toIntLinearMap

/-- The resolution transgression in integral-linear form. -/
def resolutionTransgression (F : AbelianSheaf X) (n : ℕ) :
    E₂ f F 0 (n + 1) →ₗ[ℤ] E₂ f F 2 n :=
  (resolutionTransgressionAdd f F n).toIntLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- Chosen-resolution specialization of the valuewise nonvanishing criterion. -/
lemma resolutionTransgression_apply_ne_zero_iff_connectingTwo
    (F : AbelianSheaf X) (n : ℕ) (x : E₂ f F 0 (n + 1)) :
    resolutionTransgression f F n x ≠ 0 ↔
      (ExtTransgression.homologyTwoStepResolution
        (C := AbelianSheaf Y)
        (pushedResolution f (injectiveResolution F)) n).connectingTwo (integralSheaf Y)
          (Ext.mk₀ ((resolutionExtZeroIso f (injectiveResolution F) (n + 1)).hom.hom x)) ≠
            0 := by
  exact resolutionTransgressionAddOfResolution_apply_ne_zero_iff_connectingTwo
    f (injectiveResolution F) n x

end CategoryTheory.Sheaf.Leray
