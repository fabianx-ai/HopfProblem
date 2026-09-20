/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

module

public import Lib.CategoryTheory.Sites.Leray.ResolutionTransgression
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Higher direct images as sheafified resolution cohomology

For a continuous map `f : X ⟶ Y`, an abelian sheaf `F` on `X`, and an injective resolution
`I` of `F`, this file identifies the genuine derived pushforward `Rⁿf_*F` with the
sheafification of the presheaf

`U ↦ Hⁿ(Γ(f⁻¹ U, I))`.

This is the resolution form of Hartshorne, *Algebraic Geometry*, III.8.1 (`Rⁱf_*F` is the
sheafification of the presheaf `V ↦ Hⁱ(f⁻¹V, F)`); see also Godement, *Topologie algébrique et
théorie des faisceaux*, II.4.17.1.  It uses only exactness of filtered colimits, exactness of
evaluation and presheaf pushforward, and exactness of abelian sheafification (Godement II.1.2).
It does **not** assert proper base change, identify the displayed resolution cohomology with the
cohomology of a fibre, or compute any local monodromy.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open TopCat.Presheaf

namespace CategoryTheory.Sheaf.Leray

universe u

section Generic

variable {X : TopCat.{u}} (x : X)

/-- Presheaf stalks preserve finite limits: they are filtered colimits of evaluations, and
filtered colimits of abelian groups are exact. -/
instance presheafStalk_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  change PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

/-- Presheaf stalks preserve finite colimits. -/
instance presheafStalk_preservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  change PreservesFiniteColimits
    ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

section ExactFunctor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {ι : Type*} {c : ComplexShape ι}

/-- An additive homology-preserving functor commutes with the homology of a whole complex. -/
def mapComplexHomologyIso (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] (n : ι) :
    ((F.mapHomologicalComplex c).obj K).homology n ≅ F.obj (K.homology n) :=
  (K.sc n).mapHomologyIso F

/-- Naturality of the forward homology comparison. -/
@[reassoc] theorem mapComplexHomologyIso_hom_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] (n : ι) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map φ) n ≫
      (mapComplexHomologyIso L F n).hom =
        (mapComplexHomologyIso K F n).hom ≫ F.map (HomologicalComplex.homologyMap φ n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C c n).map φ) F

/-- Naturality of the inverse homology comparison. -/
@[reassoc] theorem mapComplexHomologyIso_inv_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] (n : ι) :
    F.map (HomologicalComplex.homologyMap φ n) ≫
      (mapComplexHomologyIso L F n).inv =
        (mapComplexHomologyIso K F n).inv ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map φ) n :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor C c n).map φ) F

end ExactFunctor

/-- Forgetting the sheaf condition gives the underlying complex of presheaves. -/
abbrev underlyingPresheafComplex (K : CochainComplex (AbelianSheaf X) ℕ) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  ((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).obj K

/-- Take homology degreewise after forgetting a complex of sheaves to presheaves. -/
abbrev homologyPresheaf (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat X :=
  (underlyingPresheafComplex K).homology n

/-- The stalk of the homology sheaf equals the stalk of the presheaf obtained by taking
homology before sheafification. -/
def stalkHomologyPresheafIso (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    TopCat.Presheaf.stalk (K.homology n).obj x ≅
      TopCat.Presheaf.stalk (homologyPresheaf K n) x :=
  (mapComplexHomologyIso K
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) n).symm ≪≫
    mapComplexHomologyIso (underlyingPresheafComplex K)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) n

/-- The native abelian sheafification functor on a topological space. -/
abbrev sheafification (X : TopCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X ⥤ AbelianSheaf X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

/-- Abelian sheafification is additive. -/
instance sheafification_additive (X : TopCat.{u}) : (sheafification X).Additive :=
  inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive

/-- Abelian sheafification is left exact: it preserves finite limits. -/
instance sheafification_preservesFiniteLimits (X : TopCat.{u}) :
    PreservesFiniteLimits (sheafification X) :=
  inferInstanceAs (PreservesFiniteLimits
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- Abelian sheafification is right exact: being a left adjoint, it preserves finite colimits.
Together with the previous instance this is exactness of sheafification
(Godement II.1.2; Hartshorne II.1.2). -/
instance sheafification_preservesFiniteColimits (X : TopCat.{u}) :
    PreservesFiniteColimits (sheafification X) :=
  inferInstanceAs (PreservesFiniteColimits
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- Sheafifying the underlying presheaf of a sheaf recovers the sheaf. -/
def sheafificationUnderlyingIso (X : TopCat.{u}) :
    TopCat.Sheaf.forget AddCommGrpCat X ⋙ sheafification X ≅ 𝟭 (AbelianSheaf X) :=
  (sheafificationNatIso (Opens.grothendieckTopology X) AddCommGrpCat).symm

/-- Sheafification recovers a complex of sheaves, including its differentials. -/
def sheafificationComplexIso (K : CochainComplex (AbelianSheaf X) ℕ) :
    ((sheafification X).mapHomologicalComplex _).obj (underlyingPresheafComplex K) ≅ K :=
  (Functor.mapHomologicalComplexCompIso (sheafificationUnderlyingIso X) _).app K ≪≫
    (Functor.mapHomologicalComplexIdIso (AbelianSheaf X) _).app K

/-- The homology sheaf of a complex is the sheafification of its homology presheaf. -/
def sheafHomologyIsoSheafification (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    K.homology n ≅ (sheafification X).obj (homologyPresheaf K n) :=
  HomologicalComplex.homologyMapIso (sheafificationComplexIso K).symm n ≪≫
    mapComplexHomologyIso (underlyingPresheafComplex K) (sheafification X) n

end Generic

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Hartshorne III.8.1: the genuine higher direct image `Rⁿf_*F` is the sheafification of the
homology presheaf `U ↦ Hⁿ(Γ(f⁻¹U, I))` of any pushed injective resolution `I` of `F`. -/
def higherDirectImageResolutionSheafificationIso (F : AbelianSheaf X)
    (I : InjectiveResolution F) (n : ℕ) :
    higherDirectImageSheaf f F n ≅
      (sheafification Y).obj (homologyPresheaf (pushedResolution f I) n) :=
  higherDirectImageResolutionIso f F I n ≪≫
    sheafHomologyIsoSheafification (pushedResolution f I) n

/-- The source injective resolution evaluated on the inverse image of an actual open subset. -/
abbrev inverseImageResolutionSections {F : AbelianSheaf X} (I : InjectiveResolution F)
    (U : Opens Y) : CochainComplex AddCommGrpCat ℕ := by
  let E : AbelianSheaf X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ((Opens.map f).obj U))
  let _ : E.Additive := ⟨by intros; rfl⟩
  exact (E.mapHomologicalComplex _).obj I.cocomplex

/-- On every open `U`, the presheaf in the sheafification theorem is the actual homology of
sections of the source resolution over `f⁻¹(U)`. -/
def higherDirectImageResolutionPresheafObjIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) (U : Opens Y) :
    (homologyPresheaf (pushedResolution f I) n).obj (op U) ≅
      (inverseImageResolutionSections f I U).homology n := by
  let E : TopCat.Presheaf AddCommGrpCat.{u} Y ⥤ AddCommGrpCat.{u} :=
    (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U)
  let _ : E.Additive := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)))
  let _ : PreservesFiniteColimits E := inferInstanceAs
    (PreservesFiniteColimits
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)))
  exact (mapComplexHomologyIso
    (underlyingPresheafComplex (pushedResolution f I)) E n).symm

/-- Stalk form of the same comparison.  This is a neighborhood colimit, with no base-change
claim to the cohomology of the point fibre. -/
def higherDirectImageResolutionStalkIso (F : AbelianSheaf X)
    (I : InjectiveResolution F) (n : ℕ) (y : Y) :
    TopCat.Presheaf.stalk (higherDirectImageSheaf f F n).obj y ≅
      TopCat.Presheaf.stalk (homologyPresheaf (pushedResolution f I) n) y :=
  (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      (higherDirectImageResolutionIso f F I n) ≪≫
    stalkHomologyPresheafIso y (pushedResolution f I) n

end CategoryTheory.Sheaf.Leray
