/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.InjectiveResolutionCoyoneda
public import Lib.Algebra.Homology.DerivedCategory.KInjectiveCohomology
public import Lib.Algebra.Homology.HomologicalComplex.MapExtend
public import Lib.CategoryTheory.Sites.Leray.ResolutionPostnikov
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The total object of the resolution Postnikov spectral object

For a continuous map `f : X ⟶ Y`, an abelian sheaf `F` on `X`, and an injective resolution
`I` of `F`, this file identifies the total interval of the pushed-resolution Postnikov spectral
object with the actual cohomology `Hⁿ(X,F)`.

The proof first regards the pushed resolution as an integer-graded complex.  Pushforward preserves
injective sheaves because it is right adjoint to the finite-limit-preserving sheaf pullback, so
this bounded-below complex is K-injective.  Derived Hom out of the integral sheaf is therefore
computed by its explicit representable Hom complex.  The integral-sheaf pushforward equivalence
identifies that complex with `Hom(ℤ_X,I•)`, whose homology is `Extⁿ(ℤ_X,F) = Hⁿ(X,F)`.

This is the abutment identification of the Leray spectral sequence
`E₂^{p,q} = Hᵖ(Y, Rᑫf_*F) ⇒ Hᵖ⁺ᑫ(X, F)` (Godement, *Topologie algébrique et théorie des
faisceaux*, II.4.17; Weibel, *An Introduction to Homological Algebra*, 5.8.6, the Grothendieck
spectral sequence of the composite `Γ(Y, −) ∘ f_*`).  That `f_*` preserves injectives, because it
is right adjoint to the exact inverse image `f⁻¹`, is Weibel 2.3.10 (Hartshorne III.8.1's
standing remark).

It is the abutment-object comparison, not by itself a convergence theorem.  In particular, it
does not construct an `E_∞` page, a finite filtration on `Hⁿ(X,F)`, or identify associated
graded pieces.  Those data are not fields of Mathlib's current `SpectralSequence` structure.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The integer-graded complex obtained by applying sheaf pushforward degreewise to an injective
resolution. -/
def mappedExtendedResolution {F : AbelianSheaf X} (I : InjectiveResolution F) :
    CochainComplex (AbelianSheaf Y) ℤ :=
  ((pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

/-- Mapping the integer extension of a resolution agrees with extending its mapped
natural-number-graded complex. -/
def mappedExtendedResolutionIso {F : AbelianSheaf X} (I : InjectiveResolution F) :
    mappedExtendedResolution f I ≅
      (pushedResolution f I).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.mapExtendIso (F := pushforward f) I.cocomplex
    ComplexShape.embeddingUpNat

/-- Direct image of abelian sheaves preserves injective objects, being right adjoint to the
exact inverse image `f⁻¹` (Weibel 2.3.10). -/
theorem pushforwardPreservesInjectiveObjects :
    (pushforward f).PreservesInjectiveObjects := by
  let _ : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
    change PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{0}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat.{0}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let _ := preservesMonomorphisms_of_preservesLimitsOfShape
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)

/-- The degreewise pushforward of an injective resolution, extended to integer degrees, is
K-injective. -/
instance mappedExtendedResolution_isKInjective {F : AbelianSheaf X}
    (I : InjectiveResolution F) :
    (mappedExtendedResolution f I).IsKInjective := by
  let _ : (pushforward f).PreservesInjectiveObjects := pushforwardPreservesInjectiveObjects f
  let _ : (mappedExtendedResolution f I).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    change IsZero ((pushforward f).obj (I.cochainComplex.X i))
    exact (pushforward f).map_isZero
      (I.cochainComplex.isZero_of_isStrictlyGE 0 i hi)
  let _ : ∀ n, Injective ((mappedExtendedResolution f I).X n) := fun n => by
    change Injective ((pushforward f).obj (I.cochainComplex.X n))
    infer_instance
  exact CochainComplex.isKInjective_of_injective _ 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Degreewise integral-sheaf pushforward equivalences assemble into an isomorphism between the
two representable cochain complexes. -/
def integralCoyonedaPushforwardIso (K : CochainComplex (AbelianSheaf X) ℤ) :
    CochainComplex.HomComplex.coyonedaComplex (TopCat.ConstantSheaf.integralSheaf Y)
        (((pushforward f).mapHomologicalComplex (.up ℤ)).obj K) ≅
      CochainComplex.HomComplex.coyonedaComplex (TopCat.ConstantSheaf.integralSheaf X) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => by
      change AddCommGrpCat.of
          (TopCat.ConstantSheaf.integralSheaf Y ⟶ (pushforward f).obj (K.X n)) ≅
        AddCommGrpCat.of (TopCat.ConstantSheaf.integralSheaf X ⟶ K.X n)
      exact (TopCat.ConstantSheaf.integralHomPushforwardEquiv f (K.X n)).symm.toAddCommGrpIso)
    (fun i j hij => by
      apply AddCommGrpCat.ext
      intro h
      simp only [ConcreteCategory.comp_apply]
      dsimp [CochainComplex.HomComplex.coyonedaComplex]
      change (TopCat.ConstantSheaf.integralHomPushforwardEquiv f (K.X i)).symm h ≫ K.d i j =
        (TopCat.ConstantSheaf.integralHomPushforwardEquiv f (K.X j)).symm
          (h ≫ (pushforward f).map (K.d i j))
      apply (TopCat.ConstantSheaf.integralHomPushforwardEquiv f (K.X j)).injective
      rw [TopCat.ConstantSheaf.integralHomPushforwardEquiv_naturality]
      simp)

/-- The integral-sheaf pushforward isomorphism induces an isomorphism on cohomology. -/
def integralCoyonedaPushforwardHomologyIso
    (K : CochainComplex (AbelianSheaf X) ℤ) (n : ℤ) :
    (CochainComplex.HomComplex.coyonedaComplex (TopCat.ConstantSheaf.integralSheaf Y)
      (((pushforward f).mapHomologicalComplex (.up ℤ)).obj K)).homology n ≅
        (CochainComplex.HomComplex.coyonedaComplex (TopCat.ConstantSheaf.integralSheaf X) K).homology n :=
  HomologicalComplex.homologyMapIso (integralCoyonedaPushforwardIso f K) n

/-- Derived Hom into the pushed-resolution object computes the source sheaf cohomology. -/
def resolutionDerivedHomCohomologyEquiv {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) :
    (integralDerivedObject Y ⟶ (pushedResolutionDerivedObject f I)⟦(n : ℤ)⟧) ≃
      CategoryTheory.Sheaf.H.{0} F n := by
  let K := mappedExtendedResolution f I
  let eK : K ≅ (pushedResolution f I).extend ComplexShape.embeddingUpNat :=
    mappedExtendedResolutionIso f I
  let e₁ :
      (integralDerivedObject Y ⟶ (pushedResolutionDerivedObject f I)⟦(n : ℤ)⟧) ≃
        (integralDerivedObject Y ⟶ (DerivedCategory.Q.obj K)⟦(n : ℤ)⟧) :=
    ((shiftFunctor (DerivedCategory (AbelianSheaf Y)) (n : ℤ)).mapIso
      (DerivedCategory.Q.mapIso eK)).homToEquiv.symm
  letI : CategoryTheory.Localization.HasSmallLocalizedShiftedHom.{1}
      (HomologicalComplex.quasiIso (AbelianSheaf Y) (.up ℤ)) ℤ
      ((CochainComplex.singleFunctor (AbelianSheaf Y) 0).obj (TopCat.ConstantSheaf.integralSheaf Y)) K :=
    fun _ _ => CategoryTheory.Localization.hasSmallLocalizedHom_of_isLocalization
      (HomologicalComplex.quasiIso (AbelianSheaf Y) (.up ℤ)) DerivedCategory.Q
  let e₂ := DerivedCategory.homEquivCoyonedaHomologyOfIsKInjective.{1}
    (TopCat.ConstantSheaf.integralSheaf Y) K (n : ℤ)
  let e₃ := (integralCoyonedaPushforwardHomologyIso f I.cochainComplex (n : ℤ))
    |>.addCommGroupIsoToAddEquiv.toEquiv
  let e₄ := (I.coyonedaHomologyExtAddEquiv (TopCat.ConstantSheaf.integralSheaf X) n).toEquiv
  exact e₁.trans (e₂.trans (e₃.trans e₄))

/-- The total interval of the pushed-resolution Postnikov spectral object is the degree-`n`
cohomology `Hⁿ(X, F)` of the source sheaf.  This is the abutment of the Leray spectral sequence
(Godement II.4.17, Weibel 5.8.6). -/
def resolutionPostnikovTotalCohomologyEquiv {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) :
    (((resolutionPostnikovSpectralObject f I).H (n : ℤ)).obj
      (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) ≃
      CategoryTheory.Sheaf.H.{0} F n :=
  (resolutionPostnikovTotalIso f I (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv.trans
    (resolutionDerivedHomCohomologyEquiv f I n)

end CategoryTheory.Sheaf.Leray
