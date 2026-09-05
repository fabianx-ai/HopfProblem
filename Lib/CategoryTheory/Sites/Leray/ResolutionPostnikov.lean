/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovSlice
public import Lib.Algebra.Homology.SpectralObject.Postnikov
public import Lib.CategoryTheory.Sites.Leray.ResolutionTransgression
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Postnikov pages of a pushed sheaf resolution

For a continuous map `f : X ⟶ Y`, an abelian sheaf `F` on `X`, and an injective resolution
`I` of `F`, this file constructs a genuine first-quadrant spectral sequence from the Postnikov
tower of the derived object represented by the pushed complex `f_* I`.

Its initial page is exposed as the shifted representable group of each Postnikov slice.  The
cohomology objects of the total derived object are identified with the genuine higher direct
images `Rᵠf_*F`, yielding an objectwise identification of the page with
`Hᵖ(Y, Rᵠf_*F)` (universe-lifted at the categorical level).

This is a page construction, not yet the complete Leray theorem.  The page adapter uses the
normalized slice-to-homology comparison whose naturality is proved in
`Lib.Algebra.Homology.DerivedCategory.PostnikovSliceNaturality`; this file still does not package
that naturality or identify `d₂` with the resolution transgression.  Nor does it supply an
`E_∞` filtration and associated-graded abutment: Mathlib's current `SpectralSequence` structure
contains pages and page-to-page homology isomorphisms but no such convergence datum.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The derived object on `Y` represented by the pushed injective resolution `f_* I`, after
extending its natural-number grading by zero to an integer grading. -/
def pushedResolutionDerivedObject {F : AbelianSheaf X} (I : InjectiveResolution F) :
    DerivedCategory (AbelianSheaf Y) :=
  DerivedCategory.Q.obj ((pushedResolution f I).extend ComplexShape.embeddingUpNat)

/-- The integral sheaf in degree zero, as an object of the derived category. -/
abbrev integralDerivedObject (Y : TopCat.{0}) : DerivedCategory (AbelianSheaf Y) :=
  (DerivedCategory.singleFunctor (AbelianSheaf Y) 0).obj (integralSheaf Y)

/-- A pushed natural-number-graded resolution represents a nonnegative derived object. -/
instance pushedResolutionDerivedObject_isGE {F : AbelianSheaf X}
    (I : InjectiveResolution F) :
    DerivedCategory.TStructure.t.IsGE (pushedResolutionDerivedObject f I) 0 := by
  dsimp [pushedResolutionDerivedObject]
  infer_instance

/-- The integral sheaf in degree zero is a nonpositive derived object. -/
instance integralDerivedObject_isLE :
    DerivedCategory.TStructure.t.IsLE (integralDerivedObject Y) 0 := by
  dsimp [integralDerivedObject]
  infer_instance

/-- Integer-graded derived homology of the extended pushed resolution agrees with the original
natural-number-graded homology. -/
def pushedResolutionDerivedObjectHomologyIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.homologyFunctor (AbelianSheaf Y) (q : ℤ)).obj
      (pushedResolutionDerivedObject f I) ≅ (pushedResolution f I).homology q :=
  (DerivedCategory.homologyFunctorFactors (AbelianSheaf Y) (q : ℤ)).app
      ((pushedResolution f I).extend ComplexShape.embeddingUpNat) ≪≫
    (pushedResolution f I).extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl

/-- The cohomology objects of the pushed-resolution derived object are the genuine higher direct
images. -/
def pushedResolutionDerivedObjectHomologyHigherDirectImageIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.homologyFunctor (AbelianSheaf Y) (q : ℤ)).obj
      (pushedResolutionDerivedObject f I) ≅ higherDirectImageSheaf f F q :=
  pushedResolutionDerivedObjectHomologyIso f I q ≪≫
    (higherDirectImageResolutionIso f F I q).symm

/-- The Postnikov spectral object of the pushed resolution, tested against the integral sheaf. -/
def resolutionPostnikovSpectralObject {F : AbelianSheaf X} (I : InjectiveResolution F) :
    SpectralObject AddCommGrpCat EInt :=
  DerivedCategory.TStructure.t.coyonedaPostnikovSpectralObject
    (integralDerivedObject Y) (pushedResolutionDerivedObject f I)

/-- The genuine natural-indexed first-quadrant page sequence obtained from the pushed resolution's
Postnikov tower. -/
def resolutionPostnikovSpectralSequence {F : AbelianSheaf X} (I : InjectiveResolution F) :
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat :=
  DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
    (integralDerivedObject Y) (pushedResolutionDerivedObject f I)

/-- The total interval of the resolution Postnikov spectral object is represented by morphisms
from the integral sheaf into the shifted pushed-resolution derived object. -/
def resolutionPostnikovTotalIso {F : AbelianSheaf X} (I : InjectiveResolution F) (n : ℤ) :
    (((resolutionPostnikovSpectralObject f I).H n).obj
      (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) ≅
      AddCommGrpCat.of
        (integralDerivedObject Y ⟶ (pushedResolutionDerivedObject f I)⟦n⟧) :=
  DerivedCategory.TStructure.t.postnikovTotalIso
    (pushedResolutionDerivedObject f I)
    (preadditiveCoyoneda.obj (Opposite.op (integralDerivedObject Y))) n

/-- The initial page is the shifted representable group of the corresponding Postnikov slice. -/
def resolutionPostnikovE₂PageIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (p q : ℕ) :
    ((resolutionPostnikovSpectralSequence f I).page 2).X (p, q) ≅
      AddCommGrpCat.of
        (integralDerivedObject Y ⟶
          ((DerivedCategory.TStructure.t.eTruncGE.obj (q : ℤ)).obj
            ((DerivedCategory.TStructure.t.eTruncLT.obj (q + 1 : ℤ)).obj
              (pushedResolutionDerivedObject f I)))⟦(p + q : ℤ)⟧) :=
  DerivedCategory.TStructure.t.coyonedaPostnikovE₂PageIso
    (integralDerivedObject Y) (pushedResolutionDerivedObject f I) p q

/-- The degree-`q` Postnikov slice of the pushed resolution is isomorphic to the degree-`q`
single object on the genuine higher direct image.  The underlying normalized
`DerivedCategory.postnikovSliceIso` is natural; this definition records its objectwise sheaf
specialization. -/
def resolutionPostnikovSliceHigherDirectImageIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.TStructure.t.truncGE (q : ℤ)).obj
        ((DerivedCategory.TStructure.t.truncLT (q + 1 : ℤ)).obj
          (pushedResolutionDerivedObject f I)) ≅
      (DerivedCategory.singleFunctor (AbelianSheaf Y) (q : ℤ)).obj
        (higherDirectImageSheaf f F q) :=
  DerivedCategory.postnikovSliceIso (pushedResolutionDerivedObject f I) q ≪≫
    (DerivedCategory.singleFunctor (AbelianSheaf Y) (q : ℤ)).mapIso
      (pushedResolutionDerivedObjectHomologyHigherDirectImageIso f I q)

/-- After the page shift, the degree-`q` slice represents degree-`p` Ext from the integral sheaf
to the genuine higher direct image. -/
def resolutionPostnikovShiftedSliceHigherDirectImageIso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (p q : ℕ) :
    ((DerivedCategory.TStructure.t.truncGE (q : ℤ)).obj
        ((DerivedCategory.TStructure.t.truncLT (q + 1 : ℤ)).obj
          (pushedResolutionDerivedObject f I)))⟦(p + q : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor (AbelianSheaf Y) 0).obj
        (higherDirectImageSheaf f F q))⟦(p : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory (AbelianSheaf Y)) (p + q : ℤ)).mapIso
      (resolutionPostnikovSliceHigherDirectImageIso f I q) ≪≫
    ((DerivedCategory.singleFunctors (AbelianSheaf Y)).shiftIso
      (p + q : ℤ) (-p : ℤ) q (by omega)).app (higherDirectImageSheaf f F q) ≪≫
    (((DerivedCategory.singleFunctors (AbelianSheaf Y)).shiftIso
      (p : ℤ) (-p : ℤ) 0 (by omega)).app (higherDirectImageSheaf f F q)).symm

/-- The initial Postnikov page is objectwise the universe lift of the actual small Leray term
`Hᵖ(Y, Rᵠf_*F)`.  The lift is necessary because the standard derived category of small sheaves
has large morphism types. -/
def resolutionPostnikovE₂Iso {F : AbelianSheaf X}
    (I : InjectiveResolution F) (p q : ℕ) :
    ((resolutionPostnikovSpectralSequence f I).page 2).X (p, q) ≅
      AddCommGrpCat.of (ULift.{1} (E₂ f F p q)) :=
  resolutionPostnikovE₂PageIso f I p q ≪≫
    (preadditiveCoyoneda.obj (Opposite.op (integralDerivedObject Y))).mapIso
      (resolutionPostnikovShiftedSliceHigherDirectImageIso f I p q) ≪≫
    ((Ext.homAddEquiv (X := integralSheaf Y)
      (Y := higherDirectImageSheaf f F q) (n := p)).symm.trans
        AddEquiv.ulift.symm).toAddCommGrpIso

/-- The same initial-page identification as an additive equivalence with the unlifted small
Leray term. -/
def resolutionPostnikovE₂AddEquiv {F : AbelianSheaf X}
    (I : InjectiveResolution F) (p q : ℕ) :
    ((resolutionPostnikovSpectralSequence f I).page 2).X (p, q) ≃+
      E₂ f F p q :=
  (resolutionPostnikovE₂Iso f I p q).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift

end CategoryTheory.Sheaf.Leray
