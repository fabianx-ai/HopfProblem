/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.SpectralObject.Postnikov
public import Lib.CategoryTheory.Sites.Leray.ResolutionTransgression
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Postnikov pages of a pushed sheaf resolution

For a continuous map `f : X ⟶ Y`, an abelian sheaf `F` on `X`, and an injective resolution
`I` of `F`, this file constructs a genuine first-quadrant spectral sequence from the Postnikov
tower of the derived object represented by the pushed complex `f_* I`.

Its initial page is exposed as the shifted representable group of each Postnikov slice, and the
cohomology objects of the total derived object are identified with the genuine higher direct
images `Rᵠf_*F`.

This is a page construction, not yet the complete Leray theorem.  In particular, this file does
not identify each Postnikov slice with the corresponding single higher-direct-image sheaf, shrink
the large representable groups to Mathlib's small `Ext` groups, identify `d₂` with the resolution
transgression, or supply an `E_∞` filtration and associated-graded abutment.  Mathlib's current
`SpectralSequence` structure contains pages and page-to-page homology isomorphisms but no such
convergence datum.
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

/-- The initial page is the shifted representable group of the corresponding Postnikov slice.
The further comparison of that slice with `Rᵠf_*F` is intentionally a separate theorem. -/
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

end CategoryTheory.Sheaf.Leray
