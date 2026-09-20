/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.SpectralObject.PostnikovD2
public import Lib.CategoryTheory.Sites.Leray.ResolutionPostnikov

/-!
# The page-two differential of the resolution Postnikov spectral sequence

This file specializes the generic Postnikov page-two differential formula to the derived object
represented by a pushed injective resolution.  The result names the literal differential of
`resolutionPostnikovSpectralSequence` as the connecting map of its adjacent two-slice triangle.

That the `d₂` of a spectral sequence obtained from a Postnikov (t-structure) tower is the
connecting morphism of the triangle joining two adjacent slices is the standard description of
the differentials of the spectral object of a filtered object (cf. Verdier, *Des catégories
dérivées des catégories abéliennes*, Ch. II; Kashiwara–Schapira, *Categories and Sheaves*,
Ch. 10 and Ch. 12).  For the
Leray spectral sequence this `d₂` is the transgression of Godement II.4.17.

No convergence and no support hypothesis is used.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace CategoryTheory.Sheaf.Leray

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The literal page-two differential of the pushed-resolution Postnikov spectral sequence is
the homological connecting map of the adjacent Postnikov two-slice triangle, under the canonical
page endpoint isomorphisms. -/
lemma resolutionPostnikovE₂_d₂_eq {F : AbelianSheaf X}
    (I : InjectiveResolution F) (p q : ℕ) :
    ((resolutionPostnikovSpectralSequence f I).page 2).d (p, q + 1) (p + 2, q) =
      (DerivedCategory.TStructure.t.coyonedaPostnikovD₂SourcePageIso
        (integralDerivedObject Y) (pushedResolutionDerivedObject f I) p q).hom ≫
        (preadditiveCoyoneda.obj (Opposite.op (integralDerivedObject Y))).homologySequenceδ
          ((DerivedCategory.TStructure.t.triangleω₁δ
            (q : ℤ) ((q : ℤ) + 1 : ℤ) ((q : ℤ) + 2 : ℤ)
            (by simp) (by simp)).obj (pushedResolutionDerivedObject f I))
          ((p : ℤ) + q + 1) ((p : ℤ) + q + 2) (by omega) ≫
        (DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          (integralDerivedObject Y) (pushedResolutionDerivedObject f I) p q).inv := by
  exact DerivedCategory.TStructure.t.coyonedaPostnikovE₂_d₂_eq
    (integralDerivedObject Y) (pushedResolutionDerivedObject f I) p q

end CategoryTheory.Sheaf.Leray
