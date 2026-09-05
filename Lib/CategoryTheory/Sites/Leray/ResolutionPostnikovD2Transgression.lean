/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.HomologyTwoStepResolutionExtend
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2Normalized
public import Lib.CategoryTheory.Sites.Leray.ResolutionPostnikovD2Coordinates

/-!
# Resolution Postnikov differential and two-step transgression

This file specializes the normalized generic Postnikov `d₂` calculation to a pushed injective
resolution.  The source and target page coordinates identify its literal page-two differential
with the positive two-step resolution transgression.  No convergence or support hypothesis is
used.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Abelian.ExtTransgression
open CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

namespace CategoryTheory.Sheaf.Leray

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical resolution page coordinates, the literal page-two Postnikov differential
from `(0,q+1)` to `(2,q)` is the positive two-step resolution transgression. -/
lemma resolutionPostnikovE₂_d₂_eq_transgression
    {F : AbelianSheaf X} (I : InjectiveResolution F) (q : ℕ)
    (x : ((resolutionPostnikovSpectralSequence f I).page 2).X (0, q + 1)) :
    resolutionPostnikovE₂AddEquiv f I 2 q
        ((((resolutionPostnikovSpectralSequence f I).page 2).d
          (0, q + 1) (2, q)).hom x) =
      resolutionTransgressionAddOfResolution f I q
        (resolutionPostnikovE₂AddEquiv f I 0 (q + 1) x) := by
  have hgeneric :
      coyonedaPostnikovD₂TargetExt
          ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
          (integralSheaf Y) q
          ((((resolutionPostnikovSpectralSequence f I).page 2).d
            (0, q + 1) (2, q)).hom x) =
        (homologyTwoStepResolutionInt
          ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
          (q : ℤ)).connectingTwo (integralSheaf Y)
            (Ext.mk₀ (coyonedaPostnikovD₂SourceHom
              ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
              (integralSheaf Y) q x)) := by
    exact coyonedaPostnikovD₂TargetExt_d₂ _ _ _ _
  apply (resolutionCohomologyIso f I q 2).addCommGroupIsoToAddEquiv.symm.injective
  rw [Iso.addCommGroupIsoToAddEquiv_symm_apply,
    Iso.addCommGroupIsoToAddEquiv_symm_apply]
  rw [resolutionPostnikovE₂AddEquiv_target_coordinate]
  rw [resolutionTransgressionAddOfResolution_apply_eq_connectingTwo]
  erw [Iso.hom_inv_id_apply]
  rw [hgeneric]
  rw [← homologyTwoStepResolutionExtendUpNat_connectingTwo
    (pushedResolution f I) q (integralSheaf Y)
      (Ext.mk₀ (coyonedaPostnikovD₂SourceHom
        ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
        (integralSheaf Y) q x))]
  rw [resolutionPostnikovE₂AddEquiv_source_coordinate]
  simp

end CategoryTheory.Sheaf.Leray
