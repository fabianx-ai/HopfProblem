/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module


public import Lib.Algebra.Homology.DerivedCategory.Ext.DegreeZero
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2PageCoordinates
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2SourceCoordinates
public import Lib.CategoryTheory.Sites.Leray.ResolutionPostnikov

/-!
# Resolution coordinates for the Postnikov page-two differential

This file compares the actual Leray-page coordinates at bidegrees `(0,q+1)` and `(2,q)` with
the generic Postnikov source morphism and target `Ext²` coordinate.  The comparisons keep the
non-definitional total-degree transports visible, move all homology comparison maps through the
single-object shift adapters, and introduce no scalar or sign.

There is no textbook counterpart: these are the coordinate changes identifying two constructions
of the same groups `H⁰(Y, Rᑫ⁺¹f_*F)` and `H²(Y, Rᑫf_*F)`, the resolution-cohomology one of
`ResolutionTransgression` and the Postnikov-page one of `ResolutionPostnikov`.  They are what the
computation of the Leray `d₂` as a transgression (Godement II.4.17) needs in order to be stated
on the `E₂` page.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

namespace CategoryTheory.Sheaf.Leray

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
/-- In resolution cohomology coordinates, an element of the Postnikov page at `(0,q+1)` is its
generic normalized source morphism transported from the homology of the extended pushed
resolution.  This comparison is sign-free. -/
lemma resolutionPostnikovE₂AddEquiv_source_coordinate
    {F : AbelianSheaf X} (I : InjectiveResolution F) (q : ℕ)
    (x : ((resolutionPostnikovSpectralSequence f I).page 2).X (0, q + 1)) :
    (resolutionExtZeroIso f I (q + 1)).hom.hom
        (resolutionPostnikovE₂AddEquiv f I 0 (q + 1) x) =
      coyonedaPostnikovD₂SourceHom
          ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
          (integralSheaf Y) q x ≫
        ((pushedResolution f I).extendHomologyIso ComplexShape.embeddingUpNat
          (j := q + 1) (by simp)).hom := by
  let g : integralDerivedObject Y ⟶
      ((DerivedCategory.singleFunctor (AbelianSheaf Y) 0).obj
        (higherDirectImageSheaf f F (q + 1)))⟦(0 : ℤ)⟧ :=
    (resolutionPostnikovE₂PageIso f I 0 (q + 1)).hom.hom x ≫
      (resolutionPostnikovShiftedSliceHigherDirectImageIso f I 0 (q + 1)).hom
  have hleft :
      (resolutionExtZeroIso f I (q + 1)).hom.hom
          (resolutionPostnikovE₂AddEquiv f I 0 (q + 1) x) =
        Ext.addEquiv₀ ((Ext.homAddEquiv
          (X := integralSheaf Y)
          (Y := higherDirectImageSheaf f F (q + 1))
          (n := 0)).symm g) ≫
          (higherDirectImageResolutionIso f F I (q + 1)).hom := by
    rfl
  rw [hleft]
  apply (DerivedCategory.singleFunctor (AbelianSheaf Y) 0).map_injective
  rw [Functor.map_comp,
    Ext.singleFunctor_map_addEquiv₀_homAddEquiv_symm]
  simp [coyonedaPostnikovD₂SourceHom,
    resolutionPostnikovShiftedSliceHigherDirectImageIso,
    resolutionPostnikovSliceHigherDirectImageIso,
    pushedResolutionDerivedObjectHomologyHigherDirectImageIso,
    pushedResolutionDerivedObjectHomologyIso, g]
  erw [((DerivedCategory.singleFunctors (AbelianSheaf Y)).shiftIso
      (0 + ((q : ℤ) + 1)) 0 ((q : ℤ) + 1) (by omega)).hom.naturality_assoc
        (higherDirectImageResolutionIso f F I (q + 1)).inv
        ((DerivedCategory.singleFunctor (AbelianSheaf Y) 0).map
          (higherDirectImageResolutionIso f F I (q + 1)).hom)]
  simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]
  erw [((DerivedCategory.singleFunctors (AbelianSheaf Y)).shiftIso
      (0 + ((q : ℤ) + 1)) 0 ((q : ℤ) + 1) (by omega)).hom.naturality
        ((pushedResolution f I).extendHomologyIso ComplexShape.embeddingUpNat
          (j := q + 1) (by simp)).hom]
  erw [((DerivedCategory.singleFunctors (AbelianSheaf Y)).shiftIso
      (0 + ((q : ℤ) + 1)) 0 ((q : ℤ) + 1) (by omega)).hom.naturality_assoc
        ((DerivedCategory.homologyFunctorFactors (AbelianSheaf Y)
          ((q : ℤ) + 1)).hom.app
            ((pushedResolution f I).extend ComplexShape.embeddingUpNat))]
  simp only [Functor.map_comp]
  erw [reassoc_of%
    DerivedCategory.postnikovSourceShiftedSliceIso_hom_eq_of_shift
      ((pushedResolution f I).extend ComplexShape.embeddingUpNat) (q : ℤ)
      (0 + ((q : ℤ) + 1)) (by omega)]
  erw [reassoc_of%
    DerivedCategory.coyonedaPostnikovE₂PageIso_zero_to_d₂SourceEndpoint
      ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
      (integralSheaf Y) q x]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- In resolution cohomology coordinates, an element of the Postnikov page at `(2,q)` is its
generic normalized target `Ext²` class transported from derived homology to the homology of the
extended pushed resolution.  All shift comparisons in this formula are sign-free. -/
lemma resolutionPostnikovE₂AddEquiv_target_coordinate {F : AbelianSheaf X}
    (I : InjectiveResolution F) (q : ℕ)
    (y : ((resolutionPostnikovSpectralSequence f I).page 2).X (2, q)) :
    (resolutionCohomologyIso f I q 2).inv.hom
        (resolutionPostnikovE₂AddEquiv f I 2 q y) =
      (coyonedaPostnikovD₂TargetExt
          ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
          (integralSheaf Y) q y).comp
        (Ext.mk₀ ((pushedResolution f I).extendHomologyIso
          ComplexShape.embeddingUpNat (j := q) rfl).hom) (add_zero 2) := by
  let g : integralDerivedObject Y ⟶
      ((DerivedCategory.singleFunctor (AbelianSheaf Y) 0).obj
        (higherDirectImageSheaf f F q))⟦(2 : ℤ)⟧ :=
    (resolutionPostnikovE₂PageIso f I 2 q).hom.hom y ≫
      (resolutionPostnikovShiftedSliceHigherDirectImageIso f I 2 q).hom
  have hy : resolutionPostnikovE₂AddEquiv f I 2 q y =
      (Ext.homAddEquiv (X := integralSheaf Y)
        (Y := higherDirectImageSheaf f F q) (n := 2)).symm g := by
    rfl
  rw [hy, resolutionCohomologyIso_inv_apply]
  apply Ext.homEquiv.injective
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  have hg : (Ext.homAddEquiv.symm g).hom = g := by
    simpa only [Ext.homAddEquiv_apply] using
      (Ext.homAddEquiv (X := integralSheaf Y)
        (Y := higherDirectImageSheaf f F q) (n := 2)).apply_symm_apply g
  erw [hg]
  let h :=
    (DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
        (integralDerivedObject Y) (pushedResolutionDerivedObject f I) 0 q).hom.hom y ≫
      eqToHom (by simp [pushedResolutionDerivedObject]) ≫
      (postnikovTargetExtIso
        ((pushedResolution f I).extend ComplexShape.embeddingUpNat) (q : ℤ)).hom ≫
      ((DerivedCategory.singleFunctor (AbelianSheaf Y) 0).map
        ((DerivedCategory.homologyFunctorFactors (AbelianSheaf Y) (q : ℤ)).hom.app
          ((pushedResolution f I).extend ComplexShape.embeddingUpNat)))⟦(2 : ℤ)⟧'
  have hh : (coyonedaPostnikovD₂TargetExt
      ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
      (integralSheaf Y) q y).hom = h := by
    dsimp [coyonedaPostnikovD₂TargetExt, h, integralDerivedObject,
      pushedResolutionDerivedObject]
    exact Equiv.apply_symm_apply _ _
  erw [hh]
  simp [resolutionPostnikovShiftedSliceHigherDirectImageIso,
    resolutionPostnikovSliceHigherDirectImageIso,
    pushedResolutionDerivedObjectHomologyHigherDirectImageIso,
    pushedResolutionDerivedObjectHomologyIso,
    g, h]
  erw [postnikovTargetSingleShiftIso_hom_inv_of_shift
    (C := AbelianSheaf Y) (q : ℤ) ((2 : ℤ) + q) (by omega)
      (higherDirectImageResolutionIso f F I q).symm]
  erw [postnikovTargetSingleShiftIso_naturality_of_shift
    (C := AbelianSheaf Y) (q : ℤ) ((2 : ℤ) + q) (by omega)
      ((pushedResolution f I).extendHomologyIso ComplexShape.embeddingUpNat
        (j := q) rfl).hom]
  erw [postnikovTargetSingleShiftIso_naturality_of_shift_assoc
    (C := AbelianSheaf Y) (q : ℤ) ((2 : ℤ) + q) (by omega)
      ((DerivedCategory.homologyFunctorFactors (AbelianSheaf Y) (q : ℤ)).hom.app
        ((pushedResolution f I).extend ComplexShape.embeddingUpNat))]
  erw [reassoc_of% postnikovTargetExtIso_hom_eq_of_shift
    ((pushedResolution f I).extend ComplexShape.embeddingUpNat)
      (q : ℤ) ((2 : ℤ) + q) (by omega)]
  erw [reassoc_of%
    DerivedCategory.TStructure.t.coyonedaPostnikovE₂PageIso_two_eq_d₂Target_apply
      (integralDerivedObject Y) (pushedResolutionDerivedObject f I) q y]
  set_option backward.isDefEq.respectTransparency true in
    rfl

end CategoryTheory.Sheaf.Leray
