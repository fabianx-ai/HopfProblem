/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2PageSplice
public import Lib.Algebra.Homology.DerivedCategory.PostnikovTwoSliceEndpoints

/-!
# Ext coordinates on the target of the page-two Postnikov differential

This file identifies the lower Postnikov slice, shifted to the target degree of `d₂`, with the
degree-two shift of its homology object.  It also packages the resulting target-page element as
an `Ext²` class.  The comparison with the lower endpoint of the shifted adjacent Postnikov
triangle keeps both shift associators visible and introduces no sign.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

/-- The lower Postnikov slice, shifted to the target degree of `d₂`, is the degree-two shift
of its homology object placed in degree zero. -/
def postnikovTargetExtIso (K : CochainComplex C ℤ) (q : ℤ) :
    ((DerivedCategory.TStructure.t.truncGE q).obj
      ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj
        (DerivedCategory.Q.obj K)))⟦q + 2⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj
        ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K)))⟦(2 : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory C) (q + 2)).mapIso
      (DerivedCategory.postnikovSliceIso (DerivedCategory.Q.obj K) q) ≪≫
    ((DerivedCategory.singleFunctors C).shiftIso (q + 2) (-2) q (by omega)).app
      ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K)) ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (2 : ℤ) (-2) 0 (by omega)).app
      ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pair of single-object shift adapters used by `postnikovTargetExtIso` is natural even
when the source shift is written by an expression propositionally equal to `q + 2`. -/
@[reassoc]
lemma postnikovTargetSingleShiftIso_naturality_of_shift
    (q n : ℤ) (hn : n = q + 2) {A B : C} (u : A ⟶ B) :
    (shiftFunctor (DerivedCategory C) n).map
          ((DerivedCategory.singleFunctor C q).map u) ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          n (-2) q (by omega)).hom.app B ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app B =
      ((DerivedCategory.singleFunctors C).shiftIso
          n (-2) q (by omega)).hom.app A ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app A ≫
        (shiftFunctor (DerivedCategory C) 2).map
          ((DerivedCategory.singleFunctor C 0).map u) := by
  change
    ((DerivedCategory.singleFunctors C).functor q ⋙
        shiftFunctor (DerivedCategory C) n).map u ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          n (-2) q (by omega)).hom.app B ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app B =
      ((DerivedCategory.singleFunctors C).shiftIso
          n (-2) q (by omega)).hom.app A ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app A ≫
        ((DerivedCategory.singleFunctors C).functor 0 ⋙
          shiftFunctor (DerivedCategory C) 2).map u
  rw [((DerivedCategory.singleFunctors C).shiftIso
    n (-2) q (by omega)).hom.naturality_assoc u]
  rw [((DerivedCategory.singleFunctors C).shiftIso
    2 (-2) 0 (by omega)).inv.naturality u]

set_option backward.isDefEq.respectTransparency false in
/-- Transporting an isomorphism through the two target shift adapters and then transporting back
in degree two cancels exactly, for any source-shift expression equal to `q + 2`. -/
@[reassoc]
lemma postnikovTargetSingleShiftIso_hom_inv_of_shift
    (q n : ℤ) (hn : n = q + 2) {A B : C} (e : A ≅ B) :
    (shiftFunctor (DerivedCategory C) n).map
          ((DerivedCategory.singleFunctor C q).map e.hom) ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          n (-2) q (by omega)).hom.app B ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app B ≫
        (shiftFunctor (DerivedCategory C) 2).map
          ((DerivedCategory.singleFunctor C 0).map e.inv) =
      ((DerivedCategory.singleFunctors C).shiftIso
          n (-2) q (by omega)).hom.app A ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app A := by
  rw [postnikovTargetSingleShiftIso_naturality_of_shift_assoc q n hn e.hom]
  simp only [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The pair of single-object shift adapters used by `postnikovTargetExtIso` is natural in
the homology object. -/
@[reassoc]
lemma postnikovTargetSingleShiftIso_naturality
    (q : ℤ) {A B : C} (u : A ⟶ B) :
    (shiftFunctor (DerivedCategory C) (q + 2)).map
          ((DerivedCategory.singleFunctor C q).map u) ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          (q + 2) (-2) q (by omega)).hom.app B ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app B =
      ((DerivedCategory.singleFunctors C).shiftIso
          (q + 2) (-2) q (by omega)).hom.app A ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app A ≫
        (shiftFunctor (DerivedCategory C) 2).map
          ((DerivedCategory.singleFunctor C 0).map u) := by
  change
    ((DerivedCategory.singleFunctors C).functor q ⋙
        shiftFunctor (DerivedCategory C) (q + 2)).map u ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          (q + 2) (-2) q (by omega)).hom.app B ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app B =
      ((DerivedCategory.singleFunctors C).shiftIso
          (q + 2) (-2) q (by omega)).hom.app A ≫
        ((DerivedCategory.singleFunctors C).shiftIso
          2 (-2) 0 (by omega)).inv.app A ≫
        ((DerivedCategory.singleFunctors C).functor 0 ⋙
          shiftFunctor (DerivedCategory C) 2).map u
  rw [((DerivedCategory.singleFunctors C).shiftIso
    (q + 2) (-2) q (by omega)).hom.naturality_assoc u]
  rw [((DerivedCategory.singleFunctors C).shiftIso
    2 (-2) 0 (by omega)).inv.naturality u]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized target isomorphism can be entered from any propositionally equal expression
for the shift `q + 2`; the only extra map is the explicit equality transport. -/
lemma postnikovTargetExtIso_hom_eq_of_shift
    (K : CochainComplex C ℤ) (q n : ℤ) (hn : n = q + 2) :
    (shiftFunctor (DerivedCategory C) n).map
          (DerivedCategory.postnikovSliceIso (DerivedCategory.Q.obj K) q).hom ≫
        ((DerivedCategory.singleFunctors C).shiftIso n (-2) q (by omega)).hom.app
          ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K)) ≫
        ((DerivedCategory.singleFunctors C).shiftIso 2 (-2) 0 (by omega)).inv.app
          ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K)) =
      eqToHom (by subst n; rfl) ≫ (postnikovTargetExtIso K q).hom := by
  subst n
  simp only [postnikovTargetExtIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The target Ext coordinate factors through the normalized lower endpoint of the shifted
adjacent Postnikov triangle.  The remaining maps merely reassociate its shift by one with the
second shift used by `Ext²`; in particular, this comparison contributes no scalar. -/
lemma postnikovTargetExtIso_hom_eq_shiftedLowerEndpoint
    (K : CochainComplex C ℤ) (q : ℤ) :
    (postnikovTargetExtIso K q).hom =
      (shiftFunctorAdd' (DerivedCategory C) (q + 1) 1 (q + 2) (by omega)).hom.app
          ((DerivedCategory.TStructure.t.truncGE q).obj
            ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj
              (DerivedCategory.Q.obj K))) ≫
        ((DerivedCategory.shiftedPostnikovLowerEndpointIso K q).hom)⟦(1 : ℤ)⟧' ≫
        (((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0
          (by omega)).inv.app
            ((DerivedCategory.homologyFunctor C q).obj
              (DerivedCategory.Q.obj K)))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj
            ((DerivedCategory.homologyFunctor C q).obj
              (DerivedCategory.Q.obj K))) := by
  let A := (DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K)
  have hsingle :
      ((DerivedCategory.singleFunctors C).shiftIso
            (q + 2) (-2) q (by omega)).hom.app A ≫
          ((DerivedCategory.singleFunctors C).shiftIso
            2 (-2) 0 (by omega)).inv.app A =
        (shiftFunctorAdd' (DerivedCategory C)
            (q + 1) 1 (q + 2) (by omega)).hom.app
              ((DerivedCategory.singleFunctor C q).obj A) ≫
          (((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) (-1) q (by omega)).hom.app A)⟦(1 : ℤ)⟧' ≫
          (((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).inv.app A)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C)
            (1 : ℤ) 1 2 rfl).inv.app
              ((DerivedCategory.singleFunctor C 0).obj A) := by
    rw [SingleFunctors.shiftIso_add'_hom_app
      (DerivedCategory.singleFunctors C) (1 : ℤ) (q + 1) (q + 2) (by omega)
      (-2) (-1) q (by omega) (by omega) A]
    rw [SingleFunctors.shiftIso_add'_inv_app
      (DerivedCategory.singleFunctors C) (1 : ℤ) 1 2 rfl
      (-2) (-1) 0 (by omega) (by omega) A]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hexpanded :
      (postnikovTargetExtIso K q).hom =
        (shiftFunctorAdd' (DerivedCategory C)
            (q + 1) 1 (q + 2) (by omega)).hom.app
              ((DerivedCategory.TStructure.t.truncGE q).obj
                ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj
                  (DerivedCategory.Q.obj K))) ≫
          ((shiftFunctor (DerivedCategory C) (q + 1)).map
            (DerivedCategory.postnikovSliceIso
              (DerivedCategory.Q.obj K) q).hom)⟦(1 : ℤ)⟧' ≫
          (((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) (-1) q (by omega)).hom.app A)⟦(1 : ℤ)⟧' ≫
          (((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).inv.app A)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C)
            (1 : ℤ) 1 2 rfl).inv.app
              ((DerivedCategory.singleFunctor C 0).obj A) := by
    dsimp only [postnikovTargetExtIso]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
    rw [hsingle]
    simp only [Functor.mapIso_hom]
    rw [reassoc_of% (shiftFunctorAdd' (DerivedCategory C)
      (q + 1) 1 (q + 2) (by omega)).hom.naturality
        (DerivedCategory.postnikovSliceIso (DerivedCategory.Q.obj K) q).hom]
  have hlower :
      (DerivedCategory.shiftedPostnikovLowerEndpointIso K q).hom =
        (shiftFunctor (DerivedCategory C) (q + 1)).map
            (DerivedCategory.postnikovSliceIso
              (DerivedCategory.Q.obj K) q).hom ≫
          ((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) (-1) q (by omega)).hom.app A := by
    rfl
  rw [hlower]
  simpa only [Functor.map_comp, Category.assoc] using hexpanded

/-- An element at bidegree `(2,q)` on page two, expressed as the corresponding normalized
`Ext²` class of the degree-`q` homology object. -/
def coyonedaPostnikovD₂TargetExt
    [HasExt.{w} C] (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (y : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (2, q)) :
    Ext.{w} P
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q : ℤ)).obj K) 2 :=
  (Ext.homAddEquiv (X := P)
    (Y := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q : ℤ)).obj K)
    (n := 2)).symm
    ((DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          ((DerivedCategory.singleFunctor C 0).obj P)
          (DerivedCategory.Q.obj K) 0 q).hom.hom y ≫
      eqToHom (by simp) ≫
      (postnikovTargetExtIso K (q : ℤ)).hom ≫
      ((DerivedCategory.singleFunctor C 0).map
        ((DerivedCategory.homologyFunctorFactors C (q : ℤ)).hom.app K))⟦(2 : ℤ)⟧')

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
