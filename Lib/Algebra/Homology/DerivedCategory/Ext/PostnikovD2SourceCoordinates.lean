/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2PageSplice
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovUpperEndpointNormalization

/-!
# Source coordinates for the page-two Postnikov differential

This file identifies the ordinary source-page coordinate with the normalized upper endpoint,
including the equality transports hidden by the adjacent-triangle presentation, then expresses
a source-page element as a morphism into the chain homology object. It also computes the source
morphism selected by the Postnikov-to-splice triangle comparison: the two coordinates differ by
exactly the parity scalar introduced by shifting the triangle.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Opposite

namespace DerivedCategory

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

private lemma castIso_hom_source {D : Type*} [Category D]
    {X Y Z : D} (e : Y ≅ Z) (h : X = Y) :
    (cast (congrArg (fun T : D ↦ T ≅ Z) h.symm) e).hom =
      eqToHom h ≫ e.hom := by
  subst Y
  simp

@[reassoc]
private lemma eqToHom_comp_three_eq_id {D : Type*} [Category D]
    {W X Y : D} (h₁ : W = X) (h₂ : X = Y) (h₃ : Y = W) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ = 𝟙 W := by
  subst X
  subst Y
  simp

set_option backward.isDefEq.respectTransparency true in
private lemma postnikovUpperEndpointIso_hom_explicit
    (K : CochainComplex C ℤ) (q : ℤ) :
    (postnikovUpperEndpointIso K q).hom =
      eqToHom (show
        ((TStructure.t.triangleω₁δ
          (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
          (by simp) (by simp)).obj (Q.obj K)).obj₃ =
            (TStructure.t.truncGE (q + 1)).obj
              ((TStructure.t.truncLT (q + 2)).obj (Q.obj K)) by
          rw [TStructure.t.triangleω₁δ_obj_obj₃]
          simp only [TStructure.eTruncGE_obj_coe, TStructure.eTruncLT_obj_coe]) ≫
        (TStructure.t.truncGE (q + 1)).map
          (eqToHom (show
            (TStructure.t.truncLT (q + 2)).obj (Q.obj K) =
              (TStructure.t.truncLT ((q + 1) + 1)).obj (Q.obj K) by
                rw [show q + 1 + 1 = q + 2 by omega])) ≫
        (postnikovSliceIso (Q.obj K) (q + 1)).hom := by
  let h :
      ((TStructure.t.triangleω₁δ
        (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
        (by simp) (by simp)).obj (Q.obj K)).obj₃ =
          (TStructure.t.truncGE (q + 1)).obj
            ((TStructure.t.truncLT (q + 2)).obj (Q.obj K)) := by
    rw [TStructure.t.triangleω₁δ_obj_obj₃]
    simp only [TStructure.eTruncGE_obj_coe, TStructure.eTruncLT_obj_coe]
  change
    (cast (congrArg (fun T : DerivedCategory C ↦ T ≅
        (singleFunctor C (q + 1)).obj
          ((homologyFunctor C (q + 1)).obj (Q.obj K))) h.symm)
      ((TStructure.t.truncGE (q + 1)).mapIso
          (eqToIso (show
            (TStructure.t.truncLT (q + 2)).obj (Q.obj K) =
              (TStructure.t.truncLT ((q + 1) + 1)).obj (Q.obj K) by
                rw [show q + 1 + 1 = q + 2 by omega])) ≪≫
        postnikovSliceIso (Q.obj K) (q + 1))).hom = _
  rw [castIso_hom_source]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  all_goals exact h

set_option backward.isDefEq.respectTransparency true in
private lemma postnikovSourceShiftedSliceIso_hom_eq
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftFunctor (DerivedCategory C) (q + 1)).map
        (postnikovSliceIso (Q.obj K) (q + 1)).hom ≫
      ((singleFunctors C).shiftIso (q + 1) 0 (q + 1) (by omega)).hom.app
        ((homologyFunctor C (q + 1)).obj (Q.obj K)) =
    eqToHom (show
      ((TStructure.t.truncGE (q + 1)).obj
        ((TStructure.t.truncLT ((q + 1) + 1)).obj (Q.obj K)))⟦q + 1⟧ =
        (shiftedPostnikovAdjacentTriangle K q).obj₃ by
          dsimp [shiftedPostnikovAdjacentTriangle, Triangle.shiftFunctor]
          rw [Triangle.mk_obj₃, TStructure.t.triangleω₁δ_obj_obj₃]
          simp only [TStructure.eTruncGE_obj_coe, TStructure.eTruncLT_obj_coe]
          rw [show q + 1 + 1 = q + 2 by omega]) ≫
      (shiftedPostnikovUpperEndpointIso K q).hom := by
  have hu : (shiftedPostnikovUpperEndpointIso K q).hom =
      (shiftFunctor (DerivedCategory C) (q + 1)).map
          (postnikovUpperEndpointIso K q).hom ≫
        ((singleFunctors C).shiftIso (q + 1) 0 (q + 1) (by omega)).hom.app
          ((homologyFunctor C (q + 1)).obj (Q.obj K)) := by
    rfl
  rw [hu]
  rw [postnikovUpperEndpointIso_hom_explicit]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  erw [eqToHom_comp_three_eq_id_assoc]

set_option backward.isDefEq.respectTransparency true in
/-- Shifting the normalized degree-`q+1` Postnikov slice by any expression equal to `q+1`
agrees with the normalized upper endpoint of the shifted adjacent Postnikov triangle.  The
displayed equality morphism accounts for both cutoff and triangle-object transports; no scalar
or sign is introduced. -/
lemma postnikovSourceShiftedSliceIso_hom_eq_of_shift
    (K : CochainComplex C ℤ) (q n : ℤ) (hn : n = q + 1) :
    (shiftFunctor (DerivedCategory C) n).map
        (postnikovSliceIso (Q.obj K) (q + 1)).hom ≫
      ((singleFunctors C).shiftIso n 0 (q + 1) (by omega)).hom.app
        ((homologyFunctor C (q + 1)).obj (Q.obj K)) =
    eqToHom (show
      ((TStructure.t.truncGE (q + 1)).obj
        ((TStructure.t.truncLT ((q + 1) + 1)).obj (Q.obj K)))⟦n⟧ =
        (shiftedPostnikovAdjacentTriangle K q).obj₃ by
          subst n
          dsimp [shiftedPostnikovAdjacentTriangle, Triangle.shiftFunctor]
          rw [Triangle.mk_obj₃, TStructure.t.triangleω₁δ_obj_obj₃]
          simp only [TStructure.eTruncGE_obj_coe, TStructure.eTruncLT_obj_coe]
          rw [show q + 1 + 1 = q + 2 by omega]) ≫
      (shiftedPostnikovUpperEndpointIso K q).hom := by
  subst n
  exact postnikovSourceShiftedSliceIso_hom_eq K q

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- At bidegree `(0,q+1)`, the ordinary Postnikov page coordinate and the normalized source
coordinate for `d₂` agree after transport to the upper object of the shifted adjacent
Postnikov triangle.  This comparison is unsigned. -/
lemma coyonedaPostnikovE₂PageIso_zero_to_d₂SourceEndpoint
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (x : ((TStructure.t.coyonedaPostnikovSpectralSequence
      ((singleFunctor C 0).obj P) (Q.obj K)).page 2).X (0, q + 1)) :
    (TStructure.t.coyonedaPostnikovE₂PageIso
        ((singleFunctor C 0).obj P) (Q.obj K) 0 (q + 1)).hom.hom x ≫
        eqToHom (show
          ((TStructure.t.truncGE ((q + 1 : ℕ) : ℤ)).obj
            ((TStructure.t.truncLT (((q + 1 : ℕ) : ℤ) + 1)).obj (Q.obj K)))
              ⟦((0 + (q + 1) : ℕ) : ℤ)⟧ =
            (shiftedPostnikovAdjacentTriangle K (q : ℤ)).obj₃ by
              dsimp [shiftedPostnikovAdjacentTriangle, Triangle.shiftFunctor]
              rw [Triangle.mk_obj₃, TStructure.t.triangleω₁δ_obj_obj₃]
              simp only [zero_add, TStructure.eTruncGE_obj_coe,
                TStructure.eTruncLT_obj_coe]
              rw [show (q : ℤ) + 1 + 1 = (q : ℤ) + 2 by omega]) =
      (TStructure.t.coyonedaPostnikovD₂SourcePageIso
          ((singleFunctor C 0).obj P) (Q.obj K) 0 q).hom.hom x ≫
        eqToHom (show
          ((TStructure.t.truncGE ((q : ℤ) + 1)).obj
            ((TStructure.t.truncLT ((q : ℤ) + 2)).obj (Q.obj K)))
              ⟦(0 : ℤ) + q + 1⟧ =
            (shiftedPostnikovAdjacentTriangle K (q : ℤ)).obj₃ by
              dsimp [shiftedPostnikovAdjacentTriangle, Triangle.shiftFunctor]
              rw [Triangle.mk_obj₃, TStructure.t.triangleω₁δ_obj_obj₃]
              simp) := by
  have h := TStructure.coyonedaPostnikovFirstPageXIso_hom_apply_eq_of_indices_assoc
    TStructure.t ((singleFunctor C 0).obj P) (Q.obj K) (0, q + 1)
      (((q : ℤ) + 1 : ℤ) : EInt)
      ((((q : ℤ) + 1 + 1 : ℤ)) : EInt)
      (((q : ℤ) + 1 : ℤ) : EInt)
      (((q : ℤ) + 2 : ℤ) : EInt)
      (by simp) (by exact congrArg (fun z : ℤ => (z : EInt)) (by omega)) (by simp)
      (by exact congrArg (fun z : ℤ => (z : EInt)) (by omega))
      ((0 : ℤ) + ((q : ℤ) + 1)) ((0 : ℤ) + q + 1)
      (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega)
      (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega) x
      (eqToHom (show
        ((TStructure.t.truncGE ((q : ℤ) + 1)).obj
          ((TStructure.t.truncLT ((q : ℤ) + 2)).obj (Q.obj K)))
            ⟦(0 : ℤ) + q + 1⟧ =
          (shiftedPostnikovAdjacentTriangle K (q : ℤ)).obj₃ by
            dsimp [shiftedPostnikovAdjacentTriangle, Triangle.shiftFunctor]
            rw [Triangle.mk_obj₃, TStructure.t.triangleω₁δ_obj_obj₃]
            simp))
  dsimp [TStructure.coyonedaPostnikovE₂PageIso,
    TStructure.coyonedaPostnikovD₂SourcePageIso]
  convert h using 1 <;> simp
  all_goals congr 2

end DerivedCategory

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

/-- A page-two source element at bidegree `(0,q+1)`, expressed as the corresponding morphism
from the representing object to the degree-`q+1` chain homology of `K`. -/
def coyonedaPostnikovD₂SourceHom
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (x : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (0, q + 1)) :
    P ⟶
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) ((q : ℤ) + 1)).obj K :=
  (DerivedCategory.singleFunctor C 0).preimage
    ((DerivedCategory.TStructure.t.coyonedaPostnikovD₂SourcePageIso
        ((DerivedCategory.singleFunctor C 0).obj P) (DerivedCategory.Q.obj K) 0 q).hom.hom x ≫
      eqToHom (by
        dsimp [DerivedCategory.shiftedPostnikovAdjacentTriangle,
          Triangle.shiftFunctor]
        rw [Triangle.mk_obj₃,
          DerivedCategory.TStructure.t.triangleω₁δ_obj_obj₃]
        simp) ≫
      (DerivedCategory.shiftedPostnikovUpperEndpointIso K (q : ℤ)).hom ≫
      (DerivedCategory.singleFunctor C 0).map
        ((DerivedCategory.homologyFunctorFactors C ((q : ℤ) + 1)).hom.app K))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism selected by the Postnikov-to-splice source component is exactly the normalized
source coordinate multiplied by the parity scalar of the triangle shift. -/
lemma coyonedaPostnikovD₂SpliceSource_eq
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (x : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (0, q + 1)) :
    let z : (DerivedCategory.singleFunctor C 0).obj P ⟶
        (DerivedCategory.shiftedPostnikovAdjacentTriangle K (q : ℤ)).obj₃ :=
      (DerivedCategory.TStructure.t.coyonedaPostnikovD₂SourcePageIso
        ((DerivedCategory.singleFunctor C 0).obj P) (DerivedCategory.Q.obj K) 0 q).hom.hom x ≫
      eqToHom (by
        dsimp [DerivedCategory.shiftedPostnikovAdjacentTriangle,
          Triangle.shiftFunctor]
        rw [Triangle.mk_obj₃,
          DerivedCategory.TStructure.t.triangleω₁δ_obj_obj₃]
        simp)
    let f := (DerivedCategory.singleFunctor C 0).preimage
      (z ≫ (shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₃ ≫
        (spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K (q : ℤ))).hom)
    f = ((q : ℤ) + 1).negOnePow • coyonedaPostnikovD₂SourceHom K P q x := by
  dsimp only
  apply (DerivedCategory.singleFunctor C 0).map_injective
  rw [(DerivedCategory.singleFunctor C 0).map_preimage]
  rw [Functor.map_units_smul]
  dsimp only [coyonedaPostnikovD₂SourceHom]
  rw [(DerivedCategory.singleFunctor C 0).map_preimage]
  rw [shiftedPostnikovAdjacentTriangleIsoSplice_hom_hom₃_upper]
  simp only [Category.assoc, Linear.comp_units_smul]

omit [HasDerivedCategory C] in
/-- Multiplying both a degree-zero source morphism and its two-step connecting class by the same
parity scalar cancels. This is the sign algebra used after normalizing both page endpoints. -/
lemma connectingTwo_negOnePow_cancel
    [HasExt.{v} C] (R : TwoStepResolution (C := C)) (P : C) (n : ℤ)
    (f : P ⟶ R.complex.X₃) :
    n.negOnePow • R.connectingTwo P (Ext.mk₀ (n.negOnePow • f)) =
      R.connectingTwo P (Ext.mk₀ f) := by
  rcases Int.even_or_odd n with hn | hn
  · rw [Int.negOnePow_even n hn]
    simp
  · rw [Int.negOnePow_odd n hn]
    simp

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
