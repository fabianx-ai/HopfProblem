/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovUpperEndpointNormalization
public import Lib.Algebra.Homology.DerivedCategory.Ext.TwoStepSpliceLowerNormalization

/-!
# Normalization of the concrete lower Postnikov endpoint

This file compares the lower edge of the shifted adjacent Postnikov triangle with the standard
mapping-cone model. The parity scalar introduced by the triangle shift occurs on both routes and
cancels, so the exported lower endpoint comparison is unsigned.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated HomologicalComplex

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C]

attribute [local instance] HasDerivedCategory.standard

private lemma child_assoc_four {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ : D}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) :
    ((f ≫ g) ≫ h) ≫ i = f ≫ g ≫ h ≫ i := by
  simp

private lemma child_castIso_hom {D : Type*} [Category D]
    {X Y Z : D} (e : X ≅ Y) (h : Y = Z) :
    (cast (congrArg (fun T : D ↦ X ≅ T) h) e).hom =
      e.hom ≫ eqToHom h := by
  subst Z
  simp

private lemma child_eqToIso_hom_comp_family
    {D : Type*} [Category D] {A : Type*}
    (X : A → D) (Z : D) (f : ∀ a, X a ⟶ Z)
    {a b : A} (h : a = b) :
    (eqToIso (congrArg X h)).hom ≫ f b = f a := by
  subst b
  simp

private noncomputable def child_adjacentTwoSliceLowerHomologyIso
    (K : CochainComplex C ℤ) (q : ℤ) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj K ≅
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
        (CochainComplex.adjacentTwoSlice K q) := by
  let ι := K.ιTruncLE (q + 1)
  let π := (K.truncLE (q + 1)).πTruncGE q
  let _ : QuasiIsoAt ι q :=
    CochainComplex.quasiIsoAt_ιTruncLE K (q + 1) q (by omega)
  let _ : QuasiIsoAt π q :=
    CochainComplex.quasiIsoAt_πTruncGE (K.truncLE (q + 1)) q q (by omega)
  exact (isoOfQuasiIsoAt ι q).symm ≪≫ isoOfQuasiIsoAt π q

set_option backward.isDefEq.respectTransparency false in
private lemma child_postnikovSlice_inv_homology
    (X : DerivedCategory C) (q : ℤ) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app
          ((DerivedCategory.homologyFunctor C q).obj X) ≫
        (DerivedCategory.homologyFunctor C q).map
          (DerivedCategory.postnikovSliceIso X q).inv =
      (DerivedCategory.postnikovSliceHomologyIso X q).inv := by
  rw [← cancel_mono
    ((DerivedCategory.homologyFunctor C q).map
        (DerivedCategory.postnikovSliceIso X q).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app
        ((DerivedCategory.homologyFunctor C q).obj X))]
  simp only [Category.assoc]
  rw [← (DerivedCategory.homologyFunctor C q).map_comp_assoc]
  simp only [Iso.inv_hom_id, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]
  slice_rhs 2 3 =>
    rw [DerivedCategory.homologyFunctor_map_postnikovSliceIso_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma child_unshifted_lower_route_homology
    (K : CochainComplex C ℤ) (q : ℤ) :
    let T :=
      (DerivedCategory.TStructure.t.triangleω₁δ
        (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
        (by simp) (by simp)).obj (DerivedCategory.Q.obj K)
    (DerivedCategory.homologyFunctorFactors C q).inv.app K ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app
          ((DerivedCategory.homologyFunctor C q).obj
            (DerivedCategory.Q.obj K)) ≫
        (DerivedCategory.homologyFunctor C q).map
          (DerivedCategory.postnikovSliceIso
            (DerivedCategory.Q.obj K) q).inv ≫
        (DerivedCategory.homologyFunctor C q).map T.mor₁ ≫
        (DerivedCategory.homologyFunctor C q).map
          (DerivedCategory.postnikovTwoSliceIso K q).hom ≫
        (DerivedCategory.homologyFunctorFactors C q).hom.app
          (CochainComplex.adjacentTwoSlice K q) =
      (child_adjacentTwoSliceLowerHomologyIso K q).hom := by
  dsimp only
  rw [reassoc_of% child_postnikovSlice_inv_homology
    (DerivedCategory.Q.obj K) q]
  let ι := K.ιTruncLE (q + 1)
  let π := (K.truncLE (q + 1)).πTruncGE q
  let _ : QuasiIsoAt ι q :=
    CochainComplex.quasiIsoAt_ιTruncLE K (q + 1) q (by omega)
  let _ : QuasiIsoAt π q :=
    CochainComplex.quasiIsoAt_πTruncGE (K.truncLE (q + 1)) q q (by omega)
  have hcut : q + 2 - 1 = q + 1 := by omega
  have hBase :
      DerivedCategory.Q.obj (K.truncLE (q + 2 - 1)) =
        DerivedCategory.Q.obj (K.truncLE (q + 1)) := by
    exact congrArg
      (fun n : ℤ ↦ DerivedCategory.Q.obj (K.truncLE n)) hcut
  have hGE :
      (DerivedCategory.TStructure.t.truncGE q).obj
          (DerivedCategory.Q.obj (K.truncLE (q + 2 - 1))) =
        (DerivedCategory.TStructure.t.truncGE q).obj
          (DerivedCategory.Q.obj (K.truncLE (q + 1))) :=
    congrArg (DerivedCategory.TStructure.t.truncGE q).obj hBase
  let eLT :
      (DerivedCategory.TStructure.t.truncLT (q + 2)).obj
          (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj (K.truncLE (q + 1)) :=
    DerivedCategory.truncLTIsoQTruncLE K (q + 2) ≪≫ eqToIso hBase
  let eGE :
      (DerivedCategory.TStructure.t.truncGE q).obj
          ((DerivedCategory.TStructure.t.truncLT (q + 2)).obj
            (DerivedCategory.Q.obj K)) ≅
        (DerivedCategory.TStructure.t.truncGE q).obj
          (DerivedCategory.Q.obj (K.truncLE (q + 1))) :=
    cast (congrArg (fun T : DerivedCategory C ↦
      (DerivedCategory.TStructure.t.truncGE q).obj
          ((DerivedCategory.TStructure.t.truncLT (q + 2)).obj
            (DerivedCategory.Q.obj K)) ≅ T) hGE)
      ((DerivedCategory.TStructure.t.truncGE q).mapIso
        (DerivedCategory.truncLTIsoQTruncLE K (q + 2)))
  have heGE : eGE.hom =
      (DerivedCategory.TStructure.t.truncGE q).map eLT.hom := by
    dsimp only [eGE, eLT]
    rw [child_castIso_hom]
    simp only [Iso.trans_hom, eqToIso.hom, Functor.map_comp,
      Functor.mapIso_hom, eqToHom_map]
    exact hGE
  have hpost :
      (DerivedCategory.postnikovTwoSliceIso K q).hom =
        eGE.hom ≫
          (DerivedCategory.truncGEIsoQTruncGE
            (K.truncLE (q + 1)) q).hom := by
    rfl
  let a :
      (DerivedCategory.TStructure.t.truncLT (q + 1)).obj
          (DerivedCategory.Q.obj K) ⟶
        (DerivedCategory.TStructure.t.truncLT (q + 2)).obj
          (DerivedCategory.Q.obj K) :=
    (DerivedCategory.TStructure.t.eTruncLT.map
      (homOfLE (show ((q + 1 : ℤ) : EInt) ≤ ((q + 2 : ℤ) : EInt) by
        simp))).app (DerivedCategory.Q.obj K)
  let f :
      (DerivedCategory.TStructure.t.truncLT (q + 1)).obj
          (DerivedCategory.Q.obj K) ⟶
        DerivedCategory.Q.obj (K.truncLE (q + 1)) :=
    a ≫ eLT.hom
  have hroute :
      ((DerivedCategory.TStructure.t.triangleω₁δ
        (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
        (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₁ ≫
          (DerivedCategory.TStructure.t.truncGE q).map eLT.hom =
        (DerivedCategory.TStructure.t.truncGE q).map f := by
    rw [DerivedCategory.TStructure.t.triangleω₁δ_obj_mor₁]
    change (DerivedCategory.TStructure.t.truncGE q).map a ≫
        (DerivedCategory.TStructure.t.truncGE q).map eLT.hom = _
    rw [← Functor.map_comp]
  rw [← cancel_mono (child_adjacentTwoSliceLowerHomologyIso K q).inv]
  simp only [Category.assoc, Iso.hom_inv_id]
  dsimp only [child_adjacentTwoSliceLowerHomologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv]
  have hπnat := (DerivedCategory.homologyFunctorFactors C q).hom.naturality π
  have hιnat := (DerivedCategory.homologyFunctorFactors C q).hom.naturality ι
  have hπhom : (isoOfQuasiIsoAt π q).hom =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map π := rfl
  have hιhom : (isoOfQuasiIsoAt ι q).hom =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map ι := rfl
  let _ : IsIso
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map π) := by
    rw [← hπhom]
    infer_instance
  let _ : IsIso ((DerivedCategory.Q ⋙
      DerivedCategory.homologyFunctor C q).map π) :=
    (NatIso.isIso_map_iff
      (DerivedCategory.homologyFunctorFactors C q) π).2 (by infer_instance)
  have hπsuffix :
      (DerivedCategory.homologyFunctorFactors C q).hom.app
            (CochainComplex.adjacentTwoSlice K q) ≫
          (isoOfQuasiIsoAt π q).inv =
        inv ((DerivedCategory.Q ⋙
              DerivedCategory.homologyFunctor C q).map π) ≫
          (DerivedCategory.homologyFunctorFactors C q).hom.app
            (K.truncLE (q + 1)) := by
    rw [← cancel_mono (isoOfQuasiIsoAt π q).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hπhom, ← hπnat]
    simp
  rw [reassoc_of% hπsuffix]
  rw [hιhom, ← hιnat]
  rw [hpost, heGE]
  simp only [Functor.map_comp, Category.assoc]
  have hQπ := DerivedCategory.truncGEπ_comp_truncGEIsoQTruncGE_hom
    (K.truncLE (q + 1)) q
  have hQπmap := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor C q).map f) hQπ
  simp only [Functor.map_comp] at hQπmap
  let _ : IsIso ((DerivedCategory.homologyFunctor C q).map
      (DerivedCategory.Q.map π)) := by
    change IsIso ((DerivedCategory.Q ⋙
      DerivedCategory.homologyFunctor C q).map π)
    infer_instance
  let _ : IsIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ q).app
        (DerivedCategory.Q.obj (K.truncLE (q + 1))))) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ _ q
  have htruncSuffix :
      (DerivedCategory.homologyFunctor C q).map
            (DerivedCategory.truncGEIsoQTruncGE
              (K.truncLE (q + 1)) q).hom ≫
          inv ((DerivedCategory.homologyFunctor C q).map
            (DerivedCategory.Q.map π)) =
        inv ((DerivedCategory.homologyFunctor C q).map
          ((DerivedCategory.TStructure.t.truncGEπ q).app
            (DerivedCategory.Q.obj (K.truncLE (q + 1))))) := by
    rw [← cancel_mono ((DerivedCategory.homologyFunctor C q).map
      (DerivedCategory.Q.map π))]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← hQπmap]
    simp
  rw [reassoc_of% htruncSuffix]
  rw [← (DerivedCategory.homologyFunctor C q).map_comp_assoc]
  rw [hroute]
  have htruncNat :=
    DerivedCategory.TStructure.t.truncGEπ_naturality q f
  have htruncNatMap := congrArg
    (fun z ↦ (DerivedCategory.homologyFunctor C q).map z) htruncNat
  simp only [Functor.map_comp] at htruncNatMap
  let _ : IsIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ q).app
        ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj
          (DerivedCategory.Q.obj K)))) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ _ q
  have hGEroute :
      (DerivedCategory.homologyFunctor C q).map
            ((DerivedCategory.TStructure.t.truncGE q).map f) ≫
          inv ((DerivedCategory.homologyFunctor C q).map
            ((DerivedCategory.TStructure.t.truncGEπ q).app
              (DerivedCategory.Q.obj (K.truncLE (q + 1))))) =
        inv ((DerivedCategory.homologyFunctor C q).map
              ((DerivedCategory.TStructure.t.truncGEπ q).app
                ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj
                  (DerivedCategory.Q.obj K)))) ≫
          (DerivedCategory.homologyFunctor C q).map f := by
    rw [← cancel_mono ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ q).app
        (DerivedCategory.Q.obj (K.truncLE (q + 1)))))]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← htruncNatMap]
    simp
  rw [reassoc_of% hGEroute]
  have hBaseι :
      (eqToIso hBase).hom ≫
          DerivedCategory.Q.map (K.ιTruncLE (q + 1)) =
        DerivedCategory.Q.map (K.ιTruncLE (q + 2 - 1)) := by
    exact child_eqToIso_hom_comp_family
      (fun n : ℤ ↦ DerivedCategory.Q.obj (K.truncLE n))
      (DerivedCategory.Q.obj K)
      (fun n : ℤ ↦ DerivedCategory.Q.map (K.ιTruncLE n)) hcut
  have heLTι :
      eLT.hom ≫ DerivedCategory.Q.map (K.ιTruncLE (q + 1)) =
        (DerivedCategory.TStructure.t.truncLTι (q + 2)).app
          (DerivedCategory.Q.obj K) := by
    dsimp only [eLT]
    rw [Iso.trans_hom, Category.assoc, hBaseι]
    exact DerivedCategory.truncLTIsoQTruncLE_hom_comp_ι K (q + 2)
  have hfι :
      f ≫ DerivedCategory.Q.map ι =
        (DerivedCategory.TStructure.t.truncLTι (q + 1)).app
          (DerivedCategory.Q.obj K) := by
    dsimp only [f]
    rw [Category.assoc, heLTι]
    dsimp only [a]
    exact DerivedCategory.TStructure.t.eTruncLT_map_app_eTruncLTι_app
      (homOfLE (show ((q + 1 : ℤ) : EInt) ≤ ((q + 2 : ℤ) : EInt) by
        simp))
      (DerivedCategory.Q.obj K)
  have hfιMap := congrArg
    (fun z ↦ (DerivedCategory.homologyFunctor C q).map z) hfι
  simp only [Functor.map_comp] at hfιMap
  rw [show (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C q).map ι =
    (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Q.map ι) by rfl]
  rw [reassoc_of% hfιMap]
  dsimp only [DerivedCategory.postnikovSliceHomologyIso]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma child_homologyFunctor_map_commShiftIso_hom_comp_shiftIso
    (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (DerivedCategory.homologyFunctor C a).map
          ((DerivedCategory.Q.commShiftIso n).hom.app K) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          n a a' ha').hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctorFactors C a).hom.app (K⟦n⟧) ≫
        ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          n a a' ha').hom.app K ≫
        (DerivedCategory.homologyFunctorFactors C a').inv.app K := by
  have hshift := DerivedCategory.shiftMap_homologyFunctor_map_Q
    (C := C) (K := K⟦n⟧) (L := K) (𝟙 (K⟦n⟧)) a a' ha'
  dsimp [Functor.shiftMap, ShiftedHom.map] at hshift
  rw [DerivedCategory.Q.map_id] at hshift
  simp only [Category.id_comp] at hshift
  rw [((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shift a).map_id]
    at hshift
  simp only [Category.id_comp] at hshift
  simpa only [Functor.map_comp, Functor.map_id, Category.id_comp,
    DerivedCategory.shift_homologyFunctor,
    CochainComplex.homologyFunctor_shift] using hshift

set_option backward.isDefEq.respectTransparency false in
private lemma child_homology_shiftIso_hom_comp_factors
    (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    ((DerivedCategory.homologyFunctor C 0).shiftIso
          n a a' ha').hom.app (DerivedCategory.Q.obj K) ≫
        (DerivedCategory.homologyFunctorFactors C a').hom.app K =
      (DerivedCategory.homologyFunctor C a).map
          ((DerivedCategory.Q.commShiftIso n).inv.app K) ≫
        (DerivedCategory.homologyFunctorFactors C a).hom.app (K⟦n⟧) ≫
        ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          n a a' ha').hom.app K := by
  rw [← cancel_epi
    ((DerivedCategory.homologyFunctor C a).map
      ((DerivedCategory.Q.commShiftIso n).hom.app K))]
  rw [reassoc_of%
    child_homologyFunctor_map_commShiftIso_hom_comp_shiftIso]
  slice_lhs 3 4 =>
    erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  slice_rhs 1 2 =>
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  erw [Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma child_singleFunctorCompHomologyFunctorIso_shiftIso_one_negOne
    (A : C) :
    (DerivedCategory.homologyFunctor C (-1)).map
          (((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).hom.app A) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app A =
      ((DerivedCategory.homologyFunctor C 0).shiftIso
          1 (-1) 0 (by omega)).hom.app
            ((DerivedCategory.singleFunctor C 0).obj A) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app A := by
  have hchain :
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-1)).map
          (((CochainComplex.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).hom.app A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) (-1)).hom.app A =
      ((HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftIso
            1 (-1) 0 (by omega)).hom.app
              (((CochainComplex.singleFunctors C).functor 0).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) 0).hom.app A := by
    change _ =
      (CochainComplex.ShiftSequence.shiftIso C
        1 (-1) 0 (by omega)).hom.app
          (((CochainComplex.singleFunctors C).functor 0).obj A) ≫ _
    rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    dsimp [CochainComplex.singleFunctors]
    rw [← cancel_epi
      (((((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A)⟦(1 : ℤ)⟧).homologyπ
        (-1)))]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
    erw [ShortComplex.homologyπ_naturality_assoc]
    change _ = _ ≫
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A).homologyπ 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) 0 A).hom)
    rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
    rw [HomologicalComplex.singleObjCyclesSelfIso_hom,
      HomologicalComplex.singleObjCyclesSelfIso_hom]
    rw [HomologicalComplex.cyclesMap_i_assoc]
    erw [ShortComplex.cyclesMap_i_assoc]
    dsimp [CochainComplex.shiftShortComplexFunctorIso,
      CochainComplex.shiftShortComplexFunctor', CochainComplex.shiftEval,
      HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq]
    simp
    rfl
  let α := (DerivedCategory.singleFunctorsPostcompQIso C).hom
  let S0 := ((CochainComplex.singleFunctors C).functor 0).obj A
  have hcomm := congrArg (fun t ↦ t.app A) (α.comm 1 (-1) 0 (by omega))
  have hcomm' :
      ((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).hom.app A ≫
          (α.hom (-1)).app A =
        ((α.hom 0).app A)⟦1⟧' ≫
          (((CochainComplex.singleFunctors C).postcomp
            DerivedCategory.Q).shiftIso
              1 (-1) 0 (by omega)).hom.app A := by
    simpa using hcomm
  have hnat :=
    ((DerivedCategory.homologyFunctor C 0).shiftIso
      1 (-1) 0 (by omega)).hom.naturality ((α.hom 0).app A)
  have hnat' := hnat
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnat'
  have hshift1 := child_homology_shiftIso_hom_comp_factors
    (C := C) 1 (-1) 0 (by omega) S0
  have hpost :
      (DerivedCategory.homologyFunctor C (-1)).map
          ((((CochainComplex.singleFunctors C).postcomp
            DerivedCategory.Q).shiftIso
              1 (-1) 0 (by omega)).hom.app A) ≫
        (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
          (((CochainComplex.singleFunctors C).functor (-1)).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) (-1)).hom.app A =
      (DerivedCategory.homologyFunctor C (-1)).map
          ((DerivedCategory.Q.commShiftIso 1).inv.app S0) ≫
        (DerivedCategory.homologyFunctorFactors C (-1)).hom.app (S0⟦1⟧) ≫
        ((HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftIso
            1 (-1) 0 (by omega)).hom.app S0 ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) 0).hom.app A := by
    rw [SingleFunctors.postcomp_shiftIso_hom_app]
    rw [Functor.map_comp]
    have hfac := (DerivedCategory.homologyFunctorFactors C (-1)).hom.naturality
      (((CochainComplex.singleFunctors C).shiftIso
        1 (-1) 0 (by omega)).hom.app A)
    erw [Functor.comp_map] at hfac
    slice_lhs 2 4 =>
      rw [reassoc_of% hfac]
    rw [hchain]
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso]
  erw [Category.id_comp, Category.id_comp]
  rw [← Functor.map_comp_assoc]
  rw [hcomm']
  rw [Functor.map_comp_assoc]
  erw [hpost]
  rw [← reassoc_of% hshift1]
  erw [reassoc_of% hnat']
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma child_singleFunctorCompHomologyFunctorIso_shiftIso_one_negOne_inv
    (A : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).inv.app A ≫
        (DerivedCategory.homologyFunctor C (-1)).map
          (((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).inv.app A) =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          1 (-1) 0 (by omega)).inv.app
            ((DerivedCategory.singleFunctor C 0).obj A) := by
  rw [← cancel_mono
    ((DerivedCategory.homologyFunctor C (-1)).map
        (((DerivedCategory.singleFunctors C).shiftIso
          1 (-1) 0 (by omega)).hom.app A) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app A)]
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  slice_lhs 2 3 =>
    erw [Category.id_comp]
  rw [Iso.inv_hom_id_app]
  rw [child_singleFunctorCompHomologyFunctorIso_shiftIso_one_negOne]
  slice_rhs 2 3 =>
    rw [Iso.inv_hom_id_app]
  slice_rhs 2 3 =>
    erw [Category.id_comp]
  rw [Iso.inv_hom_id_app]

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] in
private lemma child_mappingCone_lower_homology
    (K : CochainComplex C ℤ) (q : ℤ)
    (hOne : 1 + (-1 : ℤ) = 0 := by omega)
    (hShift : q + 1 + (-1 : ℤ) = q := by omega) :
    let R := homologyTwoStepResolutionInt K q
    let L := CochainComplex.adjacentTwoSlice K q
    (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) 0 R.F).inv ≫
      (CochainComplex.ShiftSequence.shiftIso C
          1 (-1) 0 hOne).inv.app
            ((CochainComplex.singleFunctor C 0).obj R.F) ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-1)).map
        (mappingConeLowerInclusion R ≫
          (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv) ≫
      (CochainComplex.ShiftSequence.shiftIso C
          (q + 1) (-1) q hShift).hom.app L =
      (q + 1).negOnePow • (child_adjacentTwoSliceLowerHomologyIso K q).hom := by
  dsimp only
  erw [← cancel_epi
    (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) 0 (homologyTwoStepResolutionInt K q).F).hom]
  slice_lhs 1 2 =>
    rw [Iso.hom_inv_id]
  rw [Category.id_comp]
  rw [← cancel_mono
    ((CochainComplex.ShiftSequence.shiftIso C
      (q + 1) (-1) q hShift).inv.app
        (CochainComplex.adjacentTwoSlice K q))]
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Linear.units_smul_comp]
  let hιShift :
      (shiftFunctor (HomologicalComplex C (ComplexShape.up ℤ)) (q + 1) ⋙
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shift
            (-1)).obj (CochainComplex.adjacentTwoSlice K q) ⟶
        (CochainComplex.shiftedAdjacentTwoSlice K q).opcycles (-1) :=
    (CochainComplex.shiftedAdjacentTwoSlice K q).homologyι (-1)
  rw [← cancel_mono hιShift]
  simp only [Category.assoc]
  dsimp only [hιShift]
  slice_lhs 3 4 =>
    erw [Category.id_comp]
  slice_lhs 2 3 =>
    erw [HomologicalComplex.homologyι_naturality]
  have hSourceShiftι :
      (CochainComplex.ShiftSequence.shiftIso C
          1 (-1) 0 hOne).inv.app
            ((CochainComplex.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K q).F) ≫
        (((CochainComplex.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K q).F)⟦1⟧).homologyι (-1) =
      (((CochainComplex.singleFunctor C 0).obj
          (homologyTwoStepResolutionInt K q).F).homologyι 0) ≫
        ShortComplex.opcyclesMap
          ((CochainComplex.shiftShortComplexFunctorIso C 1 (-1) 0 hOne).inv.app
            ((CochainComplex.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K q).F)) := by
    rw [CochainComplex.ShiftSequence.shiftIso_inv_app]
    exact ShortComplex.homologyι_naturality _
  have hTargetShiftι :
      (CochainComplex.ShiftSequence.shiftIso C
          (q + 1) (-1) q hShift).inv.app
            (CochainComplex.adjacentTwoSlice K q) ≫
        (CochainComplex.shiftedAdjacentTwoSlice K q).homologyι (-1) =
      (CochainComplex.adjacentTwoSlice K q).homologyι q ≫
        ShortComplex.opcyclesMap
          ((CochainComplex.shiftShortComplexFunctorIso C
            (q + 1) (-1) q hShift).inv.app
              (CochainComplex.adjacentTwoSlice K q)) := by
    rw [CochainComplex.ShiftSequence.shiftIso_inv_app]
    exact ShortComplex.homologyι_naturality _
  rw [reassoc_of% hSourceShiftι]
  rw [← Linear.units_smul_comp]
  slice_rhs 2 4 =>
    rw [hTargetShiftι]
  have hSingleι :
      ((CochainComplex.singleFunctor C 0).obj
        (homologyTwoStepResolutionInt K q).F).homologyι 0 =
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) 0 (homologyTwoStepResolutionInt K q).F).hom ≫
      (HomologicalComplex.singleObjOpcyclesSelfIso
        (ComplexShape.up ℤ) 0 (homologyTwoStepResolutionInt K q).F).hom := by
    exact
      (HomologicalComplex.singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom
        (C := C) (c := ComplexShape.up ℤ)
        (j := 0) (A := (homologyTwoStepResolutionInt K q).F)).symm
  rw [hSingleι]
  have hcomponents :
      (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.up ℤ) 0 (homologyTwoStepResolutionInt K q).F).hom ≫
        ShortComplex.opcyclesMap
            ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)) ≫
        HomologicalComplex.opcyclesMap
          (mappingConeLowerInclusion (homologyTwoStepResolutionInt K q) ≫
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)
          (-1) =
      ((q + 1).negOnePow •
          (child_adjacentTwoSliceLowerHomologyIso K q).hom) ≫
          (CochainComplex.adjacentTwoSlice K q).homologyι q ≫
          ShortComplex.opcyclesMap
            ((CochainComplex.shiftShortComplexFunctorIso C
              (q + 1) (-1) q hShift).inv.app
                (CochainComplex.adjacentTwoSlice K q)) := by
    rw [HomologicalComplex.singleObjOpcyclesSelfIso_hom]
    have hSourceOp :
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj
            (homologyTwoStepResolutionInt K q).F).pOpcycles 0 ≫
          ShortComplex.opcyclesMap
            ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)) =
        ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)).τ₂ ≫
          (((CochainComplex.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K q).F)⟦(1 : ℤ)⟧).pOpcycles (-1) := by
      change ShortComplex.pOpcycles _ ≫ ShortComplex.opcyclesMap _ =
        _ ≫ ShortComplex.pOpcycles _
      exact ShortComplex.p_opcyclesMap _
    have hPhysicalOp := HomologicalComplex.p_opcyclesMap
      (mappingConeLowerInclusion (homologyTwoStepResolutionInt K q) ≫
        (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)
      (-1)
    calc
      _ = (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℤ) 0
              (homologyTwoStepResolutionInt K q).F).inv ≫
            ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)).τ₂ ≫
            (((CochainComplex.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K q).F)⟦(1 : ℤ)⟧).pOpcycles (-1) ≫
            HomologicalComplex.opcyclesMap
              (mappingConeLowerInclusion (homologyTwoStepResolutionInt K q) ≫
                (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)
              (-1) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℤ) 0
              (homologyTwoStepResolutionInt K q).F).inv ≫ z ≫
            HomologicalComplex.opcyclesMap
              (mappingConeLowerInclusion (homologyTwoStepResolutionInt K q) ≫
                (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)
              (-1)) hSourceOp
      _ = (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℤ) 0
              (homologyTwoStepResolutionInt K q).F).inv ≫
            ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)).τ₂ ≫
            (mappingConeLowerInclusion (homologyTwoStepResolutionInt K q) ≫
              (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv).f (-1) ≫
            (CochainComplex.shiftedAdjacentTwoSlice K q).pOpcycles (-1) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℤ) 0
              (homologyTwoStepResolutionInt K q).F).inv ≫
            ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)).τ₂ ≫ z)
          hPhysicalOp
      _ = _ := by
        simp only [HomologicalComplex.comp_f]
        have hsourceτ :
            ((CochainComplex.shiftShortComplexFunctorIso C
              1 (-1) 0 hOne).inv.app
                ((CochainComplex.singleFunctor C 0).obj
                  (homologyTwoStepResolutionInt K q).F)).τ₂ =
              (((CochainComplex.singleFunctor C 0).obj
                (homologyTwoStepResolutionInt K q).F).shiftFunctorObjXIso
                  1 (-1) 0 (by omega)).inv := by
          simp only [CochainComplex.shiftShortComplexFunctorIso_inv_app_τ₂]
          rfl
        rw [hsourceτ]
        have hadj :
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv.f (-1) =
              (CochainComplex.twoTermPointIso
                (K.opcyclesToCycles q (q + 1)) (-1)).inv ≫
              (CochainComplex.shiftedTwoSlicePointIso K q (-1)).inv := rfl
        rw [hadj]
        simp only [Category.assoc]
        have hpt :
            CochainComplex.twoTermPointIso
                (K.opcyclesToCycles q (q + 1)) (-1) =
              CochainComplex.twoTermPointIsoNegOne
                (K.opcyclesToCycles q (q + 1)) := by
          dsimp [CochainComplex.twoTermPointIso]
        rw [hpt]
        have hsp : CochainComplex.shiftedTwoSlicePointIso K q (-1) =
            CochainComplex.shiftedTwoSlicePointIsoNegOne K q := by
          dsimp [CochainComplex.shiftedTwoSlicePointIso]
        rw [hsp]
        have htwoInv :
            (CochainComplex.twoTermPointIsoNegOne
              (K.opcyclesToCycles q (q + 1))).inv =
                (CochainComplex.mappingCone.fst
                  ((CochainComplex.singleFunctor C 0).map
                    (K.opcyclesToCycles q (q + 1)))).1.v
                    (-1) 0 (by omega) ≫
                (HomologicalComplex.singleObjXSelf
                  (ComplexShape.up ℤ) 0 (K.opcycles q)).hom ≫
                (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) 0 (K.opcycles q)).inv := by
          dsimp [CochainComplex.twoTermPointIsoNegOne,
            CategoryTheory.Limits.isoBiprodZero,
            HomologicalComplex.singleObjXSelf,
            HomologicalComplex.singleObjXIsoOfEq,
            CochainComplex.mappingCone.fst]
          change _ =
            HomologicalComplex.homotopyCofiber.fstX
                ((CochainComplex.singleFunctor C 0).map
                  (K.opcyclesToCycles q (q + 1))) (-1) 0
                    CochainComplex.relNegOneZero ≫
              𝟙 _ ≫ 𝟙 _
          simp [HomologicalComplex.homotopyCofiber.fstX]
          rfl
        rw [htwoInv]
        simp only [Category.assoc]
        have hlower :
            (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0
                (homologyTwoStepResolutionInt K q).F).inv ≫
              (((CochainComplex.singleFunctor C 0).obj
                (homologyTwoStepResolutionInt K q).F).shiftFunctorObjXIso
                  1 (-1) 0 (by omega)).inv ≫
              (mappingConeLowerInclusion
                (homologyTwoStepResolutionInt K q)).f (-1) ≫
              (CochainComplex.mappingCone.fst
                ((CochainComplex.singleFunctor C 0).map
                  (K.opcyclesToCycles q (q + 1)))).1.v
                    (-1) 0 (by omega) ≫
              (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0 (K.opcycles q)).hom =
              K.homologyι q := by
          change
            (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0
                (homologyTwoStepResolutionInt K q).F).inv ≫
              (((CochainComplex.singleFunctor C 0).obj
                (homologyTwoStepResolutionInt K q).F).shiftFunctorObjXIso
                  1 (-1) 0 (by omega)).inv ≫
              (mappingConeLowerInclusion
                (homologyTwoStepResolutionInt K q)).f (-1) ≫
              (CochainComplex.mappingCone.fst
                ((CochainComplex.singleFunctor C 0).map
                  (homologyTwoStepResolutionInt K q).complex.f)).1.v
                    (-1) 0 (by omega) ≫
              (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) 0
                (homologyTwoStepResolutionInt K q).complex.X₁).hom =
              (homologyTwoStepResolutionInt K q).ι
          exact mappingConeLowerInclusion_f_negOne
            (homologyTwoStepResolutionInt K q)
        rw [reassoc_of% hlower]
        let ι := K.ιTruncLE (q + 1)
        let _ : QuasiIsoAt ι q :=
          CochainComplex.quasiIsoAt_ιTruncLE K (q + 1) q (by omega)
        let _ : IsIso (HomologicalComplex.opcyclesMap ι q) :=
          CochainComplex.isIso_opcyclesMap_ιTruncLE K q
        have hpoint :
            (HomologicalComplex.singleObjXSelf
                (ComplexShape.down ℕ) 0 (K.opcycles q)).inv ≫
              (CochainComplex.shiftedTwoSlicePointIsoNegOne K q).inv =
              (q + 1).negOnePow •
                ((asIso (HomologicalComplex.opcyclesMap ι q)).inv ≫
                  ((K.truncLE (q + 1)).truncGEXIsoOpcycles q).inv ≫
                  ((CochainComplex.adjacentTwoSlice K q).shiftFunctorObjXIso
                    (q + 1) (-1) q (by omega)).inv) := by
          dsimp only [ι]
          dsimp only [CochainComplex.shiftedTwoSlicePointIsoNegOne]
          simp only [Iso.trans_inv, Preadditive.smul_iso_inv,
            Int.units_inv_eq_self, Category.assoc,
            Linear.comp_units_smul]
          rw [smul_left_cancel_iff]
          simp
          slice_lhs 2 3 =>
            erw [Category.id_comp]
          simp only [Category.assoc]
          rw [IsIso.hom_inv_id_assoc]
        rw [reassoc_of% hpoint]
        simp only [Linear.comp_units_smul, Linear.units_smul_comp,
          Category.assoc]
        rw [smul_left_cancel_iff]
        let T := K.truncLE (q + 1)
        let L := CochainComplex.adjacentTwoSlice K q
        let π := T.πTruncGE q
        let _ : QuasiIsoAt π q :=
          CochainComplex.quasiIsoAt_πTruncGE T q q (by omega)
        have hπOp :
            HomologicalComplex.opcyclesMap π q =
              (T.truncGEXIsoOpcycles q).inv ≫ L.pOpcycles q := by
          dsimp only [π, L]
          rw [← cancel_epi (T.pOpcycles q)]
          rw [HomologicalComplex.p_opcyclesMap]
          rw [← CochainComplex.πTruncGE_f_boundary T q]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          rfl
        have hπShift :
            HomologicalComplex.opcyclesMap π q ≫
                ShortComplex.opcyclesMap
                  ((CochainComplex.shiftShortComplexFunctorIso C
                    (q + 1) (-1) q hShift).inv.app L) =
              (T.truncGEXIsoOpcycles q).inv ≫
                (L.shiftFunctorObjXIso
                  (q + 1) (-1) q (by omega)).inv ≫
                (CochainComplex.shiftedAdjacentTwoSlice K q).pOpcycles (-1) := by
          rw [hπOp]
          have hshiftOp :
              L.pOpcycles q ≫
                  ShortComplex.opcyclesMap
                    ((CochainComplex.shiftShortComplexFunctorIso C
                      (q + 1) (-1) q hShift).inv.app L) =
                ((CochainComplex.shiftShortComplexFunctorIso C
                    (q + 1) (-1) q hShift).inv.app L).τ₂ ≫
                  (CochainComplex.shiftedAdjacentTwoSlice K q).pOpcycles (-1) := by
            change ShortComplex.pOpcycles _ ≫
                ShortComplex.opcyclesMap _ = _ ≫ ShortComplex.pOpcycles _
            exact ShortComplex.p_opcyclesMap _
          have htargetτ :
              ((CochainComplex.shiftShortComplexFunctorIso C
                (q + 1) (-1) q hShift).inv.app L).τ₂ =
                (L.shiftFunctorObjXIso
                  (q + 1) (-1) q (by omega)).inv := by
            simp only [CochainComplex.shiftShortComplexFunctorIso_inv_app_τ₂]
            rfl
          calc
            _ = (T.truncGEXIsoOpcycles q).inv ≫
                (((CochainComplex.shiftShortComplexFunctorIso C
                    (q + 1) (-1) q hShift).inv.app L).τ₂ ≫
                  (CochainComplex.shiftedAdjacentTwoSlice K q).pOpcycles (-1)) := by
              simpa only [Category.assoc] using congrArg
                (fun z ↦ (T.truncGEXIsoOpcycles q).inv ≫ z) hshiftOp
            _ = _ := by
              rw [htargetτ]
        have hιnat := HomologicalComplex.homologyι_naturality
          (i := q) (φ := ι)
        have hιhom :
            (isoOfQuasiIsoAt ι q).hom =
              HomologicalComplex.homologyMap ι q := rfl
        have hιroute :
            (isoOfQuasiIsoAt ι q).inv ≫ T.homologyι q =
              K.homologyι q ≫
                (asIso (HomologicalComplex.opcyclesMap ι q)).inv := by
          rw [← cancel_epi (isoOfQuasiIsoAt ι q).hom]
          simp only [Iso.hom_inv_id_assoc]
          rw [hιhom]
          rw [reassoc_of% hιnat]
          simp
          rfl
        have hπnat :
            HomologicalComplex.homologyMap π q ≫ L.homologyι q =
              T.homologyι q ≫
                HomologicalComplex.opcyclesMap π q := by
          change HomologicalComplex.homologyMap π q ≫
              (T.truncGE q).homologyι q =
            T.homologyι q ≫ HomologicalComplex.opcyclesMap π q
          exact HomologicalComplex.homologyι_naturality
            (i := q) (φ := π)
        have hπhom :
            (isoOfQuasiIsoAt π q).hom =
              HomologicalComplex.homologyMap π q := rfl
        have hchild :
            (child_adjacentTwoSliceLowerHomologyIso K q).hom =
              (isoOfQuasiIsoAt ι q).inv ≫
                (isoOfQuasiIsoAt π q).hom := by
          dsimp [child_adjacentTwoSliceLowerHomologyIso, ι, π, T]
        rw [hchild, hπhom]
        simp only [Category.assoc]
        rw [reassoc_of% hπnat]
        dsimp only [L, T] at hπShift
        rw [hπShift]
        rw [reassoc_of% hιroute]
  simpa only [Category.assoc] using congrArg
    (fun z ↦
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) 0 (homologyTwoStepResolutionInt K q).F).hom ≫ z)
    hcomponents

set_option backward.isDefEq.respectTransparency false in
private lemma child_mappingCone_lower_derived_homology
    (K : CochainComplex C ℤ) (q : ℤ) :
    let R := homologyTwoStepResolutionInt K q
    let L := CochainComplex.adjacentTwoSlice K q
    (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) 0 R.F).inv ≫
      (CochainComplex.ShiftSequence.shiftIso C
          1 (-1) 0 (by omega)).inv.app
            ((CochainComplex.singleFunctor C 0).obj R.F) ≫
      (DerivedCategory.homologyFunctorFactors C (-1)).inv.app
        (((CochainComplex.singleFunctor C 0).obj R.F)⟦(1 : ℤ)⟧) ≫
      (DerivedCategory.homologyFunctor C (-1)).map
        (DerivedCategory.Q.map
          (mappingConeLowerInclusion R ≫
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)) ≫
      (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
        (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
      (CochainComplex.ShiftSequence.shiftIso C
          (q + 1) (-1) q (by omega)).hom.app L =
      (q + 1).negOnePow •
        (child_adjacentTwoSliceLowerHomologyIso K q).hom := by
  dsimp only
  let a := mappingConeLowerInclusion (homologyTwoStepResolutionInt K q) ≫
    (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv
  have hfac :=
    (DerivedCategory.homologyFunctorFactors C (-1)).inv.naturality a
  erw [Functor.comp_map] at hfac
  rw [← reassoc_of% hfac]
  simp only [Iso.inv_hom_id_app_assoc]
  exact child_mappingCone_lower_homology K q

set_option backward.isDefEq.respectTransparency false in
private lemma child_single_shift_source_normalization (A : C) :
    let S := (CochainComplex.singleFunctor C 0).obj A
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          1 (-1) 0 (by omega)).inv.app
            ((DerivedCategory.singleFunctor C 0).obj A) ≫
        (DerivedCategory.homologyFunctor C (-1)).map
          ((DerivedCategory.Q.commShiftIso 1).inv.app S) =
      (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) 0 A).inv ≫
        (CochainComplex.ShiftSequence.shiftIso C
          1 (-1) 0 (by omega)).inv.app S ≫
        (DerivedCategory.homologyFunctorFactors C (-1)).inv.app (S⟦1⟧) := by
  dsimp only
  let S := (CochainComplex.singleFunctor C 0).obj A
  have hshift := child_homology_shiftIso_hom_comp_factors
    (C := C) 1 (-1) 0 (by omega) S
  dsimp only [S] at hshift ⊢
  rw [← cancel_mono
    ((DerivedCategory.homologyFunctorFactors C (-1)).hom.app (S⟦1⟧) ≫
      (CochainComplex.ShiftSequence.shiftIso C
        1 (-1) 0 (by omega)).hom.app S)]
  simp only [Category.assoc]
  slice_lhs 3 5 =>
    erw [← hshift]
  slice_lhs 2 3 =>
    erw [Iso.inv_hom_id_app]
  erw [Category.id_comp]
  rw [singleFunctorCompHomologyFunctorIso_inv_comp_homologyFunctorFactors_hom]
  slice_rhs 3 4 =>
    rw [Iso.inv_hom_id_app]
  slice_rhs 3 4 =>
    erw [Category.id_comp]
  slice_rhs 2 3 =>
    erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact rfl

set_option backward.isDefEq.respectTransparency false in
private lemma child_physical_lower_route_homology
    (K : CochainComplex C ℤ) (q : ℤ) :
    let R := homologyTwoStepResolutionInt K q
    let L := CochainComplex.adjacentTwoSlice K q
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).inv.app R.F ≫
      (DerivedCategory.homologyFunctor C (-1)).map
        (((DerivedCategory.singleFunctors C).shiftIso
          1 (-1) 0 (by omega)).inv.app R.F) ≫
      (DerivedCategory.homologyFunctor C (-1)).map
        ((DerivedCategory.Q.commShiftIso 1).inv.app
          ((CochainComplex.singleFunctor C 0).obj R.F)) ≫
      (DerivedCategory.homologyFunctor C (-1)).map
        (DerivedCategory.Q.map
          (mappingConeLowerInclusion R ≫
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)) ≫
      (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
        (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
      (CochainComplex.ShiftSequence.shiftIso C
        (q + 1) (-1) q (by omega)).hom.app L =
      (q + 1).negOnePow •
        (child_adjacentTwoSliceLowerHomologyIso K q).hom := by
  dsimp only
  slice_lhs 1 2 =>
    rw [child_singleFunctorCompHomologyFunctorIso_shiftIso_one_negOne_inv]
  slice_lhs 1 3 =>
    rw [child_single_shift_source_normalization]
  simpa only [Category.assoc] using
    child_mappingCone_lower_derived_homology K q

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma child_concrete_lower_route_to_middle
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₁ ≫
        (DerivedCategory.Q.commShiftIso 1).inv.app
          ((CochainComplex.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K q).F) ≫
        DerivedCategory.Q.map
          (mappingConeLowerInclusion
            (homologyTwoStepResolutionInt K q)) ≫
        DerivedCategory.Q.map
          (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv =
      ((DerivedCategory.TStructure.t.triangleLTGE 0).obj
        (DerivedCategory.Q.obj
          (CochainComplex.shiftedAdjacentTwoSlice K q))).mor₁ := by
  calc
    _ = (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₁ ≫
        (spliceTriangle (homologyTwoStepResolutionInt K q)).mor₁ ≫
        (compositeTriangleIsoMappingCone
          (homologyTwoStepResolutionInt K q)).hom.hom₃ ≫
        DerivedCategory.Q.map
          (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv := by
            simpa only [Category.assoc] using congrArg
              (fun z ↦
                (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₁ ≫ z ≫
                  DerivedCategory.Q.map
                    (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)
              (spliceTriangle_mor₁_mappingCone
                (homologyTwoStepResolutionInt K q)).symm
    _ = _ := by
      rw [← (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.comm₁_assoc]
      rw [shiftedAdjacentTwoSliceTriangleIsoSplice_hom_hom₂]
      dsimp only [spliceObjTwoIsoShiftedAdjacentTwoSlice]
      simp

set_option backward.isDefEq.respectTransparency false in
private lemma child_splice_lower_endpoint_postcompose_route
    (K : CochainComplex C ℤ) (q : ℤ) :
    let R := homologyTwoStepResolutionInt K q
    let L := CochainComplex.adjacentTwoSlice K q
    (DerivedCategory.homologyFunctor C (-1)).map
          (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₁ ≫
      (DerivedCategory.homologyFunctor C (-1)).map
          (spliceTriangleObj₁Iso R).hom ≫
      (DerivedCategory.homologyFunctor C (-1)).map
          (((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).hom.app R.F) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app R.F ≫
      ((q + 1).negOnePow •
        (child_adjacentTwoSliceLowerHomologyIso K q).hom) =
      (DerivedCategory.homologyFunctor C (-1)).map
          (((DerivedCategory.TStructure.t.triangleLTGE 0).obj
            (DerivedCategory.Q.obj
              (CochainComplex.shiftedAdjacentTwoSlice K q))).mor₁) ≫
        (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
          (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
        (CochainComplex.ShiftSequence.shiftIso C
          (q + 1) (-1) q (by omega)).hom.app L := by
  dsimp only
  rw [← child_physical_lower_route_homology K q]
  slice_lhs 4 5 =>
    rw [Iso.hom_inv_id_app]
  slice_lhs 4 5 =>
    erw [Category.id_comp]
  slice_lhs 3 4 =>
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id]
  slice_lhs 3 4 =>
    erw [Category.id_comp]
  dsimp only [spliceTriangleObj₁Iso]
  slice_lhs 2 3 =>
    rw [Iso.refl_hom]
    erw [Functor.map_id]
    erw [Category.id_comp]
  rw [DerivedCategory.Q.map_comp, Functor.map_comp]
  have hroute := congrArg
    (fun z ↦ (DerivedCategory.homologyFunctor C (-1)).map z)
    (child_concrete_lower_route_to_middle K q)
  simp only [Functor.map_comp] at hroute
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫
      (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
        (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
      (CochainComplex.ShiftSequence.shiftIso C
        (q + 1) (-1) q (by omega)).hom.app
          (CochainComplex.adjacentTwoSlice K q)) hroute

set_option backward.isDefEq.respectTransparency false in
private lemma child_unshifted_lower_endpoint_postcompose_route
    (K : CochainComplex C ℤ) (q : ℤ) :
    let T :=
      (DerivedCategory.TStructure.t.triangleω₁δ
        (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
        (by simp) (by simp)).obj (DerivedCategory.Q.obj K)
    (DerivedCategory.homologyFunctor C q).map
          (DerivedCategory.postnikovSliceIso
            (DerivedCategory.Q.obj K) q).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app
          ((DerivedCategory.homologyFunctor C q).obj
            (DerivedCategory.Q.obj K)) ≫
      (DerivedCategory.homologyFunctorFactors C q).hom.app K ≫
      (child_adjacentTwoSliceLowerHomologyIso K q).hom =
      (DerivedCategory.homologyFunctor C q).map T.mor₁ ≫
        (DerivedCategory.homologyFunctor C q).map
          (DerivedCategory.postnikovTwoSliceIso K q).hom ≫
        (DerivedCategory.homologyFunctorFactors C q).hom.app
          (CochainComplex.adjacentTwoSlice K q) := by
  dsimp only
  rw [← child_unshifted_lower_route_homology K q]
  slice_lhs 3 4 =>
    rw [Iso.hom_inv_id_app]
  slice_lhs 3 4 =>
    erw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [Iso.hom_inv_id_app]
  slice_lhs 2 3 =>
    erw [Category.id_comp]
  slice_lhs 1 2 =>
    rw [← Functor.map_comp, Iso.hom_inv_id]
    erw [Functor.map_id]
  slice_lhs 1 2 =>
    erw [Category.id_comp]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma child_shifted_lower_endpoint_postcompose_route
    (K : CochainComplex C ℤ) (q : ℤ) :
    let L := CochainComplex.adjacentTwoSlice K q
    (DerivedCategory.homologyFunctor C (-1)).map
          (DerivedCategory.shiftedPostnikovLowerEndpointIso K q).hom ≫
      (DerivedCategory.homologyFunctor C (-1)).map
          ((DerivedCategory.singleFunctor C (-1)).map
            ((DerivedCategory.homologyFunctorFactors C q).hom.app K)) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app
          ((HomologicalComplex.homologyFunctor C
            (ComplexShape.up ℤ) q).obj K) ≫
      ((q + 1).negOnePow •
        (child_adjacentTwoSliceLowerHomologyIso K q).hom) =
      (DerivedCategory.homologyFunctor C (-1)).map
          (DerivedCategory.shiftedPostnikovAdjacentTriangle K q).mor₁ ≫
        (DerivedCategory.homologyFunctor C (-1)).map
          (DerivedCategory.shiftedPostnikovTwoSliceIso K q).hom ≫
        (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
          (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
        (CochainComplex.ShiftSequence.shiftIso C
          (q + 1) (-1) q (by omega)).hom.app L := by
  dsimp only
  dsimp only [DerivedCategory.shiftedPostnikovLowerEndpointIso,
    DerivedCategory.shiftedPostnikovTwoSliceIso,
    DerivedCategory.shiftedPostnikovAdjacentTriangle]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  let T :=
    (DerivedCategory.TStructure.t.triangleω₁δ
      (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
      (by simp) (by simp)).obj (DerivedCategory.Q.obj K)
  have hmor₁ :
      ((Triangle.shiftFunctor (DerivedCategory C) (q + 1)).obj T).mor₁ =
        (q + 1).negOnePow • T.mor₁⟦q + 1⟧' := by
    rfl
  rw [hmor₁, Functor.map_units_smul]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  rw [smul_left_cancel_iff]
  let A := (DerivedCategory.Q ⋙
    DerivedCategory.homologyFunctor C q).obj K
  have hfac :
      (DerivedCategory.homologyFunctor C (-1)).map
          ((DerivedCategory.singleFunctor C (-1)).map
            ((DerivedCategory.homologyFunctorFactors C q).hom.app K)) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app
          ((HomologicalComplex.homologyFunctor C
            (ComplexShape.up ℤ) q).obj K) =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C q).hom.app K := by
    simpa only [Functor.comp_map, Functor.id_map] using
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.naturality
        ((DerivedCategory.homologyFunctorFactors C q).hom.app K)
  slice_lhs 3 4 =>
    erw [hfac]
  have hsingle :=
    DerivedCategory.singleFunctorCompHomologyFunctorIso_shiftIso_hom_of_indices
      A (q + 1) (-1) q (by omega)
  slice_lhs 2 3 =>
    erw [hsingle]
  let dshift := (DerivedCategory.homologyFunctor C 0).shiftIso
    (q + 1) (-1) q (by omega)
  have hnatSlice := dshift.hom.naturality
    (DerivedCategory.postnikovSliceIso (DerivedCategory.Q.obj K) q).hom
  have hnatSlice' := hnatSlice
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnatSlice'
  slice_lhs 1 2 =>
    erw [hnatSlice']
  let L := CochainComplex.adjacentTwoSlice K q
  have htarget := child_homology_shiftIso_hom_comp_factors
    (C := C) (q + 1) (-1) q (by omega) L
  slice_rhs 3 5 =>
    erw [← htarget]
  have hnatPost := dshift.hom.naturality
    (DerivedCategory.postnikovTwoSliceIso K q).hom
  have hnatPost' := hnatPost
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnatPost'
  slice_rhs 2 3 =>
    erw [hnatPost']
  have hnatMor := dshift.hom.naturality T.mor₁
  have hnatMor' := hnatMor
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnatMor'
  slice_rhs 1 2 =>
    erw [hnatMor']
  slice_lhs 2 5 =>
    erw [child_unshifted_lower_endpoint_postcompose_route K q]
  set_option backward.isDefEq.respectTransparency true in
    have hprefix :
        dshift.hom.app
            ((DerivedCategory.TStructure.t.truncGE q).obj
              ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj
                (DerivedCategory.Q.obj K))) =
          dshift.hom.app T.obj₁ := by
      rfl
    rw [hprefix]
    symm
    exact child_assoc_four
      (dshift.hom.app T.obj₁)
      ((DerivedCategory.homologyFunctor C q).map T.mor₁)
      ((DerivedCategory.homologyFunctor C q).map
        (DerivedCategory.postnikovTwoSliceIso K q).hom)
      ((DerivedCategory.homologyFunctorFactors C q).hom.app L)

set_option backward.isDefEq.respectTransparency false in
private lemma child_postnikov_lower_endpoint_postcompose_route
    (K : CochainComplex C ℤ) (q : ℤ) :
    let R := homologyTwoStepResolutionInt K q
    let L := CochainComplex.adjacentTwoSlice K q
    (DerivedCategory.homologyFunctor C (-1)).map
          (DerivedCategory.concreteLowerEndpointPostnikovIso K q).hom ≫
      (DerivedCategory.homologyFunctor C (-1)).map
          ((DerivedCategory.singleFunctor C (-1)).map
            ((DerivedCategory.homologyFunctorFactors C q).hom.app K)) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app R.F ≫
      ((q + 1).negOnePow •
        (child_adjacentTwoSliceLowerHomologyIso K q).hom) =
      (DerivedCategory.homologyFunctor C (-1)).map
          (((DerivedCategory.TStructure.t.triangleLTGE 0).obj
            (DerivedCategory.Q.obj
              (CochainComplex.shiftedAdjacentTwoSlice K q))).mor₁) ≫
        (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
          (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
      (CochainComplex.ShiftSequence.shiftIso C
          (q + 1) (-1) q (by omega)).hom.app L := by
  dsimp only
  dsimp only [DerivedCategory.concreteLowerEndpointPostnikovIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp]
  slice_lhs 2 5 =>
    erw [child_shifted_lower_endpoint_postcompose_route K q]
  let e := DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete K q
  have he₂ : e.hom.hom₂ =
      (DerivedCategory.shiftedPostnikovTwoSliceIso K q).hom :=
    DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₂ K q
  have hbridge :
      (Triangle.π₁.mapIso e).inv ≫
          (DerivedCategory.shiftedPostnikovAdjacentTriangle K q).mor₁ ≫
          (DerivedCategory.shiftedPostnikovTwoSliceIso K q).hom =
        ((DerivedCategory.TStructure.t.triangleLTGE 0).obj
          (DerivedCategory.Q.obj
            (CochainComplex.shiftedAdjacentTwoSlice K q))).mor₁ := by
    change e.inv.hom₁ ≫
        (DerivedCategory.shiftedPostnikovAdjacentTriangle K q).mor₁ ≫ _ = _
    rw [← he₂]
    rw [e.hom.comm₁]
    rw [e.inv_hom_id_triangle_hom₁_assoc]
  have hbridgeMap := congrArg
    (fun z ↦ (DerivedCategory.homologyFunctor C (-1)).map z) hbridge
  simp only [Functor.map_comp] at hbridgeMap
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫
      (DerivedCategory.homologyFunctorFactors C (-1)).hom.app
        (CochainComplex.shiftedAdjacentTwoSlice K q) ≫
      (CochainComplex.ShiftSequence.shiftIso C
        (q + 1) (-1) q (by omega)).hom.app
          (CochainComplex.adjacentTwoSlice K q)) hbridgeMap

set_option backward.isDefEq.respectTransparency false in
private lemma child_concrete_lower_endpoint_homology
    (K : CochainComplex C ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor C (-1)).map
          (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₁ ≫
      (DerivedCategory.homologyFunctor C (-1)).map
          (spliceTriangleObj₁Iso
            (homologyTwoStepResolutionInt K q)).hom ≫
      (DerivedCategory.homologyFunctor C (-1)).map
          (((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).hom.app
              (homologyTwoStepResolutionInt K q).F) =
      (DerivedCategory.homologyFunctor C (-1)).map
          (DerivedCategory.concreteLowerEndpointPostnikovIso K q).hom ≫
        (DerivedCategory.homologyFunctor C (-1)).map
          ((DerivedCategory.singleFunctor C (-1)).map
            ((DerivedCategory.homologyFunctorFactors C q).hom.app K)) := by
  let R := homologyTwoStepResolutionInt K q
  rw [← cancel_mono
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C (-1)).hom.app R.F ≫
      ((q + 1).negOnePow •
        (child_adjacentTwoSliceLowerHomologyIso K q).hom))]
  simp only [Category.assoc]
  rw [child_splice_lower_endpoint_postcompose_route K q,
    child_postnikov_lower_endpoint_postcompose_route K q]

set_option backward.isDefEq.respectTransparency false in
/-- The first component of the actual-to-splice triangle comparison agrees with the normalized
lower Postnikov endpoint. The parity scalar introduced by shifting occurs in both the physical
mapping-cone route and the canonical Postnikov route, and therefore cancels. -/
lemma shiftedPostnikovAdjacentTriangleIsoSplice_hom_hom₁_lower
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangleIsoSplice K q).hom.hom₁ ≫
        (spliceTriangleObj₁Iso (homologyTwoStepResolutionInt K q)).hom ≫
        ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by omega)).hom.app
          (homologyTwoStepResolutionInt K q).F =
      (DerivedCategory.shiftedPostnikovLowerEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctor C (-1)).map
          ((DerivedCategory.homologyFunctorFactors C q).hom.app K) := by
  let _ : DerivedCategory.TStructure.t.IsGE
      (DerivedCategory.shiftedPostnikovAdjacentTriangle K q).obj₁ (-1) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (DerivedCategory.shiftedPostnikovLowerEndpointIso K q).symm (-1)
  let _ : DerivedCategory.TStructure.t.IsLE
      (DerivedCategory.shiftedPostnikovAdjacentTriangle K q).obj₁ (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.shiftedPostnikovLowerEndpointIso K q).symm (-1)
  apply DerivedCategory.homologyFunctor_map_injective_of_isGE_of_isLE _ _ (-1)
  simp only [Functor.map_comp]
  dsimp only [shiftedPostnikovAdjacentTriangleIsoSplice]
  simp only [Iso.trans_hom, comp_hom₁, Functor.map_comp, Category.assoc]
  rw [child_concrete_lower_endpoint_homology K q]
  rw [← Functor.map_comp_assoc]
  rw [DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₁_postnikov]

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
