/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovUpperRouteHomology
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovUpperEndpointConcreteNormalization

/-!
# Normalization of the concrete upper Postnikov endpoint

This file compares the upper edge of the shifted adjacent Postnikov triangle with the standard
mapping-cone model. The sole scalar is the explicit parity scalar introduced by shifting the
triangle; all endpoint and homology comparisons are normalized without an additional sign.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The standard mapping-cone upper edge, transported to the normalized concrete upper
Postnikov endpoint, is the canonical homology quotient multiplied by the parity scalar of the
triangle shift. The underlying concrete mapping-cone calculation itself is unsigned. -/
lemma mappingConeCompositeTriangle_mor₂_comp_concreteUpperEndpoint (K : CochainComplex C ℤ) (q : ℤ) :
    (mappingConeCompositeTriangle (homologyTwoStepResolutionInt K q)).mor₂ ≫
        (DerivedCategory.Q.mapIso
          (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q)).inv ≫
        (DerivedCategory.TStructure.t.truncGEπ 0).app
          (DerivedCategory.Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q)) ≫
        (DerivedCategory.concreteUpperEndpointPostnikovIso K q).hom ≫
        (DerivedCategory.singleFunctor C 0).map
          ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K) =
      (q + 1).negOnePow •
        (DerivedCategory.singleFunctor C 0).map
          (homologyTwoStepResolutionInt K q).complex.g := by
  dsimp only [DerivedCategory.concreteUpperEndpointPostnikovIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  let e := DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete K q
  have he₂ : e.inv.hom₂ = (DerivedCategory.shiftedPostnikovTwoSliceIso K q).inv := by
    rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id,
      DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₂]
    simp
  simp only [Functor.mapIso_inv]
  have hc :
      (DerivedCategory.TStructure.t.truncGEπ 0).app
            (DerivedCategory.Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q)) ≫
          (Triangle.π₃.map e.inv ≫
            (DerivedCategory.shiftedPostnikovUpperEndpointIso K q).hom) ≫
          (DerivedCategory.singleFunctor C 0).map
            ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K) =
        e.inv.hom₂ ≫
          (DerivedCategory.shiftedPostnikovAdjacentTriangle K q).mor₂ ≫
          (DerivedCategory.shiftedPostnikovUpperEndpointIso K q).hom ≫
          (DerivedCategory.singleFunctor C 0).map
            ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K) := by
    rw [← DerivedCategory.TStructure.t.triangleLTGE_obj_mor₂]
    rw [Triangle.π₃_map]
    simpa only [Category.assoc] using e.inv.comm₂_assoc
      ((DerivedCategory.shiftedPostnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctor C 0).map
          ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K))
  rw [hc, he₂]
  dsimp only [DerivedCategory.shiftedPostnikovTwoSliceIso,
    DerivedCategory.shiftedPostnikovAdjacentTriangle,
    DerivedCategory.shiftedPostnikovUpperEndpointIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Category.assoc]
  have hmor₂ :
      ((Triangle.shiftFunctor (DerivedCategory C) (q + 1)).obj
        ((DerivedCategory.TStructure.t.triangleω₁δ
          (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
          (by simp) (by simp)).obj (DerivedCategory.Q.obj K))).mor₂ =
        (q + 1).negOnePow •
          (((DerivedCategory.TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₂)⟦q + 1⟧' := by
    rfl
  rw [hmor₂]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  rw [smul_left_cancel_iff]
  let u := DerivedCategory.triangleω₁δIsoAdjacentTwoSliceTriangle K q
  have hu₂ : u.inv.hom₂ = (DerivedCategory.postnikovTwoSliceIso K q).inv := by
    rw [← cancel_mono u.hom.hom₂, ← comp_hom₂, u.inv_hom_id,
      DerivedCategory.triangleω₁δIsoAdjacentTwoSliceTriangle_hom_hom₂]
    simp
  have hu₀ :
      (DerivedCategory.postnikovTwoSliceIso K q).inv ≫
          ((DerivedCategory.TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₂ ≫
          (DerivedCategory.postnikovUpperEndpointIso K q).hom =
        ((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
          (DerivedCategory.Q.obj
            (CochainComplex.adjacentTwoSlice K q))).mor₂ ≫
          u.inv.hom₃ ≫
          (DerivedCategory.postnikovUpperEndpointIso K q).hom := by
    rw [← hu₂]
    exact (u.inv.comm₂_assoc
      (DerivedCategory.postnikovUpperEndpointIso K q).hom).symm
  have hu := congrArg
    (fun z ↦ (shiftFunctor (DerivedCategory C) (q + 1)).map z) hu₀
  simp only [Functor.map_comp] at hu
  rw [reassoc_of% hu]
  apply DerivedCategory.homologyFunctor_map_injective_singleFunctor
  simp only [Functor.map_comp]
  let R := homologyTwoStepResolutionInt K q
  rw [← cancel_epi
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app R.complex.X₂)]
  rw [← cancel_mono
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app R.complex.X₃)]
  simp only [Category.assoc]
  have hg :
      (DerivedCategory.homologyFunctor C 0).map
          ((DerivedCategory.singleFunctor C 0).map R.complex.g) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app
            R.complex.X₃ =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app
            R.complex.X₂ ≫ R.complex.g := by
    simpa only [Functor.comp_map, Functor.id_map] using
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality
        R.complex.g
  rw [hg]
  simp only [Iso.inv_hom_id_app_assoc]
  have hfac :
      (DerivedCategory.homologyFunctor C 0).map
          ((DerivedCategory.singleFunctor C 0).map
            ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K)) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app
            ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).obj K) =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app
            ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C (q + 1)).obj K) ≫
          (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    simpa only [Functor.comp_map, Functor.id_map] using
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality
        ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K)
  erw [hfac]
  let A := (DerivedCategory.Q ⋙
    DerivedCategory.homologyFunctor C (q + 1)).obj K
  have hsingleShift :
      (DerivedCategory.homologyFunctor C 0).map
          (((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) 0 (q + 1) (by omega)).hom.app A) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app A =
        ((DerivedCategory.homologyFunctor C 0).shiftIso
            (q + 1) 0 (q + 1) (by omega)).hom.app
              ((DerivedCategory.singleFunctor C (q + 1)).obj A) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A := by
    exact DerivedCategory.singleFunctorCompHomologyFunctorIso_shiftIso_hom A (q + 1)
  have hsingleShift' :
      (DerivedCategory.homologyFunctor C 0).map
          ((((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) 0 (q + 1) (by omega)).app A).hom) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app A =
        ((DerivedCategory.homologyFunctor C 0).shiftIso
            (q + 1) 0 (q + 1) (by omega)).hom.app
              ((DerivedCategory.singleFunctor C (q + 1)).obj A) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A := by
    exact hsingleShift
  have hsuffix :
      (DerivedCategory.homologyFunctor C 0).map
          ((((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) 0 (q + 1) (by omega)).app
              ((DerivedCategory.homologyFunctor C (q + 1)).obj
                (DerivedCategory.Q.obj K))).hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app
            ((DerivedCategory.Q ⋙
              DerivedCategory.homologyFunctor C (q + 1)).obj K) ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            ((DerivedCategory.singleFunctor C (q + 1)).obj A) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    change
      (DerivedCategory.homologyFunctor C 0).map
          ((((DerivedCategory.singleFunctors C).shiftIso
            (q + 1) 0 (q + 1) (by omega)).app A).hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K = _
    rw [reassoc_of% hsingleShift']
  erw [hsuffix]
  have hnatUpper :=
    ((DerivedCategory.homologyFunctor C 0).shiftIso
      (q + 1) 0 (q + 1) (by omega)).hom.naturality
        (DerivedCategory.postnikovUpperEndpointIso K q).hom
  have hnatUpper' := hnatUpper
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnatUpper'
  have hupperSuffix :
      (DerivedCategory.homologyFunctor C 0).map
          ((shiftFunctor (DerivedCategory C) (q + 1)).map
            (DerivedCategory.postnikovUpperEndpointIso K q).hom) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            ((DerivedCategory.singleFunctor C (q + 1)).obj A) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (((DerivedCategory.TStructure.t.triangleω₁δ
              (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
              (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).obj₃) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    change
      (DerivedCategory.homologyFunctor C 0).map
          ((shiftFunctor (DerivedCategory C) (q + 1)).map
            (DerivedCategory.postnikovUpperEndpointIso K q).hom) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            ((DerivedCategory.singleFunctor C (q + 1)).obj
              ((DerivedCategory.homologyFunctor C (q + 1)).obj
                (DerivedCategory.Q.obj K))) ≫ _ = _
    rw [reassoc_of% hnatUpper']
  erw [hupperSuffix]
  have hnatU :=
    ((DerivedCategory.homologyFunctor C 0).shiftIso
      (q + 1) 0 (q + 1) (by omega)).hom.naturality u.inv.hom₃
  have hnatU' := hnatU
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnatU'
  have huSuffix :
      (DerivedCategory.homologyFunctor C 0).map
          ((shiftFunctor (DerivedCategory C) (q + 1)).map u.inv.hom₃) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (((DerivedCategory.TStructure.t.triangleω₁δ
              (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
              (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).obj₃) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj
                (CochainComplex.adjacentTwoSlice K q))).obj₃) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    rw [reassoc_of% hnatU']
  erw [huSuffix]
  have hnatTrunc :=
    ((DerivedCategory.homologyFunctor C 0).shiftIso
      (q + 1) 0 (q + 1) (by omega)).hom.naturality
        (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
          (DerivedCategory.Q.obj
            (CochainComplex.adjacentTwoSlice K q))).mor₂)
  have hnatTrunc' := hnatTrunc
  simp only [Functor.comp_map, DerivedCategory.shift_homologyFunctor] at hnatTrunc'
  have htruncSuffix :
      (DerivedCategory.homologyFunctor C 0).map
          ((shiftFunctor (DerivedCategory C) (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj
                (CochainComplex.adjacentTwoSlice K q))).mor₂)) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj
                (CochainComplex.adjacentTwoSlice K q))).obj₃) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj
                (CochainComplex.adjacentTwoSlice K q))).obj₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj
                (CochainComplex.adjacentTwoSlice K q))).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    rw [reassoc_of% hnatTrunc']
  erw [htruncSuffix]
  let L := CochainComplex.adjacentTwoSlice K q
  have hshift := DerivedCategory.shiftMap_homologyFunctor_map_Q
    (C := C) (K := L⟦q + 1⟧) (L := L) (𝟙 (L⟦q + 1⟧)) 0 (q + 1) (by omega)
  dsimp [Functor.shiftMap, ShiftedHom.map] at hshift
  rw [DerivedCategory.Q.map_id] at hshift
  simp only [Category.id_comp] at hshift
  rw [((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shift 0).map_id]
    at hshift
  simp only [Category.id_comp] at hshift
  have hshift0 :
      (DerivedCategory.homologyFunctor C 0).map
          ((DerivedCategory.Q.commShiftIso (q + 1)).hom.app L) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (DerivedCategory.Q.obj L) =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app (L⟦q + 1⟧) ≫
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app L ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).inv.app L := by
    simpa only [Functor.map_comp, Functor.map_id, Category.id_comp,
      DerivedCategory.shift_homologyFunctor,
      CochainComplex.homologyFunctor_shift] using hshift
  have hcommSuffix :
      (DerivedCategory.homologyFunctor C 0).map
          (((DerivedCategory.Q.commShiftIso (q + 1)).symm.app L).inv) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj L)).obj₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj L)).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app (L⟦q + 1⟧) ≫
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app L ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).inv.app L ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj L)).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    change
      (DerivedCategory.homologyFunctor C 0).map
          ((DerivedCategory.Q.commShiftIso (q + 1)).hom.app L) ≫
        ((DerivedCategory.homologyFunctor C 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app
            (DerivedCategory.Q.obj L) ≫ _ = _
    rw [reassoc_of% hshift0]
  erw [hcommSuffix]
  have hroute := congrArg
    (fun z ↦ (DerivedCategory.homologyFunctor C (q + 1)).map z) hu₀
  simp only [Functor.map_comp] at hroute
  have hpostRouteSuffix :
      (DerivedCategory.homologyFunctor C (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj L)).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovTwoSliceIso K q).inv ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleω₁δ
              (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
              (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app A ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K := by
    change
      (DerivedCategory.homologyFunctor C (q + 1)).map
            (((DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj
              (DerivedCategory.Q.obj
                (CochainComplex.adjacentTwoSlice K q))).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map u.inv.hom₃ ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫ _ = _
    rw [← reassoc_of% hroute]
  erw [hpostRouteSuffix]
  dsimp only [L, A]
  slice_lhs 6 11 =>
    erw [DerivedCategory.postnikovUpperRouteHomology K q]
  exact mappingConeCompositeTriangle_mor₂_upper_homology K q

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The third component of the actual-to-splice triangle comparison is the normalized upper
Postnikov endpoint multiplied by exactly the parity scalar introduced by shifting the triangle.
No additional scalar occurs in the concrete endpoint or homology comparison. -/
lemma shiftedPostnikovAdjacentTriangleIsoSplice_hom_hom₃_upper
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangleIsoSplice K q).hom.hom₃ ≫
        (spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K q)).hom =
      (q + 1).negOnePow •
        ((DerivedCategory.shiftedPostnikovUpperEndpointIso K q).hom ≫
          (DerivedCategory.singleFunctor C 0).map
            ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K)) := by
  have hconcrete :
      (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₃ ≫
          (spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K q)).hom =
        (q + 1).negOnePow •
          ((DerivedCategory.concreteUpperEndpointPostnikovIso K q).hom ≫
            (DerivedCategory.singleFunctor C 0).map
              ((DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K)) := by
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
    change
      ((DerivedCategory.TStructure.t.triangleLTGE 0).obj
          (DerivedCategory.Q.obj (K.shiftedAdjacentTwoSlice q))).mor₂ ≫
          (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₃ ≫
          (spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K q)).hom = _
    rw [(shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.comm₂_assoc]
    rw [shiftedAdjacentTwoSliceTriangleIsoSplice_hom_hom₂]
    change
      (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).inv ≫
          (spliceTriangle (homologyTwoStepResolutionInt K q)).mor₂ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rw [← cancel_epi (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).hom]
    let R := homologyTwoStepResolutionInt K q
    apply (show Function.Injective
        (fun f : (compositeTriangle R).obj₃ ⟶
            (DerivedCategory.singleFunctor C 0).obj R.complex.X₃ ↦
          (compositeTriangle R).mor₂ ≫ f) by
      intro f g h
      rw [← sub_eq_zero]
      have hz : (compositeTriangle R).mor₂ ≫ (f - g) = 0 := by
        change (compositeTriangle R).mor₂ ≫ f =
          (compositeTriangle R).mor₂ ≫ g at h
        rw [Preadditive.comp_sub, h, sub_self]
      obtain ⟨a, ha⟩ := (compositeTriangle R).yoneda_exact₃
        (compositeTriangle_distinguished R) (f - g) hz
      have hle : DerivedCategory.TStructure.t.IsLE
          (compositeTriangle R).obj₁ 0 := by
        change DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.singleFunctor C 0).obj R.complex.X₁) 0
        infer_instance
      have hle' : DerivedCategory.TStructure.t.IsLE
          ((compositeTriangle R).obj₁⟦(1 : ℤ)⟧) (-1) :=
        DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by omega)
      rw [ha, DerivedCategory.TStructure.t.zero a (-1) 0 (by omega), comp_zero])
    dsimp only
    simp only [Iso.hom_inv_id_assoc]
    change (compositeTriangle R).mor₂ ≫ (spliceTriangle R).mor₂ = _
    rw [compositeTriangle_mor₂_comp_spliceTriangle_mor₂]
    have hsplice : (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).hom =
        (compositeTriangleIsoMappingCone R).hom.hom₃ ≫
          DerivedCategory.Q.map
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv := by
      rfl
    rw [hsplice]
    simp only [Category.assoc]
    rw [(compositeTriangleIsoMappingCone R).hom.comm₂_assoc]
    rw [compositeTriangleIsoMappingCone_hom_hom₂]
    simp only [Category.id_comp, Linear.comp_units_smul]
    rw [← smul_left_cancel_iff (q + 1).negOnePow]
    simp only [smul_smul, Int.units_mul_self, one_smul]
    exact (mappingConeCompositeTriangle_mor₂_comp_concreteUpperEndpoint K q).symm
  dsimp only [shiftedPostnikovAdjacentTriangleIsoSplice]
  simp only [Iso.trans_hom, comp_hom₃, Category.assoc]
  rw [hconcrete]
  simp only [Linear.comp_units_smul]
  rw [smul_left_cancel_iff]
  exact
    DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₃_postnikov_assoc
      K q _


end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
