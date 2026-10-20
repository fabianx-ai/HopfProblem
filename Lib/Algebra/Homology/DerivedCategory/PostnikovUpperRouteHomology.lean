/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovTwoSliceEndpoints
public import Lib.Algebra.Homology.DerivedCategory.PostnikovSliceNaturality

/-!
# Homology normalization of the upper adjacent Postnikov route

The upper edge of the unshifted adjacent Postnikov triangle, transported through the normalized
Postnikov-slice comparison, induces the good upper-truncation inclusion on homology. This
calculation is unsigned; the parity scalar occurs only when the triangle itself is shifted.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace DerivedCategory

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

private lemma castIso_hom {D : Type*} [Category D]
    {X Y Z : D} (e : X ≅ Y) (h : Y = Z) :
    (cast (congrArg (fun T : D ↦ X ≅ T) h) e).hom =
      e.hom ≫ eqToHom h := by
  subst Z
  simp

private lemma eqToIso_hom_comp_family
    {D : Type*} [Category D] {A : Type*}
    (X : A → D) (Z : D) (f : ∀ a, X a ⟶ Z)
    {a b : A} (h : a = b) :
    (eqToIso (congrArg X h)).hom ≫ f b = f a := by
  subst b
  simp

/-- Canonical transport between the two arithmetically equal upper truncation cutoffs. -/
noncomputable def postnikovUpperCutoffIso
    (K : CochainComplex C ℤ) (q : ℤ) :
    (DerivedCategory.TStructure.t.truncLT (q + 2)).obj
        (DerivedCategory.Q.obj K) ≅
      (DerivedCategory.TStructure.t.truncLT ((q + 1) + 1)).obj
        (DerivedCategory.Q.obj K) :=
  eqToIso (congrArg
    (fun n : ℤ ↦ (DerivedCategory.TStructure.t.truncLT n).obj
      (DerivedCategory.Q.obj K)) (by omega))

set_option backward.isDefEq.respectTransparency false in
/-- The normalized upper Postnikov endpoint induces the canonical Postnikov-slice homology
isomorphism, up to the definitional cutoff transport. -/
lemma homologyFunctor_map_postnikovUpperEndpointIso_hom
    (K : CochainComplex C ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor C (q + 1)).map
        (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app
        ((DerivedCategory.homologyFunctor C (q + 1)).obj
          (DerivedCategory.Q.obj K)) =
      (DerivedCategory.homologyFunctor C (q + 1)).map
          (((DerivedCategory.TStructure.t.truncGE (q + 1)).mapIso
            (postnikovUpperCutoffIso K q)).hom) ≫
        (DerivedCategory.postnikovSliceHomologyIso
          (DerivedCategory.Q.obj K) (q + 1)).hom := by
  dsimp [DerivedCategory.postnikovUpperEndpointIso]
  simp only [Functor.map_comp, Category.assoc]
  rw [DerivedCategory.homologyFunctor_map_postnikovSliceIso_hom]
  rfl

/-- The good lower-truncation projection identifies upper-degree homology of the upper
truncation with upper-degree homology of the adjacent two-slice. -/
noncomputable def adjacentTwoSliceUpperHomologyIso
    (K : CochainComplex C ℤ) (q : ℤ) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).obj
        (K.truncLE (q + 1)) ≅
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).obj
        (CochainComplex.adjacentTwoSlice K q) := by
  let π := (K.truncLE (q + 1)).πTruncGE q
  letI : QuasiIsoAt π (q + 1) :=
    CochainComplex.quasiIsoAt_πTruncGE (K.truncLE (q + 1)) q (q + 1) (by omega)
  exact isoOfQuasiIsoAt π (q + 1)

set_option backward.isDefEq.respectTransparency false in
/-- The complete unshifted upper Postnikov route induces the good upper-truncation inclusion on
homology. In particular, this route introduces no scalar. -/
lemma postnikovUpperRouteHomology
    (K : CochainComplex C ℤ) (q : ℤ) :
    let L := CochainComplex.adjacentTwoSlice K q
    let ι := K.ιTruncLE (q + 1)
    (DerivedCategory.homologyFunctorFactors C (q + 1)).inv.app L ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovTwoSliceIso K q).inv ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (((DerivedCategory.TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₂) ≫
        (DerivedCategory.homologyFunctor C (q + 1)).map
          (DerivedCategory.postnikovUpperEndpointIso K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (q + 1)).hom.app
          ((DerivedCategory.homologyFunctor C (q + 1)).obj
            (DerivedCategory.Q.obj K)) ≫
        (DerivedCategory.homologyFunctorFactors C (q + 1)).hom.app K =
      (adjacentTwoSliceUpperHomologyIso K q).inv ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).map ι := by
  dsimp only
  let π := (K.truncLE (q + 1)).πTruncGE q
  let _ : QuasiIsoAt π (q + 1) :=
    CochainComplex.quasiIsoAt_πTruncGE (K.truncLE (q + 1)) q (q + 1) (by omega)
  let _ : IsIso
      ((HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) (q + 1)).map π) := by
    change IsIso (HomologicalComplex.homologyMap π (q + 1))
    infer_instance
  rw [← cancel_epi
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).map π)]
  have hπ :
      (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) (q + 1)).map π =
        (adjacentTwoSliceUpperHomologyIso K q).hom := by
    rfl
  rw [hπ, Iso.hom_inv_id_assoc]
  rw [← hπ]
  rw [reassoc_of%
    (DerivedCategory.homologyFunctorFactors C (q + 1)).inv.naturality π]
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
    rw [castIso_hom]
    simp only [Iso.trans_hom, eqToIso.hom, Functor.map_comp,
      Functor.mapIso_hom, eqToHom_map]
    exact hGE
  have hpost :
      (DerivedCategory.postnikovTwoSliceIso K q).hom =
        eGE.hom ≫
          (DerivedCategory.truncGEIsoQTruncGE
            (K.truncLE (q + 1)) q).hom := by
    rfl
  have hQπ :
      DerivedCategory.Q.map π ≫
          (DerivedCategory.postnikovTwoSliceIso K q).inv =
        eLT.inv ≫
          (DerivedCategory.TStructure.t.truncGEπ q).app
            ((DerivedCategory.TStructure.t.truncLT (q + 2)).obj
              (DerivedCategory.Q.obj K)) := by
    rw [← cancel_mono (DerivedCategory.postnikovTwoSliceIso K q).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hpost, heGE]
    rw [reassoc_of% DerivedCategory.TStructure.t.truncGEπ_naturality q eLT.hom]
    simp only [Iso.inv_hom_id_assoc]
    rw [DerivedCategory.truncGEπ_comp_truncGEIsoQTruncGE_hom]
  have hQπmap := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor C (q + 1)).map f) hQπ
  simp only [Functor.map_comp] at hQπmap
  rw [reassoc_of% hQπmap]
  have htri :
      (DerivedCategory.TStructure.t.truncGEπ q).app
            ((DerivedCategory.TStructure.t.truncLT (q + 2)).obj
              (DerivedCategory.Q.obj K)) ≫
          (((DerivedCategory.TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₂) =
        (DerivedCategory.TStructure.t.truncGEπ (q + 1)).app
          ((DerivedCategory.TStructure.t.truncLT (q + 2)).obj
            (DerivedCategory.Q.obj K)) := by
    rw [DerivedCategory.TStructure.t.triangleω₁δ_obj_mor₂]
    exact DerivedCategory.TStructure.t.eTruncGEπ_app_eTruncGE_map_app
      (homOfLE (show (q : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))
      ((DerivedCategory.TStructure.t.truncLT (q + 2)).obj
        (DerivedCategory.Q.obj K))
  have htrimap := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor C (q + 1)).map f) htri
  simp only [Functor.map_comp] at htrimap
  rw [reassoc_of% htrimap]
  rw [reassoc_of%
    homologyFunctor_map_postnikovUpperEndpointIso_hom K q]
  dsimp only [DerivedCategory.postnikovSliceHomologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Functor.mapIso_hom, Category.assoc]
  have hUpper := DerivedCategory.TStructure.t.truncGEπ_naturality
    (q + 1) (postnikovUpperCutoffIso K q).hom
  have hUpperMap := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor C (q + 1)).map f) hUpper
  simp only [Functor.map_comp] at hUpperMap
  rw [reassoc_of% hUpperMap]
  simp only [IsIso.hom_inv_id_assoc]
  have heUpperι :
      (postnikovUpperCutoffIso K q).hom ≫
          (DerivedCategory.TStructure.t.truncLTι ((q + 1) + 1)).app
            (DerivedCategory.Q.obj K) =
        (DerivedCategory.TStructure.t.truncLTι (q + 2)).app
          (DerivedCategory.Q.obj K) := by
    exact eqToIso_hom_comp_family
      (fun n : ℤ ↦ (DerivedCategory.TStructure.t.truncLT n).obj
        (DerivedCategory.Q.obj K)) (DerivedCategory.Q.obj K)
      (fun n : ℤ ↦ (DerivedCategory.TStructure.t.truncLTι n).app
        (DerivedCategory.Q.obj K)) (by omega)
  have heUpperιMap := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor C (q + 1)).map f) heUpperι
  simp only [Functor.map_comp] at heUpperιMap
  rw [reassoc_of% heUpperιMap]
  have hBaseι :
      (eqToIso hBase).hom ≫
          DerivedCategory.Q.map (K.ιTruncLE (q + 1)) =
        DerivedCategory.Q.map (K.ιTruncLE (q + 2 - 1)) := by
    exact eqToIso_hom_comp_family
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
  have heLTinvι :
      eLT.inv ≫
          (DerivedCategory.TStructure.t.truncLTι (q + 2)).app
            (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map (K.ιTruncLE (q + 1)) := by
    rw [← heLTι]
    simp only [Iso.inv_hom_id_assoc]
  have heLTinvιMap := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor C (q + 1)).map f) heLTinvι
  simp only [Functor.map_comp] at heLTinvιMap
  rw [reassoc_of% heLTinvιMap]
  rw [show
    (DerivedCategory.homologyFunctor C (q + 1)).map
        (DerivedCategory.Q.map (K.ιTruncLE (q + 1))) =
      (DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor C (q + 1)).map
          (K.ιTruncLE (q + 1)) by rfl]
  rw [(DerivedCategory.homologyFunctorFactors C (q + 1)).hom.naturality
    (K.ιTruncLE (q + 1))]
  rw [Iso.inv_hom_id_app_assoc]

end DerivedCategory
