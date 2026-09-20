/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.TwoStepSplice
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The lower edge of the two-step splice in mapping-cone coordinates

For a two-step resolution, this file identifies the lower edge selected by the octahedron with
the literal inclusion into the standard mapping cone of the middle arrow.  The chain-level
inclusion includes the sign which cancels the sign built into left-shifting a cocycle; its
composite with the cone projection is consequently the negative shifted coefficient inclusion,
exactly as required by the rotated first short-exact triangle.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated HomologicalComplex

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C]

attribute [local instance] HasDerivedCategory.standard

/-- Auxiliary mapping-cone lift before correcting the left-shift sign. -/
noncomputable def mappingConeLowerLift
    (R : TwoStepResolution (C := C)) :
    (((CochainComplex.singleFunctor C 0).obj R.F)⟦(1 : ℤ)⟧) ⟶
      CochainComplex.mappingCone
        ((CochainComplex.singleFunctor C 0).map R.complex.f) :=
  CochainComplex.mappingCone.lift
    ((CochainComplex.singleFunctor C 0).map R.complex.f)
    ((CochainComplex.HomComplex.Cocycle.ofHom
      ((CochainComplex.singleFunctor C 0).map R.ι)).leftShift 1 1 (by omega))
    0 (by
      simp only [CochainComplex.HomComplex.δ_zero, zero_add,
        CochainComplex.HomComplex.Cocycle.leftShift_coe,
        CochainComplex.HomComplex.Cocycle.ofHom_coe]
      rw [← CochainComplex.HomComplex.Cochain.leftShift_comp_zero_cochain]
      rw [← CochainComplex.HomComplex.Cochain.ofHom_comp]
      rw [← Functor.map_comp, R.zero, Functor.map_zero]
      simp)

/-- The literal inclusion of the first coefficient into the mapping cone of the middle arrow of
a two-step resolution. The negation cancels the sign built into left-shifting a degree-zero
cocycle to degree one. -/
noncomputable def mappingConeLowerInclusion
    (R : TwoStepResolution (C := C)) :
    (((CochainComplex.singleFunctor C 0).obj R.F)⟦(1 : ℤ)⟧) ⟶
      CochainComplex.mappingCone
        ((CochainComplex.singleFunctor C 0).map R.complex.f) :=
  -mappingConeLowerLift R

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
omit [HasDerivedCategory C] in
/-- Composing the literal lift with the connecting map of the mapping-cone triangle gives the
shifted augmentation. -/
lemma mappingConeLowerLift_comp_mor₃
    (R : TwoStepResolution (C := C)) :
    mappingConeLowerLift R ≫
        (CochainComplex.mappingCone.triangle
          ((CochainComplex.singleFunctor C 0).map R.complex.f)).mor₃ =
      ((CochainComplex.singleFunctor C 0).map R.ι)⟦(1 : ℤ)⟧' := by
  ext p
  dsimp [mappingConeLowerLift, CochainComplex.mappingCone.triangle]
  simp only [HomologicalComplex.comp_f, Triangle.mk_mor₃,
    CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe,
    CochainComplex.HomComplex.Cocycle.coe_neg,
    CochainComplex.HomComplex.Cochain.rightShift_neg,
    CochainComplex.HomComplex.Cochain.neg_v,
    CochainComplex.shiftFunctor_obj_X',
    (CochainComplex.mappingCone.fst _).1.rightShift_v
      1 0 (zero_add 1) p p (add_zero p) (p + 1) rfl,
    CochainComplex.shiftFunctor_obj_X,
    CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    Preadditive.comp_neg, Category.assoc,
    CochainComplex.mappingCone.lift_f_fst_v,
    CochainComplex.HomComplex.Cocycle.leftShift_coe,
    CochainComplex.HomComplex.Cocycle.ofHom_coe,
    CochainComplex.HomComplex.Cochain.leftShift_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.shiftFunctor_map_f']
  rw [Category.comp_id,
    CochainComplex.mappingCone.lift_f_fst_v]
  simp [CochainComplex.HomComplex.Cocycle.leftShift_coe,
    CochainComplex.HomComplex.Cocycle.ofHom_coe,
    CochainComplex.HomComplex.Cochain.leftShift_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.shiftFunctorObjXIso]

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] in
/-- Composing the inclusion with the connecting map of the mapping-cone triangle gives minus the
shifted augmentation. -/
lemma mappingConeLowerInclusion_comp_mor₃
    (R : TwoStepResolution (C := C)) :
    mappingConeLowerInclusion R ≫
        (CochainComplex.mappingCone.triangle
          ((CochainComplex.singleFunctor C 0).map R.complex.f)).mor₃ =
      -((CochainComplex.singleFunctor C 0).map R.ι)⟦(1 : ℤ)⟧' := by
  change (-mappingConeLowerLift R) ≫ _ = _
  rw [Preadditive.neg_comp, mappingConeLowerLift_comp_mor₃]

/-- The lower octahedral edge has the same composite with the cone projection as the literal
mapping-cone inclusion. -/
lemma spliceTriangle_mor₁_comp_compositeTriangle_mor₃
    (R : TwoStepResolution (C := C)) :
    (spliceTriangle R).mor₁ ≫ (compositeTriangle R).mor₃ =
      -((DerivedCategory.singleFunctor C 0).map R.ι)⟦(1 : ℤ)⟧' := by
  dsimp [spliceTriangle]
  exact (Triangulated.someOctahedron _ _ _ _).comm₂

set_option backward.isDefEq.respectTransparency false in
/-- Under the normalized isomorphism from the chosen composite triangle to the standard mapping
cone, the lower edge of the octahedral splice is the literal mapping-cone inclusion. -/
lemma spliceTriangle_mor₁_mappingCone
    (R : TwoStepResolution (C := C)) :
    (spliceTriangle R).mor₁ ≫
        (compositeTriangleIsoMappingCone R).hom.hom₃ =
      (DerivedCategory.Q.commShiftIso 1).inv.app
          ((CochainComplex.singleFunctor C 0).obj R.F) ≫
        DerivedCategory.Q.map (mappingConeLowerInclusion R) := by
  let M := mappingConeCompositeTriangle R
  apply (show Function.Injective
      (fun h : (spliceTriangle R).obj₁ ⟶ M.obj₃ ↦ h ≫ M.mor₃) by
    intro f g h
    rw [← sub_eq_zero]
    have hz : (f - g) ≫ M.mor₃ = 0 := by
      change f ≫ M.mor₃ = g ≫ M.mor₃ at h
      rw [Preadditive.sub_comp, h, sub_self]
    obtain ⟨a, ha⟩ := M.coyoneda_exact₃
      (mappingConeCompositeTriangle_distinguished R) (f - g) hz
    have hle : DerivedCategory.TStructure.t.IsLE
        (spliceTriangle R).obj₁ (-1) := by
      change DerivedCategory.TStructure.t.IsLE
        (((DerivedCategory.singleFunctor C 0).obj R.F)⟦(1 : ℤ)⟧) (-1)
      exact DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by omega)
    have hge : DerivedCategory.TStructure.t.IsGE M.obj₂ 0 := by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor C 0).obj R.complex.X₂) 0
      infer_instance
    rw [ha, DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
      a (-1) 0 (by omega) hle hge, zero_comp])
  dsimp only [M]
  simp only [Category.assoc]
  rw [← (compositeTriangleIsoMappingCone R).hom.comm₃]
  rw [compositeTriangleIsoMappingCone_hom_hom₁]
  simp only [Functor.map_id, Category.comp_id]
  rw [spliceTriangle_mor₁_comp_compositeTriangle_mor₃]
  change
    -((DerivedCategory.singleFunctor C 0).map R.ι)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Q.commShiftIso 1).inv.app
          ((CochainComplex.singleFunctor C 0).obj R.F) ≫
        DerivedCategory.Q.map (mappingConeLowerInclusion R) ≫
          (DerivedCategory.Q.map
              (CochainComplex.mappingCone.triangle
                ((CochainComplex.singleFunctor C 0).map R.complex.f)).mor₃ ≫
            (DerivedCategory.Q.commShiftIso 1).hom.app
              ((CochainComplex.singleFunctor C 0).obj R.complex.X₁))
  rw [← DerivedCategory.Q.map_comp_assoc]
  rw [mappingConeLowerInclusion_comp_mor₃]
  simp only [Functor.map_neg]
  rw [Preadditive.neg_comp, Preadditive.comp_neg]
  simp only [neg_inj]
  change
    (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor C 0).map R.ι) =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app
          ((CochainComplex.singleFunctor C 0).obj R.F) ≫
        (DerivedCategory.Q.map
            ((shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map
              ((CochainComplex.singleFunctor C 0).map R.ι)) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((CochainComplex.singleFunctor C 0).obj R.complex.X₁))
  rw [Functor.commShiftIso_hom_naturality]
  simp
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
omit [HasDerivedCategory C] in
/-- The degree `-1` component of the literal lower mapping-cone inclusion is the coefficient
inclusion of the two-step resolution.  The domain shift and the left-shift cocycle signs cancel,
so this component carries no scalar. -/
lemma mappingConeLowerInclusion_f_negOne
    (R : TwoStepResolution (C := C)) :
    (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) 0 R.F).inv ≫
      (((CochainComplex.singleFunctor C 0).obj R.F).shiftFunctorObjXIso
        1 (-1) 0 (by omega)).inv ≫
      (mappingConeLowerInclusion R).f (-1) ≫
      (CochainComplex.mappingCone.fst
        ((CochainComplex.singleFunctor C 0).map R.complex.f)).1.v
          (-1) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 R.complex.X₁).hom =
      R.ι := by
  dsimp [mappingConeLowerInclusion, mappingConeLowerLift]
  simp only [Category.assoc,
    Preadditive.neg_comp, Preadditive.comp_neg,
    CochainComplex.mappingCone.lift_f_fst_v,
    CochainComplex.mappingCone.lift_f_fst_v_assoc,
    CochainComplex.HomComplex.Cocycle.leftShift_coe,
    CochainComplex.HomComplex.Cocycle.ofHom_coe,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    HomologicalComplex.single_map_f_self]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v
    _ 1 1 (by omega) (-1) 0 (by omega) 0 (by omega)]
  norm_num
  have hsingle :
      ((CochainComplex.singleFunctor C 0).map R.ι).f 0 =
        (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) 0 R.F).hom ≫
          R.ι ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) 0 R.complex.X₁).inv := by
    exact HomologicalComplex.single_map_f_self
      (c := ComplexShape.up ℤ) 0 R.ι
  rw [hsingle]
  erw [Category.id_comp, Category.id_comp]
  norm_num
  erw [Category.id_comp]
  dsimp [HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  erw [Category.id_comp]

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
