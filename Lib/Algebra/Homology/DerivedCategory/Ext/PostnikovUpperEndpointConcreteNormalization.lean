/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2Splice
public import Lib.Algebra.Homology.DerivedCategory.PostnikovUpperRouteHomology

/-!
# The concrete upper endpoint of the adjacent Postnikov two-slice

This file computes the upper edge of the standard mapping-cone model for an adjacent
Postnikov two-slice. After the canonical derived/chain homology comparisons and the good
truncation transports, this edge is exactly the homology quotient. No scalar occurs in this
concrete calculation; the parity scalar belongs to the shifted Postnikov triangle comparison.

## References

* [A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*][bbd82], §1.3.
* [J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*][verdier96], Chapter III, §4.

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- On a degree-zero single complex, the inverse derived homology comparison followed by the
comparison to chain homology is the inverse canonical single-complex homology isomorphism. -/
lemma singleFunctorCompHomologyFunctorIso_inv_comp_homologyFunctorFactors_hom (A : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
        (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((CochainComplex.singleFunctor C 0).obj A) =
      (HomologicalComplex.homologyFunctorSingleIso C
        (ComplexShape.up ℤ) 0).inv.app A := by
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso]
  simp [DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
  slice_lhs 2 4 =>
    erw [Functor.map_id]
    simp
  erw [Category.comp_id]

omit [HasDerivedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- At degree zero, the mapping-cone inclusion followed by the inverse adjacent-two-slice
comparison is the inverse of the canonical degree-zero component isomorphism. -/
lemma mappingCone_inr_comp_shiftedAdjacentTwoSliceIsoMappingCone_inv_f_zero
    (K : CochainComplex C ℤ) (q : ℤ) :
    (CochainComplex.mappingCone.inr
          ((CochainComplex.singleFunctor C 0).map
            (K.opcyclesToCycles q (q + 1))) ≫
        (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv).f 0 =
      (CochainComplex.shiftedTwoSlicePointIsoZero K q).inv := by
  dsimp [CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone,
    CochainComplex.shiftedAdjacentTwoSliceIsoTwoTerm]
  rw [← CochainComplex.twoTermPointIsoZero_hom]
  change
    (CochainComplex.twoTermPointIso
        (K.opcyclesToCycles q (q + 1)) 0).hom ≫
      (CochainComplex.twoTermPointIso
        (K.opcyclesToCycles q (q + 1)) 0).inv ≫
      (CochainComplex.shiftedTwoSlicePointIso K q 0).inv =
    (CochainComplex.shiftedTwoSlicePointIsoZero K q).inv
  simp [CochainComplex.shiftedTwoSlicePointIso]

omit [HasDerivedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- After the shift component comparison, the upper mapping-cone component is the canonical
map from cycles into the adjacent good truncation. -/
lemma mappingCone_inr_shiftedAdjacentTwoSlice_upper_component
    (K : CochainComplex C ℤ) (q : ℤ) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (K.cycles (q + 1))).inv ≫
        (CochainComplex.mappingCone.inr
            ((CochainComplex.singleFunctor C 0).map
              (K.opcyclesToCycles q (q + 1))) ≫
          (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv).f 0 ≫
        ((CochainComplex.adjacentTwoSlice K q).shiftFunctorObjXIso
          (q + 1) 0 (q + 1) (by omega)).hom =
      (K.truncLEXIsoCycles (q + 1)).inv ≫
        ((K.truncLE (q + 1)).πTruncGE q).f (q + 1) := by
  rw [mappingCone_inr_comp_shiftedAdjacentTwoSliceIsoMappingCone_inv_f_zero]
  dsimp [CochainComplex.shiftedTwoSlicePointIsoZero]
  simp [HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  erw [Category.id_comp, Category.id_comp]
  rw [← cancel_mono
    (((K.truncLE (q + 1)).truncGEXIso q (q + 1) (by omega)).hom)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [CochainComplex.πTruncGE_f_interior]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The complete concrete upper endpoint route from the standard mapping-cone triangle induces
the canonical homology quotient. In particular, this comparison introduces no sign. -/
lemma mappingConeCompositeTriangle_mor₂_upper_homology
    (K : CochainComplex C ℤ) (q : ℤ) :
    let R := homologyTwoStepResolutionInt K q
    let L := CochainComplex.adjacentTwoSlice K q
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app
          R.complex.X₂ ≫
      (DerivedCategory.homologyFunctor C 0).map
          (mappingConeCompositeTriangle R).mor₂ ≫
      (DerivedCategory.homologyFunctor C 0).map
          (DerivedCategory.Q.map
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv) ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((shiftFunctor (CochainComplex C ℤ) (q + 1)).obj L) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app L ≫
      (DerivedCategory.adjacentTwoSliceUpperHomologyIso K q).inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).map
        (K.ιTruncLE (q + 1)) =
      R.complex.g := by
  dsimp only
  dsimp [mappingConeCompositeTriangle]
  let R := homologyTwoStepResolutionInt K q
  let L := CochainComplex.adjacentTwoSlice K q
  change
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app
          R.complex.X₂ ≫
      (DerivedCategory.homologyFunctor C 0).map
          (DerivedCategory.Q.map
            (CochainComplex.mappingCone.inr
              ((CochainComplex.singleFunctor C 0).map R.complex.f))) ≫
      (DerivedCategory.homologyFunctor C 0).map
          (DerivedCategory.Q.map
            (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv) ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((shiftFunctor (CochainComplex C ℤ) (q + 1)).obj L) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app L ≫
      (DerivedCategory.adjacentTwoSliceUpperHomologyIso K q).inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).map
        (K.ιTruncLE (q + 1)) =
      R.complex.g
  rw [← Functor.map_comp_assoc]
  rw [← DerivedCategory.Q.map_comp]
  have hfac := (DerivedCategory.homologyFunctorFactors C 0).hom.naturality
    (CochainComplex.mappingCone.inr
      ((CochainComplex.singleFunctor C 0).map R.complex.f) ≫
      (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv)
  erw [Functor.comp_map] at hfac
  rw [reassoc_of% hfac]
  erw [reassoc_of%
    singleFunctorCompHomologyFunctorIso_inv_comp_homologyFunctorFactors_hom
      R.complex.X₂]
  have hsingle :
      (HomologicalComplex.homologyFunctorSingleIso C
        (ComplexShape.up ℤ) 0).inv.app R.complex.X₂ =
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) 0 R.complex.X₂).inv := rfl
  rw [hsingle]
  let h :
      (CochainComplex.singleFunctor C 0).obj (K.cycles (q + 1)) ⟶
        CochainComplex.shiftedAdjacentTwoSlice K q :=
    CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor C 0).map
          (K.opcyclesToCycles q (q + 1))) ≫
      (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q).inv
  change
    (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) 0 (K.cycles (q + 1))).inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).map
          h ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          (q + 1) 0 (q + 1) (by omega)).hom.app L ≫
      (DerivedCategory.adjacentTwoSliceUpperHomologyIso K q).inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (q + 1)).map
        (K.ιTruncLE (q + 1)) =
      K.homologyπ (q + 1)
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc]
  have hnat := HomologicalComplex.homologyπ_naturality (i := 0) (φ := h)
  erw [reassoc_of% hnat]
  let z : K.cycles (q + 1) ⟶
      (CochainComplex.shiftedAdjacentTwoSlice K q).X 0 :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (K.cycles (q + 1))).inv ≫ h.f 0
  have hz : z ≫
      (CochainComplex.shiftedAdjacentTwoSlice K q).d 0 1 = 0 := by
    dsimp only [z]
    erw [Category.assoc, h.comm]
    simp
  have hcycles :
      (HomologicalComplex.singleObjCyclesSelfIso
          (ComplexShape.up ℤ) 0 (K.cycles (q + 1))).inv ≫
        HomologicalComplex.cyclesMap h 0 =
      (CochainComplex.shiftedAdjacentTwoSlice K q).liftCycles
        z 1 (by simp) hz := by
    rw [← cancel_mono
      ((CochainComplex.shiftedAdjacentTwoSlice K q).iCycles 0)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i]
    erw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
  rw [reassoc_of% hcycles]
  have hshift := CochainComplex.liftCycles_shift_homologyπ
    L z 1 (by simp) hz (q + 1) (by omega) (q + 2) (by
      rw [CochainComplex.next]
      omega)
  rw [reassoc_of% hshift]
  simp only [Iso.inv_hom_id_app_assoc]
  let T := K.truncLE (q + 1)
  let π := T.πTruncGE q
  have hw :
      z ≫ (L.shiftFunctorObjXIso
          (q + 1) 0 (q + 1) (by omega)).hom =
        (K.truncLEXIsoCycles (q + 1)).inv ≫ π.f (q + 1) := by
    dsimp only [z, h, L, T, π]
    simpa only [Category.assoc] using
      mappingCone_inr_shiftedAdjacentTwoSlice_upper_component K q
  let w' : K.cycles (q + 1) ⟶ L.X (q + 1) :=
    (K.truncLEXIsoCycles (q + 1)).inv ≫ π.f (q + 1)
  have hTzero : T.d (q + 1) (q + 2) = 0 :=
    by apply (T.isZero_of_isStrictlyLE (q + 1) (q + 2) (by omega)).eq_of_tgt
  have hw'zero : w' ≫ L.d (q + 1) (q + 2) = 0 := by
    dsimp only [w']
    rw [Category.assoc, π.comm]
    rw [hTzero, zero_comp, comp_zero]
  have hwzero :
      (z ≫ (L.shiftFunctorObjXIso
          (q + 1) 0 (q + 1) (by omega)).hom) ≫
        L.d (q + 1) (q + 2) = 0 := by
    rw [hw]
    exact hw'zero
  have hlift :
      L.liftCycles
          (z ≫ (L.shiftFunctorObjXIso
            (q + 1) 0 (q + 1) (by omega)).hom)
          (q + 2) (by rw [CochainComplex.next]; omega) hwzero =
        L.liftCycles w' (q + 2)
          (by rw [CochainComplex.next]; omega) hw'zero := by
    rw [← cancel_mono (L.iCycles (q + 1))]
    simp only [HomologicalComplex.liftCycles_i]
    exact hw
  rw [reassoc_of% hlift]
  let wT : K.cycles (q + 1) ⟶ T.X (q + 1) :=
    (K.truncLEXIsoCycles (q + 1)).inv
  have hwTzero : wT ≫ T.d (q + 1) (q + 2) = 0 := by
    rw [hTzero, comp_zero]
  have hliftπ :
      L.liftCycles w' (q + 2)
          (by rw [CochainComplex.next]; omega) hw'zero =
        T.liftCycles wT (q + 2)
            (by rw [CochainComplex.next]; omega) hwTzero ≫
          HomologicalComplex.cyclesMap π (q + 1) := by
    simpa only [w', L] using
      (HomologicalComplex.liftCycles_comp_cyclesMap
        wT (q + 2) (by rw [CochainComplex.next]; omega)
          hwTzero π).symm
  rw [reassoc_of% hliftπ]
  have hπnat := HomologicalComplex.homologyπ_naturality
    (i := q + 1) (φ := π)
  rw [← reassoc_of% hπnat]
  have hπiso :
      HomologicalComplex.homologyMap π (q + 1) =
        (DerivedCategory.adjacentTwoSliceUpperHomologyIso K q).hom := by
    rfl
  rw [hπiso, Iso.hom_inv_id_assoc]
  let ι : T ⟶ K := K.ιTruncLE (q + 1)
  rw [show
    (HomologicalComplex.homologyFunctor C
      (ComplexShape.up ℤ) (q + 1)).map ι =
        HomologicalComplex.homologyMap ι (q + 1) by rfl]
  have hιnat := HomologicalComplex.homologyπ_naturality
    (i := q + 1) (φ := ι)
  slice_lhs 2 3 =>
    rw [hιnat]
  have hliftι :
      T.liftCycles wT (q + 2)
          (by rw [CochainComplex.next]; omega) hwTzero ≫
        HomologicalComplex.cyclesMap ι (q + 1) =
      𝟙 (K.cycles (q + 1)) := by
    rw [← cancel_mono (K.iCycles (q + 1))]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      Category.id_comp]
    dsimp only [wT, ι, T]
    rw [CochainComplex.ιTruncLE_f_boundary]
    simp
  slice_lhs 1 2 =>
    rw [hliftι]
  erw [Category.id_comp]

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
