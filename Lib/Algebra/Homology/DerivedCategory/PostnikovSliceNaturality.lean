/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovSlice

/-!
# Naturality of normalized derived-homology comparisons

This file records the all-index compatibility between the derived quotient's shift comparison
and the induced homology shift sequence, then applies the same normalization machinery to
single objects and Postnikov slices.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- Applying derived homology in degree `a` to the quotient's comparison with a shift by `n`,
then using the induced homology shift isomorphism from `a` to `a'`, agrees with first passing to
complex homology and then applying its shift isomorphism.  This is the all-index quotient/shift
coherence square; it introduces no scalar. -/
@[reassoc]
lemma homologyFunctor_map_Q_commShiftIso_hom_comp_shiftIso
    (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (homologyFunctor C a).map ((Q.commShiftIso n).hom.app K) ≫
        ((homologyFunctor C 0).shiftIso n a a' ha').hom.app (Q.obj K) =
      (homologyFunctorFactors C a).hom.app (K⟦n⟧) ≫
        ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          n a a' ha').hom.app K ≫
        (homologyFunctorFactors C a').inv.app K := by
  have hshift := shiftMap_homologyFunctor_map_Q
    (C := C) (K := K⟦n⟧) (L := K) (𝟙 (K⟦n⟧)) a a' ha'
  dsimp [Functor.shiftMap, ShiftedHom.map] at hshift
  rw [Q.map_id] at hshift
  simp only [Category.id_comp] at hshift
  rw [((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shift a).map_id]
    at hshift
  simp only [Category.id_comp] at hshift
  simpa only [Functor.map_comp, Functor.map_id, Category.id_comp,
    shift_homologyFunctor, CochainComplex.homologyFunctor_shift] using hshift

set_option backward.isDefEq.respectTransparency false in
/-- The inverse orientation of the quotient/shift coherence square: first identify derived
homology after shifting, then pass through the quotient comparison.  This form is convenient
when a shifted complex is the target of a normalized Postnikov comparison. -/
@[reassoc]
lemma homologyFunctor_shiftIso_hom_comp_homologyFunctorFactors
    (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    ((homologyFunctor C 0).shiftIso n a a' ha').hom.app (Q.obj K) ≫
        (homologyFunctorFactors C a').hom.app K =
      (homologyFunctor C a).map ((Q.commShiftIso n).inv.app K) ≫
        (homologyFunctorFactors C a).hom.app (K⟦n⟧) ≫
        ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          n a a' ha').hom.app K := by
  let J := (homologyFunctor C a).mapIso ((Q.commShiftIso n).app K)
  change _ = J.inv ≫ _
  rw [← cancel_epi J.hom]
  change (homologyFunctor C a).map ((Q.commShiftIso n).hom.app K) ≫ _ = _
  rw [reassoc_of%
    homologyFunctor_map_Q_commShiftIso_hom_comp_shiftIso n a a' ha' K]
  rw [Iso.inv_hom_id_app]
  simp only [J.hom_inv_id_assoc]
  erw [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology identifications of shifted single objects commute with the
single-functor shift comparison at arbitrary source and target degrees. -/
@[reassoc]
theorem singleFunctorCompHomologyFunctorIso_shiftIso_hom_of_indices
    (A : C) (n a a' : ℤ) (ha' : n + a = a') :
    (homologyFunctor C a).map
        (((singleFunctors C).shiftIso n a a' ha').hom.app A) ≫
        (singleFunctorCompHomologyFunctorIso C a).hom.app A =
      ((homologyFunctor C 0).shiftIso n a a' ha').hom.app
          ((singleFunctor C a').obj A) ≫
        (singleFunctorCompHomologyFunctorIso C a').hom.app A := by
  have hchain :
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) a).map
          (((CochainComplex.singleFunctors C).shiftIso
            n a a' ha').hom.app A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a).hom.app A =
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          n a a' ha').hom.app
            (((CochainComplex.singleFunctors C).functor a').obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a').hom.app A := by
    change _ =
      (CochainComplex.ShiftSequence.shiftIso C n a a' ha').hom.app
          (((CochainComplex.singleFunctors C).functor a').obj A) ≫ _
    rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    dsimp [CochainComplex.singleFunctors]
    rw [← cancel_epi
      (((((HomologicalComplex.single C (ComplexShape.up ℤ) a').obj A)⟦n⟧).homologyπ a))]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
    erw [ShortComplex.homologyπ_naturality_assoc]
    change _ = _ ≫
      (((HomologicalComplex.single C (ComplexShape.up ℤ) a').obj A).homologyπ a' ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) a' A).hom)
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
    dsimp [HomologicalComplex.XIsoOfEq]
    simp only [eqToHom_trans]
    dsimp only [HomologicalComplex.iCycles]
  let α := (singleFunctorsPostcompQIso C).hom
  let Sa' := ((CochainComplex.singleFunctors C).functor a').obj A
  have hcomm := congrArg (fun t ↦ t.app A) (α.comm n a a' ha')
  have hcomm' :
      ((singleFunctors C).shiftIso n a a' ha').hom.app A ≫
          (α.hom a).app A =
        ((α.hom a').app A)⟦n⟧' ≫
          (((CochainComplex.singleFunctors C).postcomp Q).shiftIso
            n a a' ha').hom.app A := by
    simpa using hcomm
  have hnat := ((homologyFunctor C 0).shiftIso
    n a a' ha').hom.naturality ((α.hom a').app A)
  have hnat' := hnat
  simp only [Functor.comp_map, shift_homologyFunctor] at hnat'
  have hshift0 :
      (homologyFunctor C a).map ((Q.commShiftIso n).hom.app Sa') ≫
          ((homologyFunctor C 0).shiftIso n a a' ha').hom.app (Q.obj Sa') =
        (homologyFunctorFactors C a).hom.app (Sa'⟦n⟧) ≫
          ((HomologicalComplex.homologyFunctor C
            (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app Sa' ≫
          (homologyFunctorFactors C a').inv.app Sa' := by
    exact homologyFunctor_map_Q_commShiftIso_hom_comp_shiftIso
      n a a' ha' Sa'
  have hshift1 :
      ((homologyFunctor C 0).shiftIso n a a' ha').hom.app (Q.obj Sa') ≫
          (homologyFunctorFactors C a').hom.app Sa' =
        (homologyFunctor C a).map ((Q.commShiftIso n).inv.app Sa') ≫
          (homologyFunctorFactors C a).hom.app (Sa'⟦n⟧) ≫
          ((HomologicalComplex.homologyFunctor C
            (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app Sa' := by
    let J := (homologyFunctor C a).mapIso ((Q.commShiftIso n).app Sa')
    change _ = J.inv ≫ _
    rw [← cancel_epi J.hom]
    change (homologyFunctor C a).map ((Q.commShiftIso n).hom.app Sa') ≫ _ = _
    rw [reassoc_of% hshift0]
    rw [Iso.inv_hom_id_app]
    simp only [J.hom_inv_id_assoc]
    erw [Category.comp_id]
  have hpost :
      (homologyFunctor C a).map
          ((((CochainComplex.singleFunctors C).postcomp Q).shiftIso
            n a a' ha').hom.app A) ≫
        (homologyFunctorFactors C a).hom.app
          (((CochainComplex.singleFunctors C).functor a).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a).hom.app A =
      ((homologyFunctor C 0).shiftIso n a a' ha').hom.app (Q.obj Sa') ≫
        (homologyFunctorFactors C a').hom.app Sa' ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a').hom.app A := by
    rw [SingleFunctors.postcomp_shiftIso_hom_app]
    rw [Functor.map_comp]
    have hfac := (homologyFunctorFactors C a).hom.naturality
      (((CochainComplex.singleFunctors C).shiftIso
        n a a' ha').hom.app A)
    erw [Functor.comp_map] at hfac
    rw [Category.assoc]
    rw [reassoc_of% hfac]
    erw [hchain]
    rw [reassoc_of% hshift1]
  dsimp [singleFunctorCompHomologyFunctorIso]
  erw [Category.id_comp, Category.id_comp]
  change
    (homologyFunctor C a).map
          (((singleFunctors C).shiftIso n a a' ha').hom.app A) ≫
        (homologyFunctor C a).map ((α.hom a).app A) ≫
        (homologyFunctorFactors C a).hom.app
          (((CochainComplex.singleFunctors C).functor a).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a).hom.app A =
      ((homologyFunctor C 0).shiftIso n a a' ha').hom.app
          ((singleFunctor C a').obj A) ≫
        (homologyFunctor C a').map ((α.hom a').app A) ≫
        (homologyFunctorFactors C a').hom.app Sa' ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a').hom.app A
  rw [← Functor.map_comp_assoc]
  rw [hcomm']
  rw [Functor.map_comp_assoc]
  erw [hpost]
  change
    (homologyFunctor C a).map
          ((shiftFunctor (DerivedCategory C) n).map ((α.hom a').app A)) ≫
        ((homologyFunctor C 0).shiftIso n a a' ha').hom.app
            ((((CochainComplex.singleFunctors C).postcomp Q).functor a').obj A) ≫
        (homologyFunctorFactors C a').hom.app Sa' ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a').hom.app A =
      ((homologyFunctor C 0).shiftIso n a a' ha').hom.app
          (((singleFunctors C).functor a').obj A) ≫
        (homologyFunctor C a').map ((α.hom a').app A) ≫
        (homologyFunctorFactors C a').hom.app Sa' ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) a').hom.app A
  rw [reassoc_of% hnat']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology identifications of shifted single objects commute with the
single-functor shift comparison. -/
@[reassoc]
theorem singleFunctorCompHomologyFunctorIso_shiftIso_hom (A : C) (n : ℤ) :
    (homologyFunctor C 0).map
        (((singleFunctors C).shiftIso n 0 n (by omega)).hom.app A) ≫
        (singleFunctorCompHomologyFunctorIso C 0).hom.app A =
      ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app
          ((singleFunctor C n).obj A) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app A := by
  have hchain :
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).map
          (((CochainComplex.singleFunctors C).shiftIso n 0 n (by omega)).hom.app A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) 0).hom.app A =
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          n 0 n (by omega)).hom.app
            (((CochainComplex.singleFunctors C).functor n).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) n).hom.app A := by
    change _ =
      (CochainComplex.ShiftSequence.shiftIso C n 0 n (by omega)).hom.app
          (((CochainComplex.singleFunctors C).functor n).obj A) ≫ _
    rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    dsimp [CochainComplex.singleFunctors]
    rw [← cancel_epi
      (((((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A)⟦n⟧).homologyπ 0))]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
    erw [ShortComplex.homologyπ_naturality_assoc]
    change _ = _ ≫
      (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A).homologyπ n ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) n A).hom)
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
    dsimp [HomologicalComplex.XIsoOfEq]
    simp only [eqToHom_trans]
    dsimp only [HomologicalComplex.iCycles]
  let α := (singleFunctorsPostcompQIso C).hom
  let Sn := ((CochainComplex.singleFunctors C).functor n).obj A
  have hcomm := congrArg (fun t ↦ t.app A) (α.comm n 0 n (by omega))
  have hcomm' :
      ((singleFunctors C).shiftIso n 0 n (by omega)).hom.app A ≫
          (α.hom 0).app A =
        ((α.hom n).app A)⟦n⟧' ≫
          (((CochainComplex.singleFunctors C).postcomp Q).shiftIso
            n 0 n (by omega)).hom.app A := by
    simpa using hcomm
  have hnat := ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.naturality
    ((α.hom n).app A)
  have hnat' := hnat
  simp only [Functor.comp_map, shift_homologyFunctor] at hnat'
  have hshift := shiftMap_homologyFunctor_map_Q
    (C := C) (K := Sn⟦n⟧) (L := Sn) (𝟙 (Sn⟦n⟧)) 0 n (by omega)
  dsimp [Functor.shiftMap, ShiftedHom.map] at hshift
  rw [Q.map_id] at hshift
  simp only [Category.id_comp] at hshift
  rw [((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shift 0).map_id]
    at hshift
  simp only [Category.id_comp] at hshift
  have hshift0 :
      (homologyFunctor C 0).map ((Q.commShiftIso n).hom.app Sn) ≫
          ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app (Q.obj Sn) =
        (homologyFunctorFactors C 0).hom.app (Sn⟦n⟧) ≫
          ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
            n 0 n (by omega)).hom.app Sn ≫
          (homologyFunctorFactors C n).inv.app Sn := by
    simpa only [Functor.map_comp, Functor.map_id, Category.id_comp,
      shift_homologyFunctor, CochainComplex.homologyFunctor_shift] using hshift
  have hshift1 :
      ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app (Q.obj Sn) ≫
          (homologyFunctorFactors C n).hom.app Sn =
        (homologyFunctor C 0).map ((Q.commShiftIso n).inv.app Sn) ≫
          (homologyFunctorFactors C 0).hom.app (Sn⟦n⟧) ≫
          ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
            n 0 n (by omega)).hom.app Sn := by
    let J := (homologyFunctor C 0).mapIso ((Q.commShiftIso n).app Sn)
    change _ = J.inv ≫ _
    rw [← cancel_epi J.hom]
    change (homologyFunctor C 0).map ((Q.commShiftIso n).hom.app Sn) ≫ _ = _
    rw [reassoc_of% hshift0]
    rw [Iso.inv_hom_id_app]
    simp only [J.hom_inv_id_assoc]
    erw [Category.comp_id]
  have hpost :
      (homologyFunctor C 0).map
          ((((CochainComplex.singleFunctors C).postcomp Q).shiftIso
            n 0 n (by omega)).hom.app A) ≫
        (homologyFunctorFactors C 0).hom.app
          (((CochainComplex.singleFunctors C).functor 0).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) 0).hom.app A =
      ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app (Q.obj Sn) ≫
        (homologyFunctorFactors C n).hom.app Sn ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) n).hom.app A := by
    rw [SingleFunctors.postcomp_shiftIso_hom_app]
    rw [Functor.map_comp]
    have hfac := (homologyFunctorFactors C 0).hom.naturality
      (((CochainComplex.singleFunctors C).shiftIso
        n 0 n (by omega)).hom.app A)
    erw [Functor.comp_map] at hfac
    rw [Category.assoc]
    rw [reassoc_of% hfac]
    erw [hchain]
    rw [reassoc_of% hshift1]
  dsimp [singleFunctorCompHomologyFunctorIso]
  erw [Category.id_comp, Category.id_comp]
  change
    (homologyFunctor C 0).map
          (((singleFunctors C).shiftIso n 0 n (by omega)).hom.app A) ≫
        (homologyFunctor C 0).map ((α.hom 0).app A) ≫
        (homologyFunctorFactors C 0).hom.app
          (((CochainComplex.singleFunctors C).functor 0).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) 0).hom.app A =
      ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app
          ((singleFunctor C n).obj A) ≫
        (homologyFunctor C n).map ((α.hom n).app A) ≫
        (homologyFunctorFactors C n).hom.app Sn ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) n).hom.app A
  rw [← Functor.map_comp_assoc]
  rw [hcomm']
  rw [Functor.map_comp_assoc]
  erw [hpost]
  change
    (homologyFunctor C 0).map
          ((shiftFunctor (DerivedCategory C) n).map ((α.hom n).app A)) ≫
        ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app
            ((((CochainComplex.singleFunctors C).postcomp Q).functor n).obj A) ≫
        (homologyFunctorFactors C n).hom.app Sn ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) n).hom.app A =
      ((homologyFunctor C 0).shiftIso n 0 n (by omega)).hom.app
          (((singleFunctors C).functor n).obj A) ≫
        (homologyFunctor C n).map ((α.hom n).app A) ≫
        (homologyFunctorFactors C n).hom.app Sn ≫
        (HomologicalComplex.homologyFunctorSingleIso C
          (ComplexShape.up ℤ) n).hom.app A
  rw [reassoc_of% hnat']

/-- The chosen comparison from a single-degree derived object to its homology single is
normalized to induce the identity on degree-`n` homology. -/
@[reassoc]
theorem homologyFunctor_map_isoSingleFunctorHomology_hom (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    (homologyFunctor C n).map (isoSingleFunctorHomology K n).hom ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app
          ((homologyFunctor C n).obj K) =
      𝟙 ((homologyFunctor C n).obj K) := by
  let Y := (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose
  let e : K ≅ (singleFunctor C n).obj Y :=
    (exists_iso_singleFunctor_obj_of_isGE_of_isLE K n).choose_spec.some
  let hY : (homologyFunctor C n).obj K ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C n).app Y
  change (homologyFunctor C n).map
      (e.hom ≫ (singleFunctor C n).map hY.inv) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app _ = 𝟙 _
  rw [Functor.map_comp, Category.assoc,
    ← Functor.comp_map, (singleFunctorCompHomologyFunctorIso C n).hom.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc]
  change hY.hom ≫ hY.inv = 𝟙 _
  simp

/-- The normalized Postnikov-slice comparison induces exactly the canonical identification of
its degree-`n` homology with the degree-`n` homology of the original object. -/
@[reassoc]
theorem homologyFunctor_map_postnikovSliceIso_hom (K : DerivedCategory C) (n : ℤ) :
    (homologyFunctor C n).map (postnikovSliceIso K n).hom ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app
          ((homologyFunctor C n).obj K) =
      (postnikovSliceHomologyIso K n).hom := by
  dsimp only [postnikovSliceIso]
  simp only [Iso.trans_hom, Functor.map_comp, Functor.mapIso_hom,
    Category.assoc]
  rw [show
    (homologyFunctor C n).map
        ((singleFunctor C n).map (postnikovSliceHomologyIso K n).hom) =
      (singleFunctor C n ⋙ homologyFunctor C n).map
        (postnikovSliceHomologyIso K n).hom by rfl]
  rw [(singleFunctorCompHomologyFunctorIso C n).hom.naturality]
  simp only [Functor.id_map]
  rw [homologyFunctor_map_isoSingleFunctorHomology_hom_assoc]

/-- Degree-`n` homology is faithful on the image of the degree-`n` single functor. -/
theorem homologyFunctor_map_injective_singleFunctor (A B : C) (n : ℤ) :
    Function.Injective (fun f : (singleFunctor C n).obj A ⟶ (singleFunctor C n).obj B ↦
      (homologyFunctor C n).map f) := by
  intro f g h
  suffices hp :
      (singleFunctor C n).preimage f = (singleFunctor C n).preimage g by
    rw [← (singleFunctor C n).map_preimage f,
      ← (singleFunctor C n).map_preimage g, hp]
  apply (cancel_epi
    ((singleFunctorCompHomologyFunctorIso C n).hom.app A)).mp
  calc
    (singleFunctorCompHomologyFunctorIso C n).hom.app A ≫
        (singleFunctor C n).preimage f =
      (singleFunctor C n ⋙ homologyFunctor C n).map
          ((singleFunctor C n).preimage f) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
          simpa only [Functor.id_map] using
            ((singleFunctorCompHomologyFunctorIso C n).hom.naturality
              ((singleFunctor C n).preimage f)).symm
    _ = (homologyFunctor C n).map f ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
      simp only [Functor.comp_map, (singleFunctor C n).map_preimage]
    _ = (homologyFunctor C n).map g ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
      change (homologyFunctor C n).map f = (homologyFunctor C n).map g at h
      rw [h]
    _ = (singleFunctor C n ⋙ homologyFunctor C n).map
          ((singleFunctor C n).preimage g) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app B := by
      simp only [Functor.comp_map, (singleFunctor C n).map_preimage]
    _ = (singleFunctorCompHomologyFunctorIso C n).hom.app A ≫
        (singleFunctor C n).preimage g := by
      simpa only [Functor.id_map] using
        (singleFunctorCompHomologyFunctorIso C n).hom.naturality
          ((singleFunctor C n).preimage g)

/-- Degree-`n` homology detects morphisms between objects concentrated in degree `n`. -/
theorem homologyFunctor_map_injective_of_isGE_of_isLE
    (K L : DerivedCategory C) (n : ℤ) [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n] :
    Function.Injective (fun f : K ⟶ L ↦ (homologyFunctor C n).map f) := by
  intro f g h
  change (homologyFunctor C n).map f = (homologyFunctor C n).map g at h
  apply (cancel_epi (isoSingleFunctorHomology K n).inv).mp
  apply (cancel_mono (isoSingleFunctorHomology L n).hom).mp
  apply homologyFunctor_map_injective_singleFunctor
  simp only [Functor.map_comp, h]

/-- The normalized comparison with the degree-`n` single homology object is natural on
objects concentrated in degree `n`. -/
@[reassoc]
theorem isoSingleFunctorHomology_hom_naturality
    {K L : DerivedCategory C} (n : ℤ) [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n]
    (f : K ⟶ L) :
    (isoSingleFunctorHomology K n).hom ≫
        (singleFunctor C n).map ((homologyFunctor C n).map f) =
      f ≫ (isoSingleFunctorHomology L n).hom := by
  apply homologyFunctor_map_injective_of_isGE_of_isLE K _ n
  apply (cancel_mono
    ((singleFunctorCompHomologyFunctorIso C n).hom.app
      ((homologyFunctor C n).obj L))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map,
    (singleFunctorCompHomologyFunctorIso C n).hom.naturality]
  simp only [Functor.id_map,
    homologyFunctor_map_isoSingleFunctorHomology_hom_assoc,
    homologyFunctor_map_isoSingleFunctorHomology_hom,
    Category.comp_id]

/-- The canonical identification of the degree-`n` homology of a Postnikov slice with
degree-`n` homology is natural in the derived object. -/
@[reassoc]
theorem postnikovSliceHomologyIso_hom_naturality
    {K L : DerivedCategory C} (n : ℤ) (f : K ⟶ L) :
    (homologyFunctor C n).map
          ((TStructure.t.truncLT (n + 1) ⋙ TStructure.t.truncGE n).map f) ≫
        (postnikovSliceHomologyIso L n).hom =
      (postnikovSliceHomologyIso K n).hom ≫ (homologyFunctor C n).map f := by
  have := isIso_homologyFunctor_map_truncGEπ
    ((TStructure.t.truncLT (n + 1)).obj K) n
  have := isIso_homologyFunctor_map_truncGEπ
    ((TStructure.t.truncLT (n + 1)).obj L) n
  have := isIso_homologyFunctor_map_truncLTι K n
  have := isIso_homologyFunctor_map_truncLTι L n
  simp only [postnikovSliceHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Functor.comp_map]
  apply (cancel_epi ((homologyFunctor C n).map
    ((TStructure.t.truncGEπ n).app
      ((TStructure.t.truncLT (n + 1)).obj K)))).mp
  simp only [Category.assoc]
  rw [← (homologyFunctor C n).map_comp_assoc]
  rw [TStructure.t.truncGEπ_naturality]
  rw [(homologyFunctor C n).map_comp_assoc]
  simp only [IsIso.hom_inv_id_assoc]
  simpa only [Functor.map_comp, Functor.id_map] using
    congrArg (fun g => (homologyFunctor C n).map g)
      ((TStructure.t.truncLTι (n + 1)).naturality f)

/-- The normalized comparison from a Postnikov slice to the single object on its homology is
natural in the derived object. -/
@[reassoc]
theorem postnikovSliceIso_hom_naturality
    {K L : DerivedCategory C} (n : ℤ) (f : K ⟶ L) :
    (TStructure.t.truncLT (n + 1) ⋙ TStructure.t.truncGE n).map f ≫
        (postnikovSliceIso L n).hom =
      (postnikovSliceIso K n).hom ≫
        (singleFunctor C n).map ((homologyFunctor C n).map f) := by
  have : ((TStructure.t.truncLT (n + 1) ⋙ TStructure.t.truncGE n).obj K).IsLE n := by
    dsimp only [Functor.comp_obj]
    infer_instance
  have : ((TStructure.t.truncLT (n + 1) ⋙ TStructure.t.truncGE n).obj L).IsLE n := by
    dsimp only [Functor.comp_obj]
    infer_instance
  simp only [postnikovSliceIso, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
  rw [← isoSingleFunctorHomology_hom_naturality_assoc n
    ((TStructure.t.truncGE n).map ((TStructure.t.truncLT (n + 1)).map f))]
  simp only [Category.assoc, ← (singleFunctor C n).map_comp]
  have h :
      (homologyFunctor C n).map
            ((TStructure.t.truncGE n).map ((TStructure.t.truncLT (n + 1)).map f)) ≫
          (postnikovSliceHomologyIso L n).hom =
        (postnikovSliceHomologyIso K n).hom ≫ (homologyFunctor C n).map f := by
    simpa only [Functor.comp_map] using postnikovSliceHomologyIso_hom_naturality n f
  rw [h]

end DerivedCategory
