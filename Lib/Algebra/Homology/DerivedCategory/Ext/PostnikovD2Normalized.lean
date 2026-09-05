/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2SourceCoordinates
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2PageCoordinates
public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovLowerEndpointNormalization

/-!
# Normalized page-two Postnikov differential

This file identifies the page-two differential in the coyoneda Postnikov spectral sequence with
the two-step connecting homomorphism of the canonical homology resolution.  The shift comparison
contributes the same parity scalar to the page differential and its source coordinate; these
factors cancel, so the exported comparison is unsigned.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Opposite

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C] [HasExt.{v} C]

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- The normalized target `Ext²` coordinate is the literal lower edge of the canonical
two-step splice, after the displayed shift associators. -/
lemma coyonedaPostnikovD₂TargetExt_hom_eq_splice
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (y : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (2, q)) :
    (coyonedaPostnikovD₂TargetExt K P q y).hom =
      (DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          ((DerivedCategory.singleFunctor C 0).obj P)
          (DerivedCategory.Q.obj K) 0 q).hom.hom y ≫
        eqToHom (by simp) ≫
        (shiftFunctorAdd' (DerivedCategory C) ((q : ℤ) + 1) 1
          ((q : ℤ) + 2) (by omega)).hom.app
            ((DerivedCategory.TStructure.t.triangleω₁δ
              ((q : ℤ) : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
              (((q : ℤ) + 2 : ℤ) : EInt) (by simp) (by simp)).obj
                (DerivedCategory.Q.obj K)).obj₁ ≫
        ((shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₁)⟦(1 : ℤ)⟧' ≫
        ((spliceTriangleObj₁Iso
          (homologyTwoStepResolutionInt K (q : ℤ))).hom)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K (q : ℤ)).F) := by
  let g :=
    (DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          ((DerivedCategory.singleFunctor C 0).obj P)
          (DerivedCategory.Q.obj K) 0 q).hom.hom y ≫
      eqToHom (by simp) ≫
      (postnikovTargetExtIso K (q : ℤ)).hom ≫
      ((DerivedCategory.singleFunctor C 0).map
        ((DerivedCategory.homologyFunctorFactors C (q : ℤ)).hom.app K))⟦(2 : ℤ)⟧'
  have htarget : (coyonedaPostnikovD₂TargetExt K P q y).hom = g := by
    dsimp [coyonedaPostnikovD₂TargetExt, g]
    exact Equiv.apply_symm_apply _ _
  rw [htarget]
  dsimp only [g]
  rw [postnikovTargetExtIso_hom_eq_shiftedLowerEndpoint]
  simp only [Category.assoc]
  have hsuffix :
      ((DerivedCategory.shiftedPostnikovLowerEndpointIso K (q : ℤ)).hom)⟦(1 : ℤ)⟧' ≫
          ((((DerivedCategory.singleFunctors C).shiftIso
            1 (-1) 0 (by omega)).inv.app
              ((DerivedCategory.homologyFunctor C (q : ℤ)).obj
                (DerivedCategory.Q.obj K)))⟦(1 : ℤ)⟧') ≫
          (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
            ((DerivedCategory.singleFunctor C 0).obj
              ((DerivedCategory.homologyFunctor C (q : ℤ)).obj
                (DerivedCategory.Q.obj K))) ≫
          ((DerivedCategory.singleFunctor C 0).map
            ((DerivedCategory.homologyFunctorFactors C (q : ℤ)).hom.app K))⟦(2 : ℤ)⟧' =
        ((shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₁)⟦(1 : ℤ)⟧' ≫
          ((spliceTriangleObj₁Iso
            (homologyTwoStepResolutionInt K (q : ℤ))).hom)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
            ((DerivedCategory.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K (q : ℤ)).F) := by
    let u :
        (DerivedCategory.homologyFunctor C (q : ℤ)).obj
            (DerivedCategory.Q.obj K) ⟶
          (homologyTwoStepResolutionInt K (q : ℤ)).F :=
      (DerivedCategory.homologyFunctorFactors C (q : ℤ)).hom.app K
    have hfac :
        ((shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₁ ≫
            (spliceTriangleObj₁Iso
              (homologyTwoStepResolutionInt K (q : ℤ))).hom) ≫
            ((DerivedCategory.singleFunctors C).shiftIso
              1 (-1) 0 (by omega)).hom.app
                (homologyTwoStepResolutionInt K (q : ℤ)).F =
          (DerivedCategory.shiftedPostnikovLowerEndpointIso K (q : ℤ)).hom ≫
            (DerivedCategory.singleFunctor C (-1)).map u := by
      simpa only [u, Category.assoc] using
        shiftedPostnikovAdjacentTriangleIsoSplice_hom_hom₁_lower K (q : ℤ)
    have hsuffix' := lowerTargetShift_of_fac
      ((shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₁ ≫
        (spliceTriangleObj₁Iso
          (homologyTwoStepResolutionInt K (q : ℤ))).hom)
      (DerivedCategory.shiftedPostnikovLowerEndpointIso K (q : ℤ)).hom
      u hfac
    simpa only [u, Functor.map_comp, Category.assoc] using hsuffix'
  rw [hsuffix]
  rfl

/-- In normalized `Ext` coordinates, the page-two Postnikov differential is the unsigned
two-step connecting homomorphism of the canonical homology resolution. -/
lemma coyonedaPostnikovD₂TargetExt_d₂
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (x : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (0, q + 1)) :
    coyonedaPostnikovD₂TargetExt K P q
        ((((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
          ((DerivedCategory.singleFunctor C 0).obj P)
          (DerivedCategory.Q.obj K)).page 2).d (0, q + 1) (2, q)).hom x) =
      (homologyTwoStepResolutionInt K (q : ℤ)).connectingTwo P
        (Ext.mk₀ (coyonedaPostnikovD₂SourceHom K P q x)) := by
  let y :=
    (((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).d (0, q + 1) (2, q)).hom x
  let R := homologyTwoStepResolutionInt K (q : ℤ)
  let source : P ⟶ R.complex.X₃ :=
    coyonedaPostnikovD₂SourceHom K P q x
  let target : Ext P R.F 2 :=
    coyonedaPostnikovD₂TargetExt K P q y
  have htarget0 := coyonedaPostnikovD₂TargetExt_hom_eq_splice K P q y
  have htarget : target.hom =
      (DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          ((DerivedCategory.singleFunctor C 0).obj P)
          (DerivedCategory.Q.obj K) 0 q).hom.hom y ≫
        eqToHom (by simp) ≫
        (shiftFunctorAdd' (DerivedCategory C) ((q : ℤ) + 1) 1
          ((q : ℤ) + 2) (by omega)).hom.app
            ((DerivedCategory.TStructure.t.triangleω₁δ
              ((q : ℤ) : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
              (((q : ℤ) + 2 : ℤ) : EInt) (by simp) (by simp)).obj
                (DerivedCategory.Q.obj K)).obj₁ ≫
        ((shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₁)⟦(1 : ℤ)⟧' ≫
        ((spliceTriangleObj₁Iso R).hom)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj R.F) := by
    dsimp only [target]
    exact htarget0
  have hsplice := coyonedaPostnikovE₂_d₂_connectingTwo_apply K P q x
  have hsource := coyonedaPostnikovD₂SpliceSource_eq K P q x
  dsimp only at hsplice hsource
  rw [hsource] at hsplice
  have hsplice' : (Ext.homAddEquiv (X := P) (Y := R.F) (n := 2)).symm
      ((((q : ℤ) + 1).negOnePow •
        (DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          ((DerivedCategory.singleFunctor C 0).obj P)
          (DerivedCategory.Q.obj K) 0 q).hom.hom y) ≫
        eqToHom (by simp) ≫
        (shiftFunctorAdd' (DerivedCategory C) ((q : ℤ) + 1) 1
          ((q : ℤ) + 2) (by omega)).hom.app
            ((DerivedCategory.TStructure.t.triangleω₁δ
              ((q : ℤ) : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
              (((q : ℤ) + 2 : ℤ) : EInt) (by simp) (by simp)).obj
                (DerivedCategory.Q.obj K)).obj₁ ≫
        ((shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)).hom.hom₁)⟦(1 : ℤ)⟧' ≫
        ((spliceTriangleObj₁Iso R).hom)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj R.F)) =
      R.connectingTwo P
        (Ext.mk₀ (((q : ℤ) + 1).negOnePow • source)) := by
    dsimp only [R, source, y]
    exact hsplice
  have hsigned :
      ((q : ℤ) + 1).negOnePow • target =
        R.connectingTwo P
          (Ext.mk₀ (((q : ℤ) + 1).negOnePow • source)) := by
    rw [← hsplice']
    apply (Ext.homAddEquiv (X := P)
      (Y := R.F) (n := 2)).injective
    rw [AddEquiv.apply_symm_apply]
    simp only [Units.smul_def, map_zsmul, Ext.homAddEquiv_apply]
    simpa only [Preadditive.zsmul_comp] using congrArg (fun z ↦
      (((q : ℤ) + 1).negOnePow : ℤˣ).val • z) htarget
  change target = R.connectingTwo P (Ext.mk₀ source)
  rw [← connectingTwo_negOnePow_cancel
    R P ((q : ℤ) + 1) source]
  rw [← hsigned]
  simp only [smul_smul, Int.units_mul_self, one_smul]

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
