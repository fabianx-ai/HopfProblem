/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovD2Splice
public import Lib.Algebra.Homology.SpectralObject.PostnikovD2

/-!
# The page-two Postnikov differential as a two-step splice

This file joins the literal page-two differential of the coyoneda Postnikov spectral sequence
to the positive Yoneda product of the adjacent two-step homology resolution.  The only sign is
the parity `(q + 1).negOnePow` contributed by shifting the Postnikov triangle by `q + 1`.

Both page endpoint transports, both components of the Postnikov-to-splice triangle isomorphism,
and the shift associators remain explicit.  This makes the result independent of any later
choice of coordinates on the two homology objects.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Opposite

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C] [HasExt.{w} C]

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- After the normalized page-two endpoints are transported to the shifted adjacent Postnikov
triangle and then to its two-step splice, the signed page differential is the positive Yoneda
product of the canonical two-step homology resolution. -/
lemma coyonedaPostnikovE₂_d₂_splice_apply
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (x : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (0, q + 1)) :
    let T :=
      (DerivedCategory.TStructure.t.triangleω₁δ
        ((q : ℤ) : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
        (((q : ℤ) + 2 : ℤ) : EInt) (by simp) (by simp)).obj
          (DerivedCategory.Q.obj K)
    let e := shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)
    let s₁ := spliceTriangleObj₁Iso (homologyTwoStepResolutionInt K (q : ℤ))
    let s₃ := spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K (q : ℤ))
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
      (z ≫ e.hom.hom₃ ≫ s₃.hom)
    (((q : ℤ) + 1).negOnePow •
        ((DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
          ((DerivedCategory.singleFunctor C 0).obj P) (DerivedCategory.Q.obj K) 0 q).hom.hom
            ((((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
              ((DerivedCategory.singleFunctor C 0).obj P)
              (DerivedCategory.Q.obj K)).page 2).d (0, q + 1) (2, q)).hom x))) ≫
      eqToHom (by
        dsimp [T]
        rw [DerivedCategory.TStructure.t.triangleω₁δ_obj_obj₁]
        simp) ≫
      (shiftFunctorAdd' (DerivedCategory C) ((q : ℤ) + 1) 1 ((q : ℤ) + 2)
        (by omega)).hom.app T.obj₁ ≫
      e.hom.hom₁⟦(1 : ℤ)⟧' ≫
      s₁.hom⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor C 0).obj
          (homologyTwoStepResolutionInt K (q : ℤ)).F) =
      ((((Ext.mk₀ f).comp
        (homologyTwoStepResolutionInt K (q : ℤ)).second_shortExact.extClass rfl).comp
        (homologyTwoStepResolutionInt K (q : ℤ)).first_shortExact.extClass rfl).hom) := by
  dsimp only
  let T :=
    (DerivedCategory.TStructure.t.triangleω₁δ
      ((q : ℤ) : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
      (((q : ℤ) + 2 : ℤ) : EInt) (by simp) (by simp)).obj
        (DerivedCategory.Q.obj K)
  let e := shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)
  let s₁ := spliceTriangleObj₁Iso (homologyTwoStepResolutionInt K (q : ℤ))
  let s₃ := spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K (q : ℤ))
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
    (z ≫ e.hom.hom₃ ≫ s₃.hom)
  have hf : (DerivedCategory.singleFunctor C 0).map f =
      z ≫ e.hom.hom₃ ≫ s₃.hom :=
    (DerivedCategory.singleFunctor C 0).map_preimage _
  have hd := DerivedCategory.TStructure.t.coyonedaPostnikovE₂_d₂_eq
    ((DerivedCategory.singleFunctor C 0).obj P) (DerivedCategory.Q.obj K) 0 q
  simp only [Int.ofNat_zero] at hd
  rw [hd]
  simp only [AddCommGrpCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  have hz : (DerivedCategory.singleFunctor C 0).map f ≫
        s₃.inv ≫ e.inv.hom₃ = z := by
    rw [hf]
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      e.hom_inv_id_triangle_hom₃, Category.comp_id]
  have h := postnikovAdjacent_homologySequenceδ_apply K (q : ℤ) P f
  dsimp only at h
  rw [hz] at h
  let u :=
    (DerivedCategory.TStructure.t.coyonedaPostnikovD₂SourcePageIso
      ((DerivedCategory.singleFunctor C 0).obj P) (DerivedCategory.Q.obj K) 0 q).hom.hom x
  have hreindex :=
    Pretriangulated.preadditiveCoyoneda_homologySequenceδ_reindex_apply T
      (A := op ((DerivedCategory.singleFunctor C 0).obj P))
      ((0 : ℤ) + (q : ℤ) + 1) ((0 : ℤ) + (q : ℤ) + 2)
      ((q : ℤ) + 1) ((q : ℤ) + 2)
      (by omega) (by omega) (by omega) (by omega) u
  rw [Linear.units_smul_comp]
  simp only [← Category.assoc]
  erw [hreindex]
  simp only [Category.assoc]
  rw [← Linear.units_smul_comp]
  convert h using 1
  all_goals simp only [e, s₃, z, f, Category.assoc]

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C] [HasExt.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- In `Ext` coordinates, the explicitly transported and signed page-two differential is the
connecting class of the canonical adjacent two-step homology resolution.

This is the `Ext`-valued form of `coyonedaPostnikovE₂_d₂_splice_apply`.  The derived-category
universe is independent of the hom universe; only `TwoStepResolution.connectingTwo` remains at
the hom universe of `C`. -/
lemma coyonedaPostnikovE₂_d₂_connectingTwo_apply
    (K : CochainComplex C ℤ) [K.IsGE 0] (P : C) (q : ℕ)
    (x : ((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
      ((DerivedCategory.singleFunctor C 0).obj P)
      (DerivedCategory.Q.obj K)).page 2).X (0, q + 1)) :
    let T :=
      (DerivedCategory.TStructure.t.triangleω₁δ
        ((q : ℤ) : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
        (((q : ℤ) + 2 : ℤ) : EInt) (by simp) (by simp)).obj
          (DerivedCategory.Q.obj K)
    let e := shiftedPostnikovAdjacentTriangleIsoSplice K (q : ℤ)
    let s₁ := spliceTriangleObj₁Iso (homologyTwoStepResolutionInt K (q : ℤ))
    let s₃ := spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K (q : ℤ))
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
      (z ≫ e.hom.hom₃ ≫ s₃.hom)
    (Ext.homAddEquiv (X := P)
      (Y := (homologyTwoStepResolutionInt K (q : ℤ)).F) (n := 2)).symm
      ((((q : ℤ) + 1).negOnePow •
          ((DerivedCategory.TStructure.t.coyonedaPostnikovD₂TargetPageIso
            ((DerivedCategory.singleFunctor C 0).obj P) (DerivedCategory.Q.obj K) 0 q).hom.hom
              ((((DerivedCategory.TStructure.t.coyonedaPostnikovSpectralSequence
                ((DerivedCategory.singleFunctor C 0).obj P)
                (DerivedCategory.Q.obj K)).page 2).d (0, q + 1) (2, q)).hom x))) ≫
        eqToHom (by
          dsimp [T]
          rw [DerivedCategory.TStructure.t.triangleω₁δ_obj_obj₁]
          simp) ≫
        (shiftFunctorAdd' (DerivedCategory C) ((q : ℤ) + 1) 1 ((q : ℤ) + 2)
          (by omega)).hom.app T.obj₁ ≫
        e.hom.hom₁⟦(1 : ℤ)⟧' ≫
        s₁.hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K (q : ℤ)).F)) =
      (homologyTwoStepResolutionInt K (q : ℤ)).connectingTwo P (Ext.mk₀ f) := by
  dsimp only
  apply Ext.homAddEquiv.injective
  rw [AddEquiv.apply_symm_apply, Ext.homAddEquiv_apply]
  exact coyonedaPostnikovE₂_d₂_splice_apply K P q x

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
