/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.PostnikovTwoSliceSplice
public import Lib.CategoryTheory.Triangulated.CoyonedaTriangleShift

/-!
# The adjacent Postnikov connecting map as a two-step splice

This file compares the actual connecting map in the canonical Postnikov spectral object with
the positive Yoneda product of the two short exact sequences around adjacent homology degrees.

The triangle comparison is applied only after shifting by `q + 1`.  Consequently the original
Postnikov connecting map carries exactly the scalar `(q + 1).negOnePow`.  The theorem below
keeps that scalar, both endpoint transports, and both canonical shift associators visible; after
those explicit transports, the result is the positive two-step extension class.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C] [HasExt.{w} C]

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- After transport through the actual shifted-Postnikov-to-splice triangle isomorphism, the
signed adjacent Postnikov connecting map is the positive Yoneda product of the canonical
two-step homology resolution.

The source morphism first enters the literal third endpoint of the splice and is then carried
back to the shifted Postnikov triangle.  On the target, the shift by `q + 1` is undone, the first
triangle component is applied, and the two unit shifts are combined.  Thus every comparison and
the sole parity scalar are explicit in the statement. -/
lemma postnikovAdjacent_homologySequenceδ_apply
    (K : CochainComplex C ℤ) (q : ℤ) (P : C)
    (f : P ⟶ (homologyTwoStepResolutionInt K q).complex.X₃) :
    let T :=
      (DerivedCategory.TStructure.t.triangleω₁δ
        (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
        (by simp) (by simp)).obj (DerivedCategory.Q.obj K)
    let e := shiftedPostnikovAdjacentTriangleIsoSplice K q
    let s₁ := spliceTriangleObj₁Iso (homologyTwoStepResolutionInt K q)
    let s₃ := spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K q)
    ((q + 1).negOnePow •
          ((preadditiveCoyoneda.obj
            (Opposite.op ((DerivedCategory.singleFunctor C 0).obj P))).homologySequenceδ
              T (q + 1) (q + 2) (by omega)
              ((DerivedCategory.singleFunctor C 0).map f ≫ s₃.inv ≫
                e.inv.hom₃))) ≫
        (shiftFunctorAdd' (DerivedCategory C) (q + 1) 1 (q + 2) (by omega)).hom.app
          T.obj₁ ≫
        e.hom.hom₁⟦(1 : ℤ)⟧' ≫
        s₁.hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K q).F) =
      ((((Ext.mk₀ f).comp
          (homologyTwoStepResolutionInt K q).second_shortExact.extClass rfl).comp
        (homologyTwoStepResolutionInt K q).first_shortExact.extClass rfl).hom) := by
  dsimp only
  let T :=
    (DerivedCategory.TStructure.t.triangleω₁δ
      (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
      (by simp) (by simp)).obj (DerivedCategory.Q.obj K)
  let e := shiftedPostnikovAdjacentTriangleIsoSplice K q
  let s₁ := spliceTriangleObj₁Iso (homologyTwoStepResolutionInt K q)
  let s₃ := spliceTriangleObj₃Iso (homologyTwoStepResolutionInt K q)
  let y := (DerivedCategory.singleFunctor C 0).map f ≫ s₃.inv ≫ e.inv.hom₃
  change
    ((q + 1).negOnePow •
          ((preadditiveCoyoneda.obj
            (Opposite.op ((DerivedCategory.singleFunctor C 0).obj P))).homologySequenceδ
              T (q + 1) (q + 2) (by omega) y)) ≫
        (shiftFunctorAdd' (DerivedCategory C) (q + 1) 1 (q + 2) (by omega)).hom.app
          T.obj₁ ≫
        e.hom.hom₁⟦(1 : ℤ)⟧' ≫
        s₁.hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K q).F) =
      ((((Ext.mk₀ f).comp
          (homologyTwoStepResolutionInt K q).second_shortExact.extClass rfl).comp
        (homologyTwoStepResolutionInt K q).first_shortExact.extClass rfl).hom)
  have hy : y ≫ e.hom.hom₃ =
      (DerivedCategory.singleFunctor C 0).map f ≫ s₃.inv := by
    dsimp only [y]
    rw [Category.assoc, Category.assoc,
      e.inv_hom_id_triangle_hom₃, Category.comp_id]
  have hx :
      ((DerivedCategory.singleFunctor C 0).map f ≫ s₃.inv) ≫
          (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
            (spliceTriangle (homologyTwoStepResolutionInt K q)).obj₃ =
        (Ext.mk₀ f).hom := by
    rw [Ext.mk₀_hom]
    change
      ((DerivedCategory.singleFunctor C 0).map f ≫ s₃.inv) ≫
          (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
            (spliceTriangle (homologyTwoStepResolutionInt K q)).obj₃ =
        (DerivedCategory.singleFunctor C 0).map f ≫
          (shiftFunctorZero' (DerivedCategory C) (0 : ℤ) (by rfl)).inv.app
            ((DerivedCategory.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K q).complex.X₃)
    rw [show shiftFunctorZero' (DerivedCategory C) (0 : ℤ) (by rfl) =
        shiftFunctorZero (DerivedCategory C) ℤ by
      simp [shiftFunctorZero']]
    have hz : s₃.inv ≫
          (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
            (spliceTriangle (homologyTwoStepResolutionInt K q)).obj₃ =
        (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
            ((DerivedCategory.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K q).complex.X₃) ≫
          (shiftFunctor (DerivedCategory C) 0).map s₃.inv := by
      simpa only [Functor.id_map] using
        (shiftFunctorZero (DerivedCategory C) ℤ).inv.naturality s₃.inv
    rw [Category.assoc, hz]
    dsimp only [s₃, spliceTriangleObj₃Iso]
    simp only [Iso.refl_inv]
    simp only [spliceTriangle_obj₃, Functor.map_id, Category.comp_id]
  have hpost :
      (shiftFunctor (DerivedCategory C) 1).map e.inv.hom₁ ≫
          (shiftFunctorAdd' (DerivedCategory C) (q + 1) 1 (q + 2)
            (by omega)).inv.app T.obj₁ ≫
          (shiftFunctorAdd' (DerivedCategory C) (q + 1) 1 (q + 2)
            (by omega)).hom.app T.obj₁ ≫
          (shiftFunctor (DerivedCategory C) 1).map e.hom.hom₁ ≫
          (shiftFunctor (DerivedCategory C) 1).map s₁.hom ≫
          (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
            ((DerivedCategory.singleFunctor C 0).obj
              (homologyTwoStepResolutionInt K q).F) =
        (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
          ((DerivedCategory.singleFunctor C 0).obj
            (homologyTwoStepResolutionInt K q).F) := by
    rw [Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc, e.inv_hom_id_triangle_hom₁]
    dsimp only [s₁, spliceTriangleObj₁Iso]
    simp only [spliceTriangle_obj₁, Iso.refl_hom,
      Functor.map_id, Category.id_comp]
  have h :=
    Pretriangulated.preadditiveCoyoneda_homologySequenceδ_shift_iso_of_eq
      T (spliceTriangle (homologyTwoStepResolutionInt K q))
      (q + 1) (q + 2) (by omega) e y
  rw [hy, hx] at h
  rw [← h]
  simp only [Category.assoc, hpost]
  simpa only [T, e] using
    spliceTriangle_homologySequenceδ_apply
      (homologyTwoStepResolutionInt K q) P (Ext.mk₀ f)

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
