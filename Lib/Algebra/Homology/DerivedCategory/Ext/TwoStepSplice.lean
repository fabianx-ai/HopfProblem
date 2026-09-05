/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgression
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The octahedral splice of a two-step resolution

For an exact sequence `0 → F → X₁ → X₂ → H → 0`, the octahedron axiom splices the
two associated short exact triangles into a triangle from `F⟦1⟧` to `H`.  Its connecting
morphism is the positive composite of the two short-exact connecting morphisms.  Applying the
derived coyoneda functor therefore gives the corresponding positive Yoneda product, including
the canonical comparison from the iterated shift to shift by two.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]
variable (R : TwoStepResolution (C := C))

/-- A distinguished triangle whose first morphism is the single-object image of the middle
composite `X₁ ⟶ X₂` of a two-step resolution. -/
noncomputable def compositeTriangle : Triangle (DerivedCategory C) := by
  let u := (DerivedCategory.singleFunctor C 0).map R.complex.f
  let h := distinguished_cocone_triangle u
  exact Triangle.mk u h.choose_spec.choose h.choose_spec.choose_spec.choose

/-- `compositeTriangle` is distinguished. -/
lemma compositeTriangle_distinguished :
    compositeTriangle R ∈ distTriang (DerivedCategory C) := by
  dsimp [compositeTriangle]
  exact (distinguished_cocone_triangle
    ((DerivedCategory.singleFunctor C 0).map R.complex.f)).choose_spec.choose_spec.choose_spec

set_option backward.isDefEq.respectTransparency false

/-- The octahedral splice triangle associated to a two-step resolution. -/
noncomputable def spliceTriangle : Triangle (DerivedCategory C) := by
  let T₁ := R.first_shortExact.singleTriangle
  let T₂ := R.second_shortExact.singleTriangle
  let T₃ := compositeTriangle R
  have comm : T₁.rotate.mor₁ ≫ T₂.mor₁ = T₃.mor₁ := by
    change (DerivedCategory.singleFunctor C 0).map R.toBoundary ≫
      (DerivedCategory.singleFunctor C 0).map (kernel.ι R.complex.g) =
        (DerivedCategory.singleFunctor C 0).map R.complex.f
    rw [← Functor.map_comp, R.toBoundary_ι]
  let H := Triangulated.someOctahedron comm
    (rot_of_distTriang T₁ R.first_shortExact.singleTriangle_distinguished)
    R.second_shortExact.singleTriangle_distinguished
    (compositeTriangle_distinguished R)
  exact H.triangle

/-- The octahedral splice triangle is distinguished. -/
lemma spliceTriangle_distinguished :
    spliceTriangle R ∈ distTriang (DerivedCategory C) := by
  dsimp [spliceTriangle]
  exact (Triangulated.someOctahedron _ _ _ _).mem

/-- The connecting morphism of the splice is the positive composite of the two short-exact
connecting morphisms. -/
lemma spliceTriangle_mor₃ :
    (spliceTriangle R).mor₃ =
      R.second_shortExact.singleδ ≫ R.first_shortExact.singleδ⟦(1 : ℤ)⟧' := by
  dsimp [spliceTriangle]
  rfl

variable [HasExt.{w} C]

/-- Coyoneda homology of the splice connecting morphism is the positive Yoneda product of the
two short exact extension classes. -/
lemma spliceTriangle_homologySequenceδ_apply (P : C)
    (x : Ext.{w} P R.complex.X₃ 0) :
    (preadditiveCoyoneda.obj
        (Opposite.op ((DerivedCategory.singleFunctor C 0).obj P))).homologySequenceδ
          (spliceTriangle R) 0 1 rfl x.hom ≫
      (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor C 0).obj R.F) =
      (((x.comp R.second_shortExact.extClass rfl).comp
        R.first_shortExact.extClass rfl).hom) := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply,
    spliceTriangle_mor₃, Ext.comp_hom, Ext.comp_hom,
    ShortComplex.ShortExact.extClass_hom,
    ShortComplex.ShortExact.extClass_hom]
  change
    (x.hom ≫
      (shiftFunctor (DerivedCategory C) 0).map
        (R.second_shortExact.singleδ ≫
          R.first_shortExact.singleδ⟦(1 : ℤ)⟧') ≫
      (shiftFunctorAdd' (DerivedCategory C) 1 0 1 rfl).inv.app
        (((DerivedCategory.singleFunctor C 0).obj R.F)⟦(1 : ℤ)⟧)) ≫
      (shiftFunctorAdd' (DerivedCategory C) 1 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor C 0).obj R.F) =
    ShiftedHom.comp (c := 2)
      (ShiftedHom.comp (c := 1) x.hom R.second_shortExact.singleδ rfl)
        R.first_shortExact.singleδ rfl
  simp only [Functor.map_comp, Category.assoc]
  rw [← shiftFunctorAdd'_assoc_inv_app (C := DerivedCategory C)
    1 1 0 2 1 2 rfl rfl rfl]
  simpa [ShiftedHom.comp, Functor.map_comp, Category.assoc] using
    (ShiftedHom.comp_assoc x.hom R.second_shortExact.singleδ
      R.first_shortExact.singleδ rfl rfl rfl).symm

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
