/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Coyoneda connecting maps and shifted triangles

For a triangle `T` and an integer `n`, Mathlib's triangle shift `Triangle.shiftFunctor`
multiplies all three arrows of `T⟦n⟧` by the sign `n.negOnePow`; this is the standard sign
convention for the shift of a distinguished triangle (Neeman, *Triangulated Categories*, §1.1;
Verdier).  This file records how the connecting arrow of `T⟦n⟧` and the associated representable
homology-sequence map of `preadditiveCoyoneda` compare with those of `T` once the canonical shift
associators `shiftFunctorAdd` are inserted, and specialises the comparison to degree zero, where
the formally present shift by `0` is removed.

The homology sequence of a representable functor on a triangle is
`CategoryTheory.Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply` in
`Mathlib/CategoryTheory/Triangulated/Yoneda.lean`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

set_option backward.isDefEq.respectTransparency false in
/-- Reindex a representable homology-sequence connecting map along equal source and target
degrees.  The displayed `eqToHom`s are the exact transports on the shifted endpoints. -/
lemma preadditiveCoyoneda_homologySequenceδ_reindex_apply
    (T : Triangle C) {A : Cᵒᵖ}
    (n₀ n₁ n₀' n₁' : ℤ) (h : n₀ + 1 = n₁) (h' : n₀' + 1 = n₁')
    (hn₀ : n₀ = n₀') (hn₁ : n₁ = n₁')
    (x : A.unop ⟶ T.obj₃⟦n₀⟧) :
    (preadditiveCoyoneda.obj A).homologySequenceδ T n₀ n₁ h x ≫
        eqToHom (congrArg (fun n : ℤ ↦ T.obj₁⟦n⟧) hn₁) =
      (preadditiveCoyoneda.obj A).homologySequenceδ T n₀' n₁' h'
        (x ≫ eqToHom (congrArg (fun n : ℤ ↦ T.obj₃⟦n⟧) hn₀)) := by
  cases hn₀
  cases hn₁
  rw [Subsingleton.elim h' h]
  simp only [eqToHom_refl]
  rw [Category.comp_id x]
  exact Category.comp_id
    ((preadditiveCoyoneda.obj A).homologySequenceδ T n₀ n₁ h x)

/-- At degrees zero and one, the representable connecting map is literal postcomposition by
the triangle's third arrow after cancelling the canonical shift-by-zero maps. -/
lemma preadditiveCoyoneda_homologySequenceδ_zero_apply
    (T : Triangle C) {A : Cᵒᵖ} (x : A.unop ⟶ T.obj₃) :
    (preadditiveCoyoneda.obj A).homologySequenceδ T 0 1 rfl
        (x ≫ (shiftFunctorZero C ℤ).inv.app T.obj₃) =
      x ≫ T.mor₃ := by
  rw [preadditiveCoyoneda_homologySequenceδ_apply]
  rw [shiftFunctorAdd'_add_zero_inv_app]
  simp only [Category.assoc]
  rw [NatIso.naturality_1]
  rw [Functor.id_map]

/-- The third arrow of a shifted triangle displays the parity scalar and the canonical
commutation of its two shifts. -/
lemma triangleShift_mor₃ (T : Triangle C) (n : ℤ) :
    ((Triangle.shiftFunctor C n).obj T).mor₃ =
      n.negOnePow • T.mor₃⟦n⟧' ≫
        (shiftFunctorComm C 1 n).hom.app T.obj₁ := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- After recombining the target shifts, the third arrow of a shifted triangle is the original
third arrow shifted by `n`, multiplied by exactly `n.negOnePow`. -/
lemma triangleShift_mor₃_comp_shiftFunctorAdd_inv (T : Triangle C) (n : ℤ) :
    ((Triangle.shiftFunctor C n).obj T).mor₃ ≫
        (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ =
      n.negOnePow •
        (T.mor₃⟦n⟧' ≫
          (shiftFunctorAdd' C 1 n (n + 1) (by omega)).inv.app T.obj₁) := by
  change
    (n.negOnePow • T.mor₃⟦n⟧' ≫
        (shiftFunctorComm C 1 n).hom.app T.obj₁) ≫
      (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ = _
  rw [shiftFunctorComm_eq C 1 n (n + 1) (by omega)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Linear.units_smul_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero-to-one coyoneda connecting map of `T⟦n⟧` is `n.negOnePow` times the
degree-`n`-to-`n+1` connecting map of `T`, after the canonical zero and sum shift comparisons. -/
lemma preadditiveCoyoneda_homologySequenceδ_shift_zero
    (T : Triangle C) (n : ℤ) {A : Cᵒᵖ}
    (x : A.unop ⟶ ((Triangle.shiftFunctor C n).obj T).obj₃) :
    (preadditiveCoyoneda.obj A).homologySequenceδ
          ((Triangle.shiftFunctor C n).obj T) 0 1 rfl
          (x ≫ (shiftFunctorZero C ℤ).inv.app
            ((Triangle.shiftFunctor C n).obj T).obj₃) ≫
        (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ =
      n.negOnePow •
        ((preadditiveCoyoneda.obj A).homologySequenceδ
          T n (n + 1) rfl x) := by
  rw [preadditiveCoyoneda_homologySequenceδ_zero_apply]
  calc
    _ = x ≫ (((Triangle.shiftFunctor C n).obj T).mor₃ ≫
          (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁) :=
      Category.assoc _ _ _
    _ = x ≫ (n.negOnePow •
          (T.mor₃⟦n⟧' ≫
            (shiftFunctorAdd' C 1 n (n + 1) (by omega)).inv.app T.obj₁)) := by
      rw [triangleShift_mor₃_comp_shiftFunctorAdd_inv]
    _ = n.negOnePow •
        ((preadditiveCoyoneda.obj A).homologySequenceδ
          T n (n + 1) rfl x) := by
      rw [preadditiveCoyoneda_homologySequenceδ_apply]
      simp only [Linear.comp_units_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Transport the shifted-triangle formula across an arbitrary triangle isomorphism.  The
argument is first carried by the third component of `e`; the result is carried back by the
shift of its inverse first component.  After these components cancel through the third square
of `e`, the only scalar left is the parity factor contributed by the triangle shift itself. -/
lemma preadditiveCoyoneda_homologySequenceδ_shift_iso
    (T T' : Triangle C) (n : ℤ)
    (e : (Triangle.shiftFunctor C n).obj T ≅ T') {A : Cᵒᵖ}
    (x : A.unop ⟶ ((Triangle.shiftFunctor C n).obj T).obj₃) :
    (preadditiveCoyoneda.obj A).homologySequenceδ T' 0 1 rfl
          ((x ≫ e.hom.hom₃) ≫
            (shiftFunctorZero C ℤ).inv.app T'.obj₃) ≫
        e.inv.hom₁⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ =
      n.negOnePow •
        ((preadditiveCoyoneda.obj A).homologySequenceδ
          T n (n + 1) rfl x) := by
  rw [preadditiveCoyoneda_homologySequenceδ_zero_apply]
  rw [Category.assoc, Category.assoc, ← e.hom.comm₃_assoc]
  rw [← Category.assoc
    ((shiftFunctor C (1 : ℤ)).map e.hom.hom₁)
    ((shiftFunctor C (1 : ℤ)).map e.inv.hom₁)]
  rw [← Functor.map_comp, e.hom_inv_id_triangle_hom₁,
    Functor.map_id, Category.id_comp]
  simpa only [preadditiveCoyoneda_homologySequenceδ_zero_apply,
    Category.assoc] using
      preadditiveCoyoneda_homologySequenceδ_shift_zero T n x

set_option backward.isDefEq.respectTransparency false in
/-- A version of `preadditiveCoyoneda_homologySequenceδ_shift_iso` in which the successor
degree is named independently.  This avoids forcing clients to normalize expressions such as
`(q + 1) + 1` and `q + 2` definitionally. -/
lemma preadditiveCoyoneda_homologySequenceδ_shift_iso_of_eq
    (T T' : Triangle C) (n m : ℤ) (hnm : n + 1 = m)
    (e : (Triangle.shiftFunctor C n).obj T ≅ T') {A : Cᵒᵖ}
    (x : A.unop ⟶ ((Triangle.shiftFunctor C n).obj T).obj₃) :
    (preadditiveCoyoneda.obj A).homologySequenceδ T' 0 1 rfl
          ((x ≫ e.hom.hom₃) ≫
            (shiftFunctorZero C ℤ).inv.app T'.obj₃) ≫
        e.inv.hom₁⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' C n 1 m hnm).inv.app T.obj₁ =
      n.negOnePow •
        ((preadditiveCoyoneda.obj A).homologySequenceδ
          T n m hnm x) := by
  subst m
  simpa using preadditiveCoyoneda_homologySequenceδ_shift_iso T T' n e x

end CategoryTheory.Pretriangulated
