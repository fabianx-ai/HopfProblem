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

For a triangle `T` and an integer `n`, Mathlib's triangle shift multiplies all three arrows by
`n.negOnePow`.  This file records how its connecting arrow and the corresponding representable
homology-sequence map compare with those of `T` after the canonical shift associators are
inserted.

The degree-zero statement also removes the formally present shift by zero.  Together, these
lemmas expose the exact parity factor needed when an adjacent Postnikov triangle is shifted to
degrees `-1` and `0`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

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

end CategoryTheory.Pretriangulated
