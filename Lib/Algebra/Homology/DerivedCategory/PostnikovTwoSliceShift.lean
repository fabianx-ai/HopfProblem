/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovTwoSlice

/-!
# Shifting an adjacent Postnikov interval to degrees -1 and 0

This file shifts the adjacent Postnikov triangle spanning degrees `q` and `q + 1` by `q + 1`
and compares it with the cutoff-zero triangle of the explicit shifted adjacent two-slice.

The prescribed middle component first uses the concrete good-truncation model and then the
canonical comparison between shifting before and after the derived quotient.  Since Mathlib's
shift functor on triangles scales every arrow by `(q + 1).negOnePow`, the third-square statement
records that parity factor and the canonical commutation of the shifts by `1` and `q + 1`.

## References

* [A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*][bbd82], §1.3, §1.1 (shifted
  triangles and their sign convention).
* [J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*][verdier96], Chapter II.

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

attribute [local instance] HasDerivedCategory.standard

/-- The abstract adjacent Postnikov interval, shifted so that its support lies in degrees
`-1` and `0`, has the explicit shifted good-truncation model. -/
def shiftedPostnikovTwoSliceIso (K : CochainComplex C ℤ) (q : ℤ) :
    ((TStructure.t.truncGE q).obj
      ((TStructure.t.truncLT (q + 2)).obj (Q.obj K)))⟦q + 1⟧ ≅
      Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q) :=
  (shiftFunctor (DerivedCategory C) (q + 1)).mapIso
      (postnikovTwoSliceIso K q) ≪≫
    (Q.commShiftIso (q + 1)).symm.app
      (CochainComplex.adjacentTwoSlice K q)

/-- The actual adjacent triangle in the canonical Postnikov spectral object, shifted to
degrees `-1` and `0`. -/
abbrev shiftedPostnikovAdjacentTriangle (K : CochainComplex C ℤ) (q : ℤ) :
    Triangle (DerivedCategory C) :=
  (Triangle.shiftFunctor (DerivedCategory C) (q + 1)).obj
    ((TStructure.t.triangleω₁δ
      (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
      (by simp) (by simp)).obj (Q.obj K))

/-- The cutoff-`q+1` triangle of the concrete unshifted adjacent two-slice, shifted to
degrees `-1` and `0`. -/
abbrev shiftedAdjacentTwoSliceTruncationTriangle
    (K : CochainComplex C ℤ) (q : ℤ) : Triangle (DerivedCategory C) :=
  (Triangle.shiftFunctor (DerivedCategory C) (q + 1)).obj
    ((TStructure.t.triangleLTGE (q + 1)).obj
      (Q.obj (CochainComplex.adjacentTwoSlice K q)))

/-- Shifting the cutoff-`q+1` triangle of the concrete adjacent slice gives its cutoff-zero
triangle.  The middle component is the canonical compatibility of `Q` with shifts. -/
def shiftedAdjacentTwoSliceTruncationTriangleIsoConcrete
    (K : CochainComplex C ℤ) (q : ℤ) :
    shiftedAdjacentTwoSliceTruncationTriangle K q ≅
      (TStructure.t.triangleLTGE 0).obj
        (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q)) := by
  exact (TStructure.t.triangle_iso_exists
    (Triangle.shift_distinguished _
      (TStructure.t.triangleLTGE_distinguished (q + 1)
        (Q.obj (CochainComplex.adjacentTwoSlice K q))) (q + 1))
    (TStructure.t.triangleLTGE_distinguished 0
      (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q)))
    ((Q.commShiftIso (q + 1)).symm.app
      (CochainComplex.adjacentTwoSlice K q)) (-1) 0
    (by
      exact @TStructure.t.isLE_shift _ _ _ _ _ _ _
        ((TStructure.t.triangleLTGE (q + 1)).obj
          (Q.obj (CochainComplex.adjacentTwoSlice K q))).obj₁
        q (q + 1) (-1) (by omega) (by
          simpa using TStructure.t.isLE_truncLT_obj
            (Q.obj (CochainComplex.adjacentTwoSlice K q)) (q + 1) q (by omega)))
    (by
      exact TStructure.t.isGE_shift _ (q + 1) (q + 1) 0 (by omega))
    (by
      change TStructure.t.IsLE
        ((TStructure.t.truncLT 0).obj
          (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))) (-1)
      exact TStructure.t.isLE_truncLT_obj _ 0 (-1) (by omega))
    (by
      change TStructure.t.IsGE
        ((TStructure.t.truncGE 0).obj
          (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))) 0
      infer_instance)).choose

/-- The shifted cutoff-triangle comparison has the prescribed middle component. -/
lemma shiftedAdjacentTwoSliceTruncationTriangleIsoConcrete_hom_hom₂
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedAdjacentTwoSliceTruncationTriangleIsoConcrete K q).hom.hom₂ =
      (Q.commShiftIso (q + 1)).inv.app
        (CochainComplex.adjacentTwoSlice K q) := by
  exact (TStructure.t.triangle_iso_exists
    (Triangle.shift_distinguished _
      (TStructure.t.triangleLTGE_distinguished (q + 1)
        (Q.obj (CochainComplex.adjacentTwoSlice K q))) (q + 1))
    (TStructure.t.triangleLTGE_distinguished 0
      (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q)))
    ((Q.commShiftIso (q + 1)).symm.app
      (CochainComplex.adjacentTwoSlice K q)) (-1) 0
    (by
      exact @TStructure.t.isLE_shift _ _ _ _ _ _ _
        ((TStructure.t.triangleLTGE (q + 1)).obj
          (Q.obj (CochainComplex.adjacentTwoSlice K q))).obj₁
        q (q + 1) (-1) (by omega) (by
          simpa using TStructure.t.isLE_truncLT_obj
            (Q.obj (CochainComplex.adjacentTwoSlice K q)) (q + 1) q (by omega)))
    (by
      exact TStructure.t.isGE_shift _ (q + 1) (q + 1) 0 (by omega))
    (by
      change TStructure.t.IsLE
        ((TStructure.t.truncLT 0).obj
          (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))) (-1)
      exact TStructure.t.isLE_truncLT_obj _ 0 (-1) (by omega))
    (by
      change TStructure.t.IsGE
        ((TStructure.t.truncGE 0).obj
          (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))) 0
      infer_instance)).choose_spec

/-- The shifted actual spectral-object triangle is the cutoff-zero triangle of the explicit
shifted adjacent two-slice. -/
def shiftedPostnikovAdjacentTriangleIsoConcrete
    (K : CochainComplex C ℤ) (q : ℤ) :
    shiftedPostnikovAdjacentTriangle K q ≅
      (TStructure.t.triangleLTGE 0).obj
        (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q)) :=
  (Triangle.shiftFunctor (DerivedCategory C) (q + 1)).mapIso
      (triangleω₁δIsoAdjacentTwoSliceTriangle K q) ≪≫
    shiftedAdjacentTwoSliceTruncationTriangleIsoConcrete K q

set_option backward.isDefEq.respectTransparency false in
/-- The middle component of the shifted actual-triangle comparison is exactly the shifted
concrete two-slice comparison. -/
lemma shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₂
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₂ =
      (shiftedPostnikovTwoSliceIso K q).hom := by
  change
    ((triangleω₁δIsoAdjacentTwoSliceTriangle K q).hom.hom₂)⟦q + 1⟧' ≫
        (shiftedAdjacentTwoSliceTruncationTriangleIsoConcrete K q).hom.hom₂ = _
  rw [triangleω₁δIsoAdjacentTwoSliceTriangle_hom_hom₂,
    shiftedAdjacentTwoSliceTruncationTriangleIsoConcrete_hom_hom₂]
  rfl

/-- The connecting arrow in the shifted Postnikov triangle displays both the parity of the
triangle shift and the canonical commutation of the shifts by `1` and `q + 1`. -/
lemma shiftedPostnikovAdjacentTriangle_mor₃
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangle K q).mor₃ =
      (q + 1).negOnePow •
          (((TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (Q.obj K)).mor₃)⟦q + 1⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 (q + 1)).hom.app _ := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The third square of the shifted concrete comparison, with its shift parity displayed. -/
lemma shiftedPostnikovAdjacentTriangleIsoConcrete_comm₃_signed
    (K : CochainComplex C ℤ) (q : ℤ) :
    ((q + 1).negOnePow •
          (((TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (Q.obj K)).mor₃)⟦q + 1⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 (q + 1)).hom.app _) ≫
        ((shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₁)⟦(1 : ℤ)⟧' =
      (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₃ ≫
        ((TStructure.t.triangleLTGE 0).obj
          (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))).mor₃ := by
  rw [← shiftedPostnikovAdjacentTriangle_mor₃ K q]
  exact (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.comm₃

end DerivedCategory
