/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.AdjacentTwoSlice
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-!
# A concrete model for an adjacent Postnikov interval

For an integer-indexed cochain complex `K`, the Postnikov interval cut out by the two adjacent
degrees `q` and `q + 1` is represented by the concrete good-truncation complex
`(K.truncLE (q + 1)).truncGE q`.

The second comparison identifies the triangle occurring in the canonical spectral object with
the ordinary truncation triangle of this concrete two-slice. It is deliberately stated before
shifting the two degrees to `-1` and `0`; the cochain-shift sign is handled by the explicit
two-slice model in `AdjacentTwoSlice`.
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

/-- The abstract Postnikov interval supported in degrees `q` and `q + 1` has the concrete
adjacent good-truncation model. -/
def postnikovTwoSliceIso (K : CochainComplex C ℤ) (q : ℤ) :
    (TStructure.t.truncGE q).obj
        ((TStructure.t.truncLT (q + 2)).obj (Q.obj K)) ≅
      Q.obj (CochainComplex.adjacentTwoSlice K q) :=
  let e₁ :
      (TStructure.t.truncGE q).obj
          ((TStructure.t.truncLT (q + 2)).obj (Q.obj K)) ≅
        (TStructure.t.truncGE q).obj (Q.obj (K.truncLE (q + 1))) := by
    simpa only [show q + 2 - 1 = q + 1 by omega] using
      (TStructure.t.truncGE q).mapIso (truncLTIsoQTruncLE K (q + 2))
  e₁ ≪≫ truncGEIsoQTruncGE (K.truncLE (q + 1)) q

/-- The triangle in the canonical spectral object spanning the adjacent degrees `q` and
`q + 1` is the canonical truncation triangle of the concrete adjacent two-slice. -/
def triangleω₁δIsoAdjacentTwoSliceTriangle
    (K : CochainComplex C ℤ) (q : ℤ) :
    (TStructure.t.triangleω₁δ (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + 2 : ℤ) : EInt) (by simp) (by simp)).obj (Q.obj K) ≅
      (TStructure.t.triangleLTGE (q + 1)).obj
        (Q.obj (CochainComplex.adjacentTwoSlice K q)) :=
  TStructure.t.triangleω₁δObjIso (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + 2 : ℤ) : EInt) (by simp) (by simp) (Q.obj K) ≪≫
    (TStructure.t.triangleLTGE (q + 1)).mapIso (postnikovTwoSliceIso K q)

/-- The middle component of the adjacent-triangle comparison is precisely the concrete
two-slice comparison. -/
lemma triangleω₁δIsoAdjacentTwoSliceTriangle_hom_hom₂
    (K : CochainComplex C ℤ) (q : ℤ) :
    (triangleω₁δIsoAdjacentTwoSliceTriangle K q).hom.hom₂ =
      (postnikovTwoSliceIso K q).hom := by
  change 𝟙 _ ≫ (postnikovTwoSliceIso K q).hom = _
  simp

end DerivedCategory
