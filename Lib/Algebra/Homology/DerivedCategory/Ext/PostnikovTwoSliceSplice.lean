/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovTwoSliceShift
public import Lib.Algebra.Homology.DerivedCategory.Ext.AdjacentTwoSliceSplice

/-!
# The shifted adjacent Postnikov triangle as an octahedral splice

This file composes the concrete shifted Postnikov comparison with the mapping-cone/octahedral
splice comparison for the canonical adjacent homology sequence.  The resulting bridge starts at
the actual `triangleω₁δ` used by the canonical spectral object and ends at the two-step splice
whose connecting map is the positive Yoneda product.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

/-- The shifted actual adjacent Postnikov triangle agrees with the octahedral splice of the
canonical adjacent homology sequence. -/
def shiftedPostnikovAdjacentTriangleIsoSplice
    (K : CochainComplex C ℤ) (q : ℤ) :
    DerivedCategory.shiftedPostnikovAdjacentTriangle K q ≅
      spliceTriangle (homologyTwoStepResolutionInt K q) :=
  DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete K q ≪≫
    shiftedAdjacentTwoSliceTriangleIsoSplice K q

/-- The middle component is the explicit shifted two-slice comparison followed by the inverse
of the splice-to-mapping-cone comparison. -/
lemma shiftedPostnikovAdjacentTriangleIsoSplice_hom_hom₂
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangleIsoSplice K q).hom.hom₂ =
      (DerivedCategory.shiftedPostnikovTwoSliceIso K q).hom ≫
        (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).inv := by
  change
    (DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₂ ≫
        (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₂ = _
  rw [DerivedCategory.shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₂,
    shiftedAdjacentTwoSliceTriangleIsoSplice_hom_hom₂]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The third square from the actual Postnikov connecting arrow to the positive splice arrow,
with the parity and shift-commutation factors displayed explicitly. -/
lemma shiftedPostnikovAdjacentTriangleIsoSplice_comm₃_signed
    (K : CochainComplex C ℤ) (q : ℤ) :
    ((q + 1).negOnePow •
          (((DerivedCategory.TStructure.t.triangleω₁δ
            (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
            (by simp) (by simp)).obj (DerivedCategory.Q.obj K)).mor₃)⟦q + 1⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 (q + 1)).hom.app _) ≫
        ((shiftedPostnikovAdjacentTriangleIsoSplice K q).hom.hom₁)⟦(1 : ℤ)⟧' =
      (shiftedPostnikovAdjacentTriangleIsoSplice K q).hom.hom₃ ≫
        (spliceTriangle (homologyTwoStepResolutionInt K q)).mor₃ := by
  rw [← DerivedCategory.shiftedPostnikovAdjacentTriangle_mor₃ K q]
  exact (shiftedPostnikovAdjacentTriangleIsoSplice K q).hom.comm₃

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
