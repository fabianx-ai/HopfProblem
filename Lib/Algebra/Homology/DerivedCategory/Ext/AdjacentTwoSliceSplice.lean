/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.AdjacentTwoSlice
public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgressionHomology
public import Lib.Algebra.Homology.DerivedCategory.Ext.TwoStepSplice

/-!
# The adjacent two-slice triangle as an octahedral splice

The homology sequence of an integer-indexed cochain complex gives a canonical two-step exact
sequence around degrees `q` and `q + 1`.  This file compares its octahedral splice triangle with
the canonical cutoff-zero truncation triangle of the shifted adjacent two-slice.

The middle-object comparison is fixed by the explicit signed isomorphism from the shifted
two-slice to the mapping cone on `opcyclesToCycles`.  The resulting third square carries the
canonical truncation connecting morphism to the positive composite of the two short-exact
connecting morphisms; no additional negation is introduced.

## References

* [A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*][bbd82], §1.3 (adjacent
  truncations of the canonical t-structure).
* [M. Kashiwara, P. Schapira, *Categories and sheaves*][kashiwaraSchapira06], §10.1.
* [J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*][verdier96], Chapter II (the
  octahedral axiom).

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe w' v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

/-- The middle object of the octahedral splice of the canonical adjacent homology sequence is
the derived image of the shifted adjacent two-slice. -/
noncomputable def spliceObjTwoIsoShiftedAdjacentTwoSlice
    (K : CochainComplex C ℤ) (q : ℤ) :
    (spliceTriangle (homologyTwoStepResolutionInt K q)).obj₂ ≅
      DerivedCategory.Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q) :=
  Triangle.π₃.mapIso
      (compositeTriangleIsoMappingCone
        (homologyTwoStepResolutionInt K q)) ≪≫
    (DerivedCategory.Q.mapIso
      (CochainComplex.shiftedAdjacentTwoSliceIsoMappingCone K q)).symm

/-- The canonical cutoff-zero triangle of the shifted adjacent two-slice agrees with the
octahedral splice triangle, normalized by the explicit two-slice/mapping-cone comparison on the
middle object. -/
noncomputable def shiftedAdjacentTwoSliceTriangleIsoSplice
    (K : CochainComplex C ℤ) (q : ℤ) :
    (DerivedCategory.TStructure.t.triangleLTGE 0).obj
        (DerivedCategory.Q.obj
          (CochainComplex.shiftedAdjacentTwoSlice K q)) ≅
      spliceTriangle (homologyTwoStepResolutionInt K q) := by
  let R := homologyTwoStepResolutionInt K q
  let e :
      DerivedCategory.Q.obj
          (CochainComplex.shiftedAdjacentTwoSlice K q) ≅
        (spliceTriangle R).obj₂ :=
    (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).symm
  exact (DerivedCategory.TStructure.t.triangle_iso_exists
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished 0
      (DerivedCategory.Q.obj
        (CochainComplex.shiftedAdjacentTwoSlice K q)))
    (spliceTriangle_distinguished R) e (-1) 0
    (by
      simpa using (inferInstanceAs
        (DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.triangleLTGE 0).obj
            (DerivedCategory.Q.obj
              (CochainComplex.shiftedAdjacentTwoSlice K q))).obj₁ (0 - 1))))
    (by infer_instance)
    (by
      change DerivedCategory.TStructure.t.IsLE
        (((DerivedCategory.singleFunctor C 0).obj R.F)⟦(1 : ℤ)⟧) (-1)
      exact DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by omega))
    (by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor C 0).obj R.complex.X₃) 0
      infer_instance)
    (by omega)).choose

/-- The whole-triangle comparison has the prescribed middle component. -/
lemma shiftedAdjacentTwoSliceTriangleIsoSplice_hom_hom₂
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₂ =
      (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).inv := by
  exact (DerivedCategory.TStructure.t.triangle_iso_exists
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished 0
      (DerivedCategory.Q.obj
        (CochainComplex.shiftedAdjacentTwoSlice K q)))
    (spliceTriangle_distinguished (homologyTwoStepResolutionInt K q))
    (spliceObjTwoIsoShiftedAdjacentTwoSlice K q).symm (-1) 0
    (by
      simpa using (inferInstanceAs
        (DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.triangleLTGE 0).obj
            (DerivedCategory.Q.obj
              (CochainComplex.shiftedAdjacentTwoSlice K q))).obj₁ (0 - 1))))
    (by infer_instance)
    (by
      change DerivedCategory.TStructure.t.IsLE
        (((DerivedCategory.singleFunctor C 0).obj
          (homologyTwoStepResolutionInt K q).F)⟦(1 : ℤ)⟧) (-1)
      exact DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by omega))
    (by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor C 0).obj
          (homologyTwoStepResolutionInt K q).complex.X₃) 0
      infer_instance)
    (by omega)).choose_spec

/-- The third square carries the canonical truncation connecting morphism to the splice
connecting morphism. -/
lemma shiftedAdjacentTwoSliceTriangleIsoSplice_comm₃
    (K : CochainComplex C ℤ) (q : ℤ) :
    ((DerivedCategory.TStructure.t.triangleLTGE 0).obj
        (DerivedCategory.Q.obj
          (CochainComplex.shiftedAdjacentTwoSlice K q))).mor₃ ≫
        ((shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₁)⟦(1 : ℤ)⟧' =
      (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.hom₃ ≫
        (spliceTriangle (homologyTwoStepResolutionInt K q)).mor₃ :=
  (shiftedAdjacentTwoSliceTriangleIsoSplice K q).hom.comm₃

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
