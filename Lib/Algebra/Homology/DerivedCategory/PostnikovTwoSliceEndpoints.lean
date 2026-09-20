/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.PostnikovSlice
public import Lib.Algebra.Homology.DerivedCategory.PostnikovTwoSliceShift

/-!
# Normalized endpoints of the shifted adjacent Postnikov triangle

The endpoints of the adjacent Postnikov triangle are the degree-`q` and degree-`q+1` slices.
After shifting the triangle by `q + 1`, this file identifies them with single objects in degrees
`-1` and `0`, using the maintained normalized `postnikovSliceIso`.

The same normalizations are transported to the cutoff-zero triangle of the explicit shifted
two-slice.  The exported composition equalities make that transport available without unfolding
the endpoint components selected by t-structure triangle uniqueness.

## References

* [A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*][bbd82], §1.3 (endpoints of the
  adjacent Postnikov triangle).

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

/-- The lower endpoint of the shifted adjacent Postnikov triangle is the degree-`q` homology
object placed in degree `-1`. -/
def shiftedPostnikovLowerEndpointIso (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangle K q).obj₁ ≅
      (singleFunctor C (-1)).obj ((homologyFunctor C q).obj (Q.obj K)) :=
  (shiftFunctor (DerivedCategory C) (q + 1)).mapIso
      (postnikovSliceIso (Q.obj K) q) ≪≫
    ((singleFunctors C).shiftIso (q + 1) (-1) q (by omega)).app
      ((homologyFunctor C q).obj (Q.obj K))

/-- Before shifting, the upper endpoint of the adjacent triangle is the degree-`q+1`
Postnikov slice. -/
def postnikovUpperEndpointIso (K : CochainComplex C ℤ) (q : ℤ) :
    ((TStructure.t.triangleω₁δ
      (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 2 : ℤ) : EInt)
      (by simp) (by simp)).obj (Q.obj K)).obj₃ ≅
      (singleFunctor C (q + 1)).obj
        ((homologyFunctor C (q + 1)).obj (Q.obj K)) := by
  change (TStructure.t.truncGE (q + 1)).obj
      ((TStructure.t.truncLT (q + 2)).obj (Q.obj K)) ≅ _
  exact (TStructure.t.truncGE (q + 1)).mapIso
      (eqToIso (by
        congr 2
        omega)) ≪≫
    postnikovSliceIso (Q.obj K) (q + 1)

/-- The upper endpoint of the shifted adjacent Postnikov triangle is the degree-`q+1` homology
object placed in degree zero. -/
def shiftedPostnikovUpperEndpointIso (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangle K q).obj₃ ≅
      (singleFunctor C 0).obj ((homologyFunctor C (q + 1)).obj (Q.obj K)) :=
  (shiftFunctor (DerivedCategory C) (q + 1)).mapIso
      (postnikovUpperEndpointIso K q) ≪≫
    ((singleFunctors C).shiftIso (q + 1) 0 (q + 1) (by omega)).app
      ((homologyFunctor C (q + 1)).obj (Q.obj K))

/-- The lower endpoint adapter on the concrete cutoff-zero triangle, normalized by
`postnikovSliceIso`. -/
def concreteLowerEndpointPostnikovIso (K : CochainComplex C ℤ) (q : ℤ) :
    ((TStructure.t.triangleLTGE 0).obj
      (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))).obj₁ ≅
      (singleFunctor C (-1)).obj ((homologyFunctor C q).obj (Q.obj K)) :=
  (Triangle.π₁.mapIso (shiftedPostnikovAdjacentTriangleIsoConcrete K q)).symm ≪≫
    shiftedPostnikovLowerEndpointIso K q

/-- The upper endpoint adapter on the concrete cutoff-zero triangle, normalized by
`postnikovSliceIso`. -/
def concreteUpperEndpointPostnikovIso (K : CochainComplex C ℤ) (q : ℤ) :
    ((TStructure.t.triangleLTGE 0).obj
      (Q.obj (CochainComplex.shiftedAdjacentTwoSlice K q))).obj₃ ≅
      (singleFunctor C 0).obj ((homologyFunctor C (q + 1)).obj (Q.obj K)) :=
  (Triangle.π₃.mapIso (shiftedPostnikovAdjacentTriangleIsoConcrete K q)).symm ≪≫
    shiftedPostnikovUpperEndpointIso K q

set_option backward.isDefEq.respectTransparency false in
/-- The lower endpoint of the shifted triangle bridge agrees with the normalized Postnikov
adapter after transport to the concrete cutoff-zero triangle. -/
@[reassoc]
lemma shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₁_postnikov
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₁ ≫
        (concreteLowerEndpointPostnikovIso K q).hom =
      (shiftedPostnikovLowerEndpointIso K q).hom := by
  change (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₁ ≫
      (shiftedPostnikovAdjacentTriangleIsoConcrete K q).inv.hom₁ ≫
        (shiftedPostnikovLowerEndpointIso K q).hom = _
  exact (Triangle.π₁.mapIso
    (shiftedPostnikovAdjacentTriangleIsoConcrete K q)).hom_inv_id_assoc _

set_option backward.isDefEq.respectTransparency false in
/-- The upper endpoint of the shifted triangle bridge agrees with the normalized Postnikov
adapter after transport to the concrete cutoff-zero triangle. -/
@[reassoc]
lemma shiftedPostnikovAdjacentTriangleIsoConcrete_hom_hom₃_postnikov
    (K : CochainComplex C ℤ) (q : ℤ) :
    (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₃ ≫
        (concreteUpperEndpointPostnikovIso K q).hom =
      (shiftedPostnikovUpperEndpointIso K q).hom := by
  change (shiftedPostnikovAdjacentTriangleIsoConcrete K q).hom.hom₃ ≫
      (shiftedPostnikovAdjacentTriangleIsoConcrete K q).inv.hom₃ ≫
        (shiftedPostnikovUpperEndpointIso K q).hom = _
  exact (Triangle.π₃.mapIso
    (shiftedPostnikovAdjacentTriangleIsoConcrete K q)).hom_inv_id_assoc _

end DerivedCategory
