/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTetrahedron
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareSubdivision
/-!
# The boundary relation for based tetrahedra

For a based tetrahedron `τ` the alternating sum of the classes of its four faces vanishes in
`π_2`: `∑ i, (-1) ^ i • basedTriangleClass (basedTetrahedronFace τ i) = 0`
(`basedTetrahedron_signed_relation`).  The proof subdivides the two quadrilateral fillings of
the tetrahedron boundary along their diagonals; each yields a pair of faces, and the fillings
are homotopic, so `[face 3] + [face 1] = [face 0] + [face 2]`.  Applied to the normalized
tetrahedron of a singular `3`-simplex this gives `normalizedTriangle_boundary_relation`: the
triangle-class operator vanishes on boundaries.  This is the relation that makes the inverse
Hurewicz map well defined on `H_2` in this development's proof of the degree-two Hurewicz
theorem (statement: Hatcher, Thm 4.32; the argument is recorded in `Lib/docs/C.md`).

## Main results

* `Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_pair_relation`,
  `basedTetrahedron_boundary_relation`, `basedTetrahedron_signed_relation`.
* `Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedron`,
  `normalizedTriangle_boundary_relation`.
-/

open Set Function Topology

noncomputable section

/-! ### Tetrahedron boundary relations -/

/-- On the lower triangle of the square, `tetrahedronQuadrilateralA` lands on face `3` of the tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_lower
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u) =
      SingularChains.simplexFace 2 3 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![u 0, Min.min (u 0) (u 1)] j =
      (SingularChains.simplexFace 2 3 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_three]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply]

/-- On the upper triangle of the square, `tetrahedronQuadrilateralA` lands on face `1` of the tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_upper
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u) =
      SingularChains.simplexFace 2 1 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have subdivisionSubMin_coe (u v : (unitInterval)) :
    (subdivisionSubMin u v : ℝ) = (u : ℝ) - Min.min (u : ℝ) (v : ℝ) := rfl
  have hm : (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) ≤ (u 0 : ℝ) :=
    sub_le_self _ (le_min (u 0).property.1 (u 1).property.1)
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![subdivisionSubMin (u 0) (u 1), u 0] j =
      (SingularChains.simplexFace 2 1 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_one]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply,
      subdivisionSubMin_coe, min_eq_left hm, max_eq_right hm]

/-- The third face of the quarter-shifted tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_face_three
    (s : SingularChains.Simplex 2) :
    tetrahedronQuarterShift (SingularChains.simplexFace 2 3 s) = SingularChains.simplexFace 2 0 s :=
  by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (SingularChains.simplexFace 2 3 s) j =
      (SingularChains.simplexFace 2 0 s : Fin 4 → ℝ) j
  rw [simplexFace_two_zero]
  fin_cases j
  · exact SingularChains.simplexFace_apply_self 2 3 s
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 2

/-- The first face of the quarter-shifted tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_face_one
    (s : SingularChains.Simplex 2) :
    tetrahedronQuarterShift (SingularChains.simplexFace 2 1 s) =
      SingularChains.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) := by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (SingularChains.simplexFace 2 1 s) j =
      (SingularChains.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) :
          Fin 4 → ℝ)
        j
  rw [simplexFace_two_two]
  fin_cases j
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 2
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 0
  · exact SingularChains.simplexFace_apply_self 2 1 s
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 1

/-- The lower subdivision loop of the quadrilateral loop equals the `basedTriangleLoop` of face `3`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 3) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u)) =
      τ.val (SingularChains.simplexFace 2 3 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower]

/-- The upper subdivision loop of the quadrilateral loop equals the `basedTriangleLoop` of face `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 1) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u)) =
      τ.val (SingularChains.simplexFace 2 1 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_upper]

/-- The lower subdivision loop of the shifted quadrilateral equals the `basedTriangleLoop` of face `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 0) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u))) =
      τ.val (SingularChains.simplexFace 2 0 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower, tetrahedronQuarterShift_face_three]

/-- The upper subdivision loop of the shifted quadrilateral equals the `basedTriangleLoop` of twice-cyclically-permuted face `2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u))) =
      τ.val
        (SingularChains.simplexFace 2 2
          (triangleCyclicPermutation (triangleCyclicPermutation (triangleCubeQuotient u))))
  rw [tetrahedronQuadrilateralA_upper, tetrahedronQuarterShift_face_one]

/-- `basedTriangleClass (face 3) + basedTriangleClass (face 1) = basedTriangleClass (face 0) + basedTriangleClass (face 2)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_pair_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 3) +
        basedTriangleClass (basedTetrahedronFace τ 1) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass (basedTetrahedronFace τ 2) := by
  have hA :=
    subdivision_additiveClass (tetrahedronQuadrilateralLoop τ)
      (tetrahedronQuadrilateralLoop_diagonal τ)
  rw [tetrahedronLowerLoop_eq_face, tetrahedronUpperLoop_eq_face] at hA
  have hB :=
    subdivision_additiveClass (tetrahedronShiftedQuadrilateralLoop τ)
      (tetrahedronShiftedQuadrilateralLoop_diagonal τ)
  rw [tetrahedronShiftedLowerLoop_eq_face, tetrahedronShiftedUpperLoop_eq_face] at hB
  change
    Additive.ofMul (⟦tetrahedronShiftedQuadrilateralLoop τ⟧ : π_ 2 X x) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass
          (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) at hB
  simp only [basedTriangleClass_cyclic] at hB
  exact hA.symm.trans ((congrArg Additive.ofMul (tetrahedronFillings_class τ)).trans hB)

/-- The alternating sum `face 0 - face 1 + face 2 - face 3` of based-triangle classes is `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_boundary_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 0) -
            basedTriangleClass (basedTetrahedronFace τ 1) +
          basedTriangleClass (basedTetrahedronFace τ 2) -
        basedTriangleClass (basedTetrahedronFace τ 3) =
      0 := by
  calc
    _ =
        (basedTriangleClass (basedTetrahedronFace τ 0) +
            basedTriangleClass (basedTetrahedronFace τ 2)) -
          (basedTriangleClass (basedTetrahedronFace τ 3) +
            basedTriangleClass (basedTetrahedronFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedTetrahedron_pair_relation τ).symm

/-- The signed sum `∑ i, (-1)^i • basedTriangleClass (face i)` over the four faces is `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_signed_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • basedTriangleClass (basedTetrahedronFace τ i) = 0 := by
  have h := basedTetrahedron_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

/-- The normalized `3`-simplex packaged as a `BasedTetrahedron` via `normalizedTetrahedronMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) :
    BasedTetrahedron x :=
  BasedTetrahedron.ofFaces (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

/-- The faces of the normalized tetrahedron are normalized based triangles. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedron_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) (i : Fin 4) :
    basedTetrahedronFace (normalizedTetrahedron x smp) i =
      normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i)) := by
  apply Subtype.ext
  exact normalizedTetrahedronMap_face x smp i

/-- The signed sum of the normalized-triangle classes of the four faces is `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangle_boundary_relation {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) :
    ∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          basedTriangleClass (normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i))) =
      0 := by
  simpa only [normalizedTetrahedron_face] using
    basedTetrahedron_signed_relation (normalizedTetrahedron x smp)
