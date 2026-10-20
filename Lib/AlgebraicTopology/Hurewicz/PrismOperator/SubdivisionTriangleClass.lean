/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.NormalizedSquare
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareSubdivision
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.TwoTriangles
/-!
# The class of a glued pair of based triangles

The based square glued from two based triangles `τ` (below the diagonal) and `υ` (above it)
has class `basedTriangleClass τ - basedTriangleClass υ` in `Additive (π_ 2 X x)`
(`basedTrianglesLoop_class`): the diagonal subdivision splits the class into the lower and
upper triangle classes, and the upper triangle is read against its orientation, which negates
the class (`subdivisionUpperOrientation_class`).  Together with the normalization of a square
this gives `triangleClassOperator x (squareChain p) = ⟦p⟧` and therefore
`hurewiczInverse x ∘ hurewiczMap x = id` (`hurewiczInverse_comp_hurewiczMap`): the Hurewicz map
is injective (Hatcher, Thm 4.32, second half of the `n = 2` case).

## Main results

* `Hurewicz.DegreeTwo.SimplyConnected.subdivision_basedTriangleClass_sum`,
  `subdivisionUpperOrientation_class`, `subdivision_basedTriangleClass_sub`.
* `Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_class`, `squareNormalization_class`.
* `Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_squareChain`,
  `hurewiczInverse_comp_hurewiczMap`.
-/

open Set Function Topology

noncomputable section

/-! ### Subdivision triangle classes -/

/-- The square map of the positively oriented upper subdivision triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  Hurewicz.DegreeTwo.squareCoordinates.comp (squareAffineTriangle ![(0, 0), (1, 1), (0, 1)])

/-- The `0`-face of the upper positive subdivision triangle. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_zero
    (s : SingularChains.Simplex 2) : (subdivisionUpperPositiveSquareTriangle s 0 : ℝ) = s 1 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_fst_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

/-- The `1`-face of the upper positive subdivision triangle. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_one
    (s : SingularChains.Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_snd_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

/-- The coordinate sum of a subdivision triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionTriangle_coordinate_sum
    (s : SingularChains.Simplex 2) : s 0 + s 1 + s 2 = 1 := by
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  linarith

/-- `p (lowerSquareTriangle s) = x` for `s` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerSquareTriangle_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (lowerSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle s 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

/-- `p (upperSquareTriangle s) = x` for `s` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (upperSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle s 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

/-- `p (subdivisionUpperPositiveSquareTriangle s) = x` for `s` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (subdivisionUpperPositiveSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = 1
    rw [subdivisionUpperPositiveSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi
  · change s 2 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]

/-- The lower subdivision triangle as a based triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerBasedTriangle {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    BasedTriangle x :=
  ⟨p.val.comp lowerSquareTriangle, subdivisionLowerSquareTriangle_based p hd⟩

/-- The upper subdivision triangle read against the orientation, as a `BasedTriangle`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp upperSquareTriangle, subdivisionUpperNegativeSquareTriangle_based p hd⟩

/-- The upper subdivision triangle read with the orientation, as a `BasedTriangle`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp subdivisionUpperPositiveSquareTriangle,
    subdivisionUpperPositiveSquareTriangle_based p hd⟩

/-- The lower triangle loop equals the loop of the lower based triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionLowerTriangleLoop p hd = basedTriangleLoop (subdivisionLowerBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, Min.min (u 0) (u 1)] = p (lowerSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

/-- The upper triangle loops equal the loops of the upper based triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperTriangleLoop p hd =
      basedTriangleLoop (subdivisionUpperPositiveBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![subdivisionSubMin (u 0) (u 1), u 0] =
      p (subdivisionUpperPositiveSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp [subdivisionSubMin]

/-- The loop of the upper negative based triangle at `u` is `p ![min (u 0) (u 1), u 0]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeBasedTriangle_loop_apply {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : Fin 2 → (unitInterval)) :
    basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) u =
      p ![Min.min (u 0) (u 1), u 0] := by
  change p (upperSquareTriangle (triangleQuotient (u 0, u 1))) = p ![Min.min (u 0) (u 1), u 0]
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

/-- `⟦p⟧` splits as the sum of the lower and upper positive based-triangle classes. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_basedTriangleClass_sum {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) +
        basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) := by
  simpa only [subdivisionLowerTriangleLoop_eq_basedTriangleLoop,
    subdivisionUpperTriangleLoop_eq_basedTriangleLoop, basedTriangleClass] using
    subdivision_additiveClass p hd

/-- The subdivision-square map underlying the negatively oriented upper triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) (u 1), u 0]
  continuous_toFun := by fun_prop

/-- The `subdivisionUpperNegativeMap` with the second coordinate reversed. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0]
  continuous_toFun := by fun_prop

/-- `p (subdivisionUpperNegativeMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

/-- `p (subdivisionUpperNegativeReversedMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeReversedMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩

/-- The pullback loop `p ∘ subdivisionUpperNegativeMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeMap (subdivisionUpperNegativeMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperNegativeReversedMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedLoop {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeReversedMap
    (subdivisionUpperNegativeReversedMap_based p hd)

/-- The upper triangle map and the reversed upper negative map land on the same side of the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperTriangleMap u) (subdivisionUpperNegativeReversedMap u) :=
  by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .one 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperTriangleMap, h])
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact
      .zero 0 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])

/-- The homotopy relating the upper negative loop to its reversal. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientationHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperTriangleLoop p hd).val.HomotopyRel
      (subdivisionUpperNegativeReversedLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperTriangleMap_based p hd)
    (subdivisionUpperNegativeReversedMap_based p hd) subdivisionUpperOrientation_sides

/-- The reversed upper negative loop is `symmAt 1` of the upper negative loop. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedLoop_eq_symmAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeReversedLoop p hd =
      GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0] =
      subdivisionUpperNegativeLoop p hd
        (fun j => if j = 1 then (unitInterval.symm) (u 1) else u j)
  simp [subdivisionUpperNegativeLoop, subdivisionPullbackLoop, subdivisionUpperNegativeMap]

/-- The upper triangle loop is homotopic to the `symmAt 1`-reversed upper negative loop. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic (subdivisionUpperTriangleLoop p hd)
      (GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)) := by
  rw [← subdivisionUpperNegativeReversedLoop_eq_symmAt]
  exact ⟨subdivisionUpperOrientationHomotopy p hd⟩

/-- `⟦subdivisionUpperTriangleLoop⟧ = ⟦subdivisionUpperNegativeLoop⟧⁻¹` in `π_2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_class {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((·⁻¹) : π_ 2 X x → π_ 2 X x) ⟦subdivisionUpperNegativeLoop p hd⟧ := by
  have h :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      (⟦GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)⟧ : π_ 2 X x) :=
    Quotient.sound (subdivisionUpperOrientation_homotopic p hd)
  exact
    h.trans
      (HomotopyGroup.inv_spec (i := (1 : Fin 2)) (p := subdivisionUpperNegativeLoop p hd)).symm

/-- The additive form of `subdivisionUpperOrientation_class`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_additiveClass {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((-·) : Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivisionUpperOrientation_class p hd)

/-- From `a = b + c` and `c = -d`, conclude `a = b - d`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_eq_sub_of_eq_add {A : Type*} [AddGroup A]
    {a b c d : A} (h : a = b + c) (hc : c = -d) : a = b - d :=
  h.trans ((congrArg (fun z => b + z) hc).trans (sub_eq_add_neg b d).symm)

/-- The upper negative loop equals the loop of its based triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeLoop p hd =
      basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  exact (subdivisionUpperNegativeBasedTriangle_loop_apply p hd u).symm

/-- The class of the upper positive based triangle is the negated upper negative
class. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveBasedTriangle_class_eq_neg
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) =
      -basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) := by
  unfold basedTriangleClass
  rw [← subdivisionUpperTriangleLoop_eq_basedTriangleLoop, ←
    subdivisionUpperNegativeLoop_eq_basedTriangleLoop]
  exact subdivisionUpperOrientation_additiveClass p hd

/-- `⟦p⟧` splits as the lower based-triangle class minus the upper negative one. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_basedTriangleClass_sub {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) -
        basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_basedTriangleClass_sum p hd)
    (subdivisionUpperPositiveBasedTriangle_class_eq_neg p hd)

/-- `⟦basedTrianglesLoop τ υ⟧` is `basedTriangleClass τ - basedTriangleClass υ`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_class {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x) =
      basedTriangleClass τ - basedTriangleClass υ := by
  have hd : ∀ t : (unitInterval), basedTrianglesLoop τ υ ![t, t] = x := by
    intro t
    have he : (![t, t] : Fin 2 → (unitInterval)) = fun _ => t := by
      funext i
      fin_cases i <;> rfl
    rw [he, basedTrianglesLoop_diagonal]
  have hl : subdivisionLowerBasedTriangle (basedTrianglesLoop τ υ) hd = τ :=
    Subtype.ext (basedTrianglesLoop_lower τ υ)
  have hu : subdivisionUpperNegativeBasedTriangle (basedTrianglesLoop τ υ) hd = υ :=
    Subtype.ext (basedTrianglesLoop_upper τ υ)
  simpa only [hl, hu] using subdivision_basedTriangleClass_sub (basedTrianglesLoop τ υ) hd

/-- `⟦p⟧ = ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_quotient {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (⟦p⟧ : π_ 2 X x) =
      ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧ :=
  Quotient.sound (squareNormalization_homotopic p)

/-- `basedTriangleClass (lower) - basedTriangleClass (upper) = ⟦p⟧` additively. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    basedTriangleClass (squareNormalizedLowerTriangle p) -
        basedTriangleClass (squareNormalizedUpperTriangle p) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  have h := congrArg Additive.ofMul (squareNormalization_quotient p)
  exact
    (basedTrianglesLoop_class (squareNormalizedLowerTriangle p)
          (squareNormalizedUpperTriangle p)).symm.trans
      h.symm

/-- `triangleClassOperator` of the square chain of `p` is `⟦p⟧` additively. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_squareChain {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    triangleClassOperator x (Hurewicz.DegreeTwo.squareChain p) = Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [squareChain_two_triangles, map_sub, triangleClassOperator_simplex,
    triangleClassOperator_simplex,
    normalizedTriangle_of_verticesBased x _ (lowerSquareTriangle_verticesBased p),
    normalizedTriangle_of_verticesBased x _ (upperSquareTriangle_verticesBased p)]
  exact squareNormalization_class p

/-- `hurewiczInverse ∘ hurewiczMap` on a `⟦p⟧` representative returns `⟦p⟧`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_hurewiczMap_mk {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczInverse x (Hurewicz.DegreeTwo.hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [Hurewicz.DegreeTwo.hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact triangleClassOperator_squareChain x p

/-- `hurewiczInverse` of `hurewiczMap` of a class returns the class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczInverse x (Hurewicz.DegreeTwo.hurewiczMap x a) = a := by
  change
    hurewiczInverse x (Hurewicz.DegreeTwo.hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

/-- `hurewiczInverse ∘ hurewiczMap` is the identity on `Additive (π_2)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_comp_hurewiczMap {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (hurewiczInverse x).comp (Hurewicz.DegreeTwo.hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a
