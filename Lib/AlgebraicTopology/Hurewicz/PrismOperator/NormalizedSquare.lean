/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.TwoTriangles
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.VertexEdgeStraightening
/-!
# Normalizing a based square to a pair of based triangles

A based square `p` is homotopic rel boundary to the square glued from two based triangles
along the diagonal (`squareNormalization_homotopic`): the lower and upper triangles of `p`
are vertex-based, their edge straightenings are homotopies that agree on the diagonal and are
constant on the outer edges, and gluing two such triangle homotopies along the diagonal gives a
homotopy of based squares (`gluedTriangleHomotopy`).  The glued square of two based triangles
`τ`, `υ` is `basedTrianglesLoop τ υ`.  This is the reduction of an arbitrary square to based
triangles in this development's proof of the degree-two Hurewicz theorem (statement: Hatcher,
Thm 4.32; the argument is recorded in `Lib/docs/C.md`).

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopyMap`, `gluedTriangleHomotopy`.
* `Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop`, `basedTrianglesLoop_lower`,
  `basedTrianglesLoop_upper`, `basedTrianglesHomotopy_of_faces`.
* `Hurewicz.DegreeTwo.SimplyConnected.squareNormalizedLowerTriangle`,
  `squareNormalizedUpperTriangle`, `squareNormalizationHomotopy`,
  `squareNormalization_homotopic`.
-/

open Set Function Topology

noncomputable section

/-! ### Normalized squares -/

/-- The lower square triangle of `p` is vertex-based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp lowerSquareTriangle) := by
  intro i
  change p (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨1, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

/-- The upper square triangle of `p` is vertex-based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp upperSquareTriangle) := by
  intro i
  change p (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

/-- The face-`1` restrictions of the lower and upper square triangles of `p` agree. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareTriangles_diagonal {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).comp (SingularChains.simplexFace 1 1) =
      (p.val.comp upperSquareTriangle).comp (SingularChains.simplexFace 1 1) := by
  apply ContinuousMap.ext
  intro s
  change
    p.val (lowerSquareTriangle (SingularChains.simplexFace 1 1 s)) =
      p.val (upperSquareTriangle (SingularChains.simplexFace 1 1 s))
  apply congrArg p.val
  funext i
  apply Subtype.ext
  fin_cases i
  · change
      (lowerSquareTriangle (SingularChains.simplexFace 1 1 s) 0 : ℝ) =
        (upperSquareTriangle (SingularChains.simplexFace 1 1 s) 0 : ℝ)
    rw [lowerSquareTriangle_zero, upperSquareTriangle_zero, SingularChains.simplexFace_apply_self,
      zero_add]
  · change
      (lowerSquareTriangle (SingularChains.simplexFace 1 1 s) 1 : ℝ) =
        (upperSquareTriangle (SingularChains.simplexFace 1 1 s) 1 : ℝ)
    rw [lowerSquareTriangle_one, upperSquareTriangle_one, SingularChains.simplexFace_apply_self,
      zero_add]

/-- For `i ≠ 1`, face `i` of the lower square triangle of `p` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_outerFace {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp lowerSquareTriangle).comp (SingularChains.simplexFace 1 i) =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (SingularChains.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (SingularChains.simplexFace 1 0 s) 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    have h1 : SingularChains.simplexFace 1 0 s 1 = s 0 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 0
    have h2 : SingularChains.simplexFace 1 0 s 2 = s 1 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (SingularChains.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (SingularChains.simplexFace 1 2 s) 1 : ℝ) = 0
    rw [lowerSquareTriangle_one, SingularChains.simplexFace_apply_self]

/-- For `i ≠ 1`, face `i` of the upper square triangle of `p` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_outerFace {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp upperSquareTriangle).comp (SingularChains.simplexFace 1 i) =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (SingularChains.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (SingularChains.simplexFace 1 0 s) 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    have h1 : SingularChains.simplexFace 1 0 s 1 = s 0 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 0
    have h2 : SingularChains.simplexFace 1 0 s 2 = s 1 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (SingularChains.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (SingularChains.simplexFace 1 2 s) 0 : ℝ) = 0
    rw [upperSquareTriangle_zero, SingularChains.simplexFace_apply_self]

/-- For `t 1 ≤ t 0`, `lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 1 : ℝ) ≤ t 0) : lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 0 : ℝ) = (t 0 : ℝ)
    rw [lowerSquareTriangle_zero, triangleQuotient_one, triangleQuotient_two]
    ring
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 1 : ℝ) = (t 1 : ℝ)
    rw [lowerSquareTriangle_one, triangleQuotient_two, min_eq_right h]

/-- For `t 0 ≤ t 1`, `upperSquareTriangle (triangleQuotient (t 1, t 0)) = t`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 0 : ℝ) ≤ t 1) : upperSquareTriangle (triangleQuotient (t 1, t 0)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 0 : ℝ) = (t 0 : ℝ)
    rw [upperSquareTriangle_zero, triangleQuotient_two, min_eq_right h]
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 1 : ℝ) = (t 1 : ℝ)
    rw [upperSquareTriangle_one, triangleQuotient_one, triangleQuotient_two]
    ring

/-- The perimeter of the triangle quotient on the lower half. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_perimeter_of_le
    (z : (unitInterval) × (unitInterval)) (hper : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1)
    (hle : (z.2 : ℝ) ≤ z.1) : triangleQuotient z 0 = 0 ∨ triangleQuotient z 2 = 0 := by
  rcases hper with h | h | h | h
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_left z.2.property.1
  · left
    rw [triangleQuotient_zero, h]
    norm_num
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_right z.1.property.1
  · have hu : z.1 = 1 := Subtype.ext (le_antisymm z.1.property.2 (by simpa only [h] using hle))
    left
    rw [triangleQuotient_zero, hu]
    norm_num

/-- A point of the `Fin 2` cube boundary has some coordinate equal to `0` or `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.cubeBoundary_productBoundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : t 0 = 0 ∨ t 0 = 1 ∨ t 1 = 0 ∨ t 1 = 1 := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hi))

/-- Glue `L` and `U` along the diagonal face `s 1 = 0`. -/
def Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopyMap {X : Type} [TopologicalSpace X]
    (L U : C((unitInterval) × SingularChains.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) :
    C((unitInterval) × (Fin 2 → (unitInterval)), X)
    where
  toFun
    z :=
    if (z.2 1 : ℝ) ≤ z.2 0 then L (z.1, triangleQuotient (z.2 0, z.2 1))
    else U (z.1, triangleQuotient (z.2 1, z.2 0))
  continuous_toFun := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro z h
    have he : z.2 1 = z.2 0 := Subtype.ext h
    have hq : triangleQuotient (z.2 0, z.2 1) 1 = 0 := by
      simp only [triangleQuotient_one, he, min_self, sub_self]
    simpa only [he] using hdiag z.1 (triangleQuotient (z.2 0, z.2 1)) hq

/-- The glued map is `x` on the square boundary, given the boundary hypotheses on `L` and `U`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopyMap_boundary {X : Type}
    [TopologicalSpace X] (L U : C((unitInterval) × SingularChains.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (x : X)
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x) (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x)
    (r : (unitInterval)) (t : Fin 2 → (unitInterval)) (ht : t ∈ Cube.boundary (Fin 2)) :
    gluedTriangleHomotopyMap L U hdiag (r, t) = x := by
  have hp := cubeBoundary_productBoundary t ht
  change (if (t 1 : ℝ) ≤ t 0 then _ else _) = x
  split_ifs with h
  · exact hL r _ (triangleQuotient_perimeter_of_le (t 0, t 1) hp h)
  · have hp' : t 1 = 0 ∨ t 1 = 1 ∨ t 0 = 0 ∨ t 0 = 1 := by
      rcases hp with hp | hp | hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inr (Or.inr hp))
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    exact hU r _ (triangleQuotient_perimeter_of_le (t 1, t 0) hp' (le_of_not_ge h))

/-- The `HomotopyRel` from `p` to `q` glued from lower- and upper-triangle homotopies. -/
def Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x}
    (L : (p.val.comp lowerSquareTriangle).Homotopy (q.val.comp lowerSquareTriangle))
    (U : (p.val.comp upperSquareTriangle).Homotopy (q.val.comp upperSquareTriangle))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel q.val (Cube.boundary (Fin 2))
    where
  toContinuousMap := gluedTriangleHomotopyMap L.toContinuousMap U.toContinuousMap hdiag
  map_zero_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = p.val t
    split_ifs with h
    · change L (0, triangleQuotient (t 0, t 1)) = p.val t
      rw [L.apply_zero]
      change p.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = p.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (0, triangleQuotient (t 1, t 0)) = p.val t
      rw [U.apply_zero]
      change p.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = p.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  map_one_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = q.val t
    split_ifs with h
    · change L (1, triangleQuotient (t 0, t 1)) = q.val t
      rw [L.apply_one]
      change q.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = q.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (1, triangleQuotient (t 1, t 0)) = q.val t
      rw [U.apply_one]
      change q.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = q.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  prop' r t
    ht :=
    (gluedTriangleHomotopyMap_boundary L.toContinuousMap U.toContinuousMap hdiag x hL hU r t
          ht).trans
      (GenLoop.boundary p t ht).symm

/-- Two based triangles agree on the diagonal edge (the `s 1 = 0` face where both are
constantly the basepoint). -/
private theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangles_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ υ : BasedTriangle x) (s : SingularChains.Simplex 2)
    (hs : s 1 = 0) : τ.val s = υ.val s :=
  (τ.property s ⟨1, hs⟩).trans (υ.property s ⟨1, hs⟩).symm

/-- The based square loop gluing `τ` on the lower triangle and `υ` on the upper triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ υ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨(gluedTriangleHomotopyMap (τ.val.comp ContinuousMap.snd) (υ.val.comp ContinuousMap.snd)
          (fun _ => basedTriangles_diagonal τ υ)).comp
      ⟨fun t => ((0 : (unitInterval)), t), by fun_prop⟩,
    by
    intro t ht
    exact
      gluedTriangleHomotopyMap_boundary _ _ (fun _ => basedTriangles_diagonal τ υ) x
        (fun _ s hs => τ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
        (fun _ s hs => υ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩))) 0 t ht⟩

/-- `basedTrianglesLoop τ υ` is `τ` below the diagonal and `υ` above it. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_apply {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (t : Fin 2 → (unitInterval)) :
    basedTrianglesLoop τ υ t =
      if (t 1 : ℝ) ≤ t 0 then τ.val (triangleQuotient (t 0, t 1))
      else υ.val (triangleQuotient (t 1, t 0)) :=
  rfl

/-- `basedTrianglesLoop` sends diagonal points to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (u : (unitInterval)) :
    basedTrianglesLoop τ υ (fun _ => u) = x := by
  rw [basedTrianglesLoop_apply, if_pos le_rfl]
  apply τ.property
  exact ⟨1, by simp only [triangleQuotient_one, min_self, sub_self]⟩

/-- The lower triangle restriction of `basedTrianglesLoop τ υ` is `τ`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp lowerSquareTriangle = τ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (lowerSquareTriangle s) = τ.val s
  rw [basedTrianglesLoop_apply]
  have hle : (lowerSquareTriangle s 1 : ℝ) ≤ lowerSquareTriangle s 0 := by
    rw [lowerSquareTriangle_zero, lowerSquareTriangle_one]
    exact le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  rw [if_pos hle]
  change
    τ.val (triangleQuotient ((lowerProductTriangle s).1, (lowerProductTriangle s).2)) = τ.val s
  exact congrArg τ.val (ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s)

/-- The triangle quotient of the swapped upper-square-triangle pair returns the original
simplex: the upper triangle of the square covers the standard triangle. -/
private theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_swapped_upper
    (s : SingularChains.Simplex 2) :
    triangleQuotient (upperSquareTriangle s 1, upperSquareTriangle s 0) = s := by
  have hpair : (upperSquareTriangle s 1, upperSquareTriangle s 0) = lowerProductTriangle s := by
    apply Prod.ext <;> apply Subtype.ext
    · rw [upperSquareTriangle_one, lowerProductTriangle_fst]
    · rw [upperSquareTriangle_zero, lowerProductTriangle_snd]
  rw [hpair]
  exact ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s

/-- The upper triangle restriction of `basedTrianglesLoop τ υ` is `υ`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp upperSquareTriangle = υ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (upperSquareTriangle s) = υ.val s
  rw [basedTrianglesLoop_apply]
  split_ifs with h
  · have hs : s 1 = 0 := by
      rw [upperSquareTriangle_zero, upperSquareTriangle_one] at h
      exact le_antisymm (by linarith) (stdSimplex.zero_le s 1)
    have he : upperSquareTriangle s 0 = upperSquareTriangle s 1 := by
      apply Subtype.ext
      rw [upperSquareTriangle_zero, upperSquareTriangle_one, hs, zero_add]
    have hq : triangleQuotient (upperSquareTriangle s 0, upperSquareTriangle s 1) = s := by
      simpa only [he] using triangleQuotient_swapped_upper s
    rw [hq]
    exact basedTriangles_diagonal τ υ s hs
  · rw [triangleQuotient_swapped_upper]

/-- The `HomotopyRel` from `p` to `basedTrianglesLoop τ υ` assembled from triangle homotopies `L`, `U`. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  gluedTriangleHomotopy (L.cast rfl (basedTrianglesLoop_lower τ υ).symm)
    (U.cast rfl (basedTrianglesLoop_upper τ υ).symm) hdiag hL hU

/-- If `P` holds on all points of face `i`, it holds at every `s` with `s i = 0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleProperty_of_face
    {P : SingularChains.Simplex 2 → Prop} (i : Fin 3)
    (h : ∀ u, P (SingularChains.simplexFace 1 i u)) (s : SingularChains.Simplex 2) (hs : s i = 0) :
    P s := by simpa only [simplexFace_inverse] using h (simplexFaceInverse 1 i ⟨s, hs⟩)

/-- The `HomotopyRel` from `p` to `basedTrianglesLoop τ υ` given homotopies to `τ` and `υ` on the two triangles. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesHomotopy_of_faces {X : Type} [TopologicalSpace X]
    {x : X} {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag :
      ∀ r s, L (r, SingularChains.simplexFace 1 1 s) = U (r, SingularChains.simplexFace 1 1 s))
    (hL : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, L (r, SingularChains.simplexFace 1 i s) = x)
    (hU : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, U (r, SingularChains.simplexFace 1 i s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy τ υ L U
    (fun r s hs => triangleProperty_of_face (P := fun s => L (r, s) = U (r, s)) 1 (hdiag r) s hs)
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => L (r, s) = x) 0 (hL r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => L (r, s) = x) 2 (hL r 2 (by decide)) s))
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => U (r, s) = x) 0 (hU r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => U (r, s) = x) 2 (hU r 2 (by decide)) s))

/-- The edge-straightened `BasedTriangle` of the lower square triangle of `p`. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizedLowerTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp lowerSquareTriangle)
    (lowerSquareTriangle_verticesBased p)

/-- The edge-straightened `BasedTriangle` of the upper square triangle of `p`. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizedUpperTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp upperSquareTriangle)
    (upperSquareTriangle_verticesBased p)

/-- The homotopy from a vertex-based `2`-simplex to its edge-straightened triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizationTriangleHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(SingularChains.Simplex 2, X))
    (h : VerticesBased x 2 smp) : smp.Homotopy (edgeStraightenedTriangle x smp h).val
    where
  toContinuousMap := triangleEdgeStraighteningHomotopy x smp
  map_zero_left := triangleEdgeStraighteningHomotopy_zero x smp
  map_one_left _ := rfl

/-- The homotopy from `p ∘ lowerSquareTriangle` to its normalized triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareLowerNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).Homotopy (squareNormalizedLowerTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (lowerSquareTriangle_verticesBased p)

/-- The homotopy from `p ∘ upperSquareTriangle` to its normalized triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareUpperNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp upperSquareTriangle).Homotopy (squareNormalizedUpperTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (upperSquareTriangle_verticesBased p)

/-- On face `i`, the triangle edge-straightening homotopy is `edgeStraighteningHomotopy` of that face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_edge_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(SingularChains.Simplex 2, X))
    (i : Fin 3) (r : (unitInterval)) (s : SingularChains.Simplex 1) :
    triangleEdgeStraighteningHomotopy x smp (r, SingularChains.simplexFace 1 i s) =
      edgeStraighteningHomotopy x (smp.comp (SingularChains.simplexFace 1 i)) (r, s) :=
  DFunLike.congr_fun (triangleEdgeStraighteningHomotopy_face x smp i) (r, s)

/-- The lower and upper normalization homotopies agree on face `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_diagonal {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (s : SingularChains.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, SingularChains.simplexFace 1 1 s) =
      squareUpperNormalizationHomotopy p (r, SingularChains.simplexFace 1 1 s) := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, SingularChains.simplexFace 1 1 s) =
      triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, SingularChains.simplexFace 1 1 s)
  rw [squareNormalization_edge_face, squareNormalization_edge_face, squareTriangles_diagonal]

/-- The lower normalization homotopy is `x` on outer faces `i ≠ 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareLowerNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : SingularChains.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, SingularChains.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, SingularChains.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, lowerSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

/-- The upper normalization homotopy is `x` on outer faces `i ≠ 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareUpperNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : SingularChains.Simplex 1) :
    squareUpperNormalizationHomotopy p (r, SingularChains.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, SingularChains.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, upperSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

/-- The `HomotopyRel` from `p` to the loop of its normalized lower/upper triangles. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizationHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)).val
      (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy_of_faces (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p) (squareLowerNormalizationHomotopy p)
    (squareUpperNormalizationHomotopy p) (squareNormalization_diagonal p)
    (squareLowerNormalization_outerFace p) (squareUpperNormalization_outerFace p)

/-- `p` is homotopic to `basedTrianglesLoop` of its normalized triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_homotopic {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    GenLoop.Homotopic p
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)) :=
  ⟨squareNormalizationHomotopy p⟩
