/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareRotation
/-!
# Based tetrahedra and the cyclic symmetry of based triangles

A based tetrahedron is a singular `3`-simplex sending the `1`-skeleton to the basepoint; its
four faces are based triangles.  Two quadrilateral fillings of the tetrahedron boundary,
`tetrahedronQuadrilateralA` and its quarter-shifted image, give based squares that are
homotopic rel boundary through the tetrahedron (`tetrahedronFillingsHomotopy`), hence have the
same class in `π_2` (`tetrahedronFillings_class`).  Cyclically permuting the vertices of a
based triangle does not change its class either (`basedTriangleClass_cyclic`), since the
permuted loop is homotopic to the quarter-turn rotation of the original.  These are the
geometric inputs to the boundary relation (the class of a based `3`-simplex boundary vanishes),
proved in `TetrahedronRelation`, of this development's proof of the degree-two Hurewicz theorem
(statement: Hatcher, Thm 4.32; the argument is recorded in `Lib/docs/C.md`).

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron`, `basedTetrahedronFace`,
  `BasedTetrahedron.ofFaces`.
* `Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend`: the affine blend of two points of
  a simplex, used for straight-line homotopies.
* `Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA`, `tetrahedronQuarterShift`,
  `tetrahedronQuadrilateralLoop`, `tetrahedronFillings_class`.
* `Hurewicz.DegreeTwo.SimplyConnected.triangleCyclicPermutation`, `cyclicBasedTriangle`,
  `basedTriangleClass_cyclic`.
-/

open Set Function Topology

noncomputable section

/-! ### Based tetrahedra and quadrilateral fillings -/

/-- The one-skeleton of the tetrahedron: points with at least two vanishing
barycentric coordinates. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronOneSkeleton : Set (SingularChains.Simplex 3) :=
  {s | ∃ i j : Fin 4, i ≠ j ∧ s i = 0 ∧ s j = 0}

/-- A based tetrahedron at `x`: a `3`-simplex map sending the one-skeleton to `x`. -/
def Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(SingularChains.Simplex 3, X) // ∀ s ∈ tetrahedronOneSkeleton, τ s = x }

/-- Each face map of the triangle lands in `triangleBoundary`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_triangleBoundary (i : Fin 4)
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    SingularChains.simplexFace 2 i s ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, SingularChains.simplexFace_apply_self 2 i s,
      (SingularChains.simplexFace_apply_succAbove 2 i s j).trans hj⟩

/-- The `i`-th face of a based tetrahedron, as a based triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedronFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTetrahedron x) (i : Fin 4) : BasedTriangle x :=
  ⟨τ.val.comp (SingularChains.simplexFace 2 i), fun s hs =>
    τ.property _ (simplexFace_triangleBoundary i s hs)⟩

/-- The linear blend between two simplex values of a tetrahedron. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend {n : ℕ} (t : (unitInterval))
    (a b : SingularChains.Simplex n) : SingularChains.Simplex n :=
  ⟨(1 - (t : ℝ)) • (a : Fin (n + 1) → ℝ) + (t : ℝ) • (b : Fin (n + 1) → ℝ),
    convex_stdSimplex ℝ _ a.property b.property (sub_nonneg.mpr t.property.2) t.property.1
      (by ring)⟩

/-- At `t = 0` the tetrahedron blend is the first map. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_zero {n : ℕ}
    (a b : SingularChains.Simplex n) : tetrahedronSimplexBlend 0 a b = a := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) * a i + (0 : ℝ) * b i = a i
  simp

/-- At `t = 1` the tetrahedron blend is the second map. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_one {n : ℕ}
    (a b : SingularChains.Simplex n) : tetrahedronSimplexBlend 1 a b = b := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) * a i + (1 : ℝ) * b i = b i
  simp

/-- Blending a simplex point with itself is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_self {n : ℕ} (t : (unitInterval))
    (a : SingularChains.Simplex n) : tetrahedronSimplexBlend t a a = a := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * a i + (t : ℝ) * a i = a i
  ring

/-- The blend of two tetrahedron maps as a continuous map on the cylinder. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlendMap {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] (f g : C(Y, SingularChains.Simplex n)) :
    C((unitInterval) × Y, SingularChains.Simplex n)
    where
  toFun p := tetrahedronSimplexBlend p.1 (f p.2) (g p.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change
      Continuous fun p : (unitInterval) × Y => (1 - (p.1 : ℝ)) * f p.2 i + (p.1 : ℝ) * g p.2 i
    have hf : Continuous fun p : (unitInterval) × Y => f p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
    have hg : Continuous fun p : (unitInterval) × Y => g p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (g.continuous.comp continuous_snd))
    exact
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hf).add
        ((continuous_subtype_val.comp continuous_fst).mul hg)

/-- A coordinate vanishing at both endpoints of a blend vanishes throughout. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate {n : ℕ}
    (t : (unitInterval)) (a b : SingularChains.Simplex n) (i : Fin (n + 1)) (ha : a i = 0)
    (hb : b i = 0) : tetrahedronSimplexBlend t a b i = 0 := by
  change (1 - (t : ℝ)) * a i + (t : ℝ) * b i = 0
  simp [ha, hb]

/-- Face `0` of a `2`-simplex is `![0, s 0, s 1, s 2]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_zero (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 0 s : Fin 4 → ℝ) = ![0, s 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_self 2 0 s
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 2

/-- Face `1` of a `2`-simplex is `![s 0, 0, s 1, s 2]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_one (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 1 s : Fin 4 → ℝ) = ![s 0, 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 0
  · exact SingularChains.simplexFace_apply_self 2 1 s
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 2

/-- Face `2` of a `2`-simplex is `![s 0, s 1, 0, s 2]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_two (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 2 s : Fin 4 → ℝ) = ![s 0, s 1, 0, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 1
  · exact SingularChains.simplexFace_apply_self 2 2 s
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 2

/-- Face `3` of a `2`-simplex is `![s 0, s 1, s 2, 0]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_three (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 3 s : Fin 4 → ℝ) = ![s 0, s 1, s 2, 0] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 2
  · exact SingularChains.simplexFace_apply_self 2 3 s

/-- A `3`-simplex map is a based tetrahedron if its one-skeleton restrictions are
constant at `x`. -/
def Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron.ofFaces {X : Type} [TopologicalSpace X]
    {x : X} (τ : C(SingularChains.Simplex 3, X))
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.triangleBoundary,
          (τ.comp (SingularChains.simplexFace 2 i)) s = x) :
    Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := Hurewicz.DegreeTwo.SimplyConnected.simplexFaceInverse 2 i ⟨s, hi⟩
    have ht : t ∈ Hurewicz.DegreeTwo.SimplyConnected.triangleBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (SingularChains.simplexFace 2 i t) = x at he
    rw [show SingularChains.simplexFace 2 i t = s from
        Hurewicz.DegreeTwo.SimplyConnected.simplexFace_inverse 2 i ⟨s, hi⟩] at he
    exact he⟩

/-- The first quadrilateral filling the tetrahedron boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 3)
    where
  toFun
    u :=
    ⟨![1 - Max.max (u 0 : ℝ) (u 1 : ℝ), (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        Min.min (u 0 : ℝ) (u 1 : ℝ), (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (u 1).property.1
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
        · rw [min_eq_left h, max_eq_right h]
          ring
        · rw [min_eq_right h, max_eq_left h]
          ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

/-- `tetrahedronQuadrilateralA` sends the square boundary into the tetrahedron `1`-skeleton. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_boundary
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u ∈ tetrahedronOneSkeleton := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hi
      refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 0).property.1]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 1).property.2,
          max_eq_left (u 1).property.2]
    · change u 1 = 1 at hi
      refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 0).property.2,
          max_eq_right (u 0).property.2]

/-- The diagonal of `tetrahedronQuadrilateralA` lands in the `1`-skeleton. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_diagonal (t : (unitInterval)) :
    tetrahedronQuadrilateralA ![t, t] ∈ tetrahedronOneSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩ <;> simp [DFunLike.coe, tetrahedronQuadrilateralA]

/-- The cyclic shift of a `3`-simplex, `s ↦ ![s 3, s 0, s 1, s 2]`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift :
    C(SingularChains.Simplex 3, SingularChains.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 3, s 0, s 1, s 2], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val

/-- The cyclic index permutation `Fin 4 ≃ Fin 4` behind `tetrahedronQuarterShift`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterIndex : Fin 4 ≃ Fin 4
    where
  toFun i := ![1, 2, 3, 0] i
  invFun i := ![3, 0, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- `tetrahedronQuarterShift s` has `s i` at index `tetrahedronQuarterIndex i`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_index (s : SingularChains.Simplex 3)
    (i : Fin 4) : tetrahedronQuarterShift s (tetrahedronQuarterIndex i) = s i := by
  fin_cases i <;> rfl

/-- `tetrahedronQuarterShift` preserves the tetrahedron `1`-skeleton. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_oneSkeleton
    (s : SingularChains.Simplex 3) (hs : s ∈ tetrahedronOneSkeleton) :
    tetrahedronQuarterShift s ∈ tetrahedronOneSkeleton := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact
    ⟨tetrahedronQuarterIndex i, tetrahedronQuarterIndex j, fun h =>
      hij (tetrahedronQuarterIndex.injective h), by simpa, by simpa⟩

/-- The based square loop `τ ∘ tetrahedronQuadrilateralA`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp tetrahedronQuadrilateralA, fun u hu =>
    τ.property _ (tetrahedronQuadrilateralA_boundary u hu)⟩

/-- The quadrilateral loop sends diagonal points to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuadrilateralA_diagonal t)

/-- The based square loop `τ ∘ tetrahedronQuadrilateralB`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedQuadrilateralLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA), fun u hu =>
    τ.property _
      (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_boundary u hu))⟩

/-- The shifted quadrilateral loop sends diagonal points to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronShiftedQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_diagonal t))

/-- The second quadrilateral filling the tetrahedron boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralB :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 3) :=
  (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA).comp quarterTurn

/-- The perimeter relation between the two quadrilateral fillings. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateral_perimeter
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u = tetrahedronQuadrilateralB u := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuarterShift_zero (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 0 = s 3 := rfl
  have tetrahedronQuarterShift_one (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 1 = s 0 := rfl
  have tetrahedronQuarterShift_two (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 2 = s 1 := rfl
  have tetrahedronQuarterShift_three (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 3 = s 2 := rfl
  have tetrahedronQuadrilateralB_apply (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralB u =
      tetrahedronQuarterShift (tetrahedronQuadrilateralA ![u 1, (unitInterval.symm) (u 0)]) :=
    rfl
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA u j = tetrahedronQuadrilateralB u j
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 1).property.2, max_eq_right (u 1).property.2,
          min_eq_left (u 1).property.1, max_eq_right (u 1).property.1]
    · change u 1 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 0).property.1, max_eq_left (u 0).property.1, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 1).property.2, max_eq_left (u 1).property.2,
          min_eq_right (u 1).property.1, max_eq_left (u 1).property.1]
    · change u 1 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 0).property.2, max_eq_right (u 0).property.2, (u 0).property.1]

/-- The homotopy between the two quadrilateral fillings of a based tetrahedron
(using `Subsingleton (π_2)`). -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronFillingsHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (tetrahedronQuadrilateralLoop τ).val.HomotopyRel
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (tetrahedronQuadrilateralA p.2)
        (tetrahedronQuadrilateralB p.2))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap tetrahedronQuadrilateralA tetrahedronQuadrilateralB).continuous
  map_zero_left
    u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (tetrahedronQuadrilateralB u)
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu := by
    change τ.val (tetrahedronSimplexBlend t _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [← tetrahedronQuadrilateral_perimeter u hu, tetrahedronSimplexBlend_self]

/-- The two quadrilateral fillings are homotopic rel boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronFillings_homotopic {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    GenLoop.Homotopic (tetrahedronQuadrilateralLoop τ)
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)) :=
  ⟨tetrahedronFillingsHomotopy τ⟩

/-- The two quadrilateral fillings have equal `π_2`-classes. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronFillings_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (⟦tetrahedronQuadrilateralLoop τ⟧ : π_ 2 X x) = ⟦tetrahedronShiftedQuadrilateralLoop τ⟧ :=
  (Quotient.sound (tetrahedronFillings_homotopic τ)).trans
    (rotatedSquareLoop_class (tetrahedronShiftedQuadrilateralLoop τ))

/-! ### Cyclic permutation of the triangle -/

/-- The cyclic permutation of the triangle's vertices. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleCyclicPermutation :
    C(SingularChains.Simplex 2, SingularChains.Simplex 2)
    where
  toFun
    s :=
    ⟨![s 1, s 2, s 0], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + s 2) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

/-- The cyclic permutation preserves the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleCyclicPermutation_boundary
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleCyclicPermutation s ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩

/-- The cyclic permutation of a based triangle is again based. -/
def Hurewicz.DegreeTwo.SimplyConnected.cyclicBasedTriangle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : BasedTriangle x :=
  ⟨τ.val.comp triangleCyclicPermutation, fun s hs =>
    τ.property _ (triangleCyclicPermutation_boundary s hs)⟩

/-- The cyclically permuted triangle quotient agrees at the common zero face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.cyclicTriangleQuotient_commonZero
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3,
      triangleCyclicPermutation (triangleCubeQuotient u) i = 0 ∧
        triangleCubeQuotient (quarterTurn u) i = 0 := by
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have triangleCyclicPermutation_zero (s : SingularChains.Simplex 2) :
    triangleCyclicPermutation s 0 = s 1 := rfl
  have triangleCyclicPermutation_one (s : SingularChains.Simplex 2) :
    triangleCyclicPermutation s 1 = s 2 := rfl
  have triangleCyclicPermutation_two (s : SingularChains.Simplex 2) :
    triangleCyclicPermutation s 2 = s 0 := rfl
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_left (u 1).property.1, min_eq_left (u 1).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩
      · simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_right (u 0).property.1]
      · simp [triangleCubeQuotient_apply, hi, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_two, hi,
          min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_zero, hi,
          min_eq_left (u 0).property.2]

/-- The blend of the cyclically permuted cube quotient with the quarter-turned quotient stays in the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.cyclicTriangleQuotient_blend_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronSimplexBlend t (triangleCyclicPermutation (triangleCubeQuotient u))
        (triangleCubeQuotient (quarterTurn u)) ∈
      triangleBoundary := by
  obtain ⟨i, hi, hj⟩ := cyclicTriangleQuotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

/-- The `HomotopyRel` from the cyclically permuted based-triangle loop to its rotated square loop. -/
def Hurewicz.DegreeTwo.SimplyConnected.cyclicTriangleLoopHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop (cyclicBasedTriangle τ)).val.HomotopyRel
      (rotatedSquareLoop (basedTriangleLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (triangleCyclicPermutation (triangleCubeQuotient p.2))
        (triangleCubeQuotient (quarterTurn p.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap (triangleCyclicPermutation.comp triangleCubeQuotient)
          (triangleCubeQuotient.comp quarterTurn)).continuous
  map_zero_left
    u := by
    change
      τ.val (tetrahedronSimplexBlend 0 _ _) =
        τ.val (triangleCyclicPermutation (triangleCubeQuotient u))
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (triangleCubeQuotient (quarterTurn u))
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu :=
    (τ.property _ (cyclicTriangleQuotient_blend_boundary t u hu)).trans
      ((basedTriangleLoop (cyclicBasedTriangle τ)).property u hu).symm

/-- Cyclic permutation of a based triangle preserves its `π_2`-class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleClass_cyclic {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    basedTriangleClass (cyclicBasedTriangle τ) = basedTriangleClass τ := by
  have h :
    GenLoop.Homotopic (basedTriangleLoop (cyclicBasedTriangle τ))
      (rotatedSquareLoop (basedTriangleLoop τ)) :=
    ⟨cyclicTriangleLoopHomotopy τ⟩
  have he :
    (⟦basedTriangleLoop (cyclicBasedTriangle τ)⟧ : π_ 2 X x) =
      ⟦rotatedSquareLoop (basedTriangleLoop τ)⟧ :=
    Quotient.sound h
  exact congrArg Additive.ofMul (he.trans (rotatedSquareLoop_class (basedTriangleLoop τ)))
