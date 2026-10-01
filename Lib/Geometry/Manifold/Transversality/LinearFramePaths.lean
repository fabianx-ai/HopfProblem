/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Path components of the real general linear group

`SL(n, ℝ)` is path connected for `n ≥ 2`, every matrix being a product of transvections (and
`diag(a, a⁻¹)` a product of six transvections); consequently the matrices with determinant of a
given sign form a path-connected set, so `GL(n, ℝ)` has exactly two path components.

## Main results

* `LinearFramePaths.joined_one_specialLinear`
* `LinearFramePaths.joined_determinantComponent`

## References

* cf. [M. Hirsch, *Differential Topology*][hirsch76], Ch. 8 §3, where the two components of
  `GL(n, ℝ)` enter the disc theorem.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- The elementary diagonal matrix `diag(a, a⁻¹)` in the coordinates `i, j` is a product of six
transvections.
-/
theorem LinearFramePaths.diag2n_decompose {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (a : ℝ) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
                Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
              Matrix.SpecialLinearGroup.transvection hij a *
            Matrix.SpecialLinearGroup.transvection hij (-1) *
          Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  change
    Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) =
      (1 + Matrix.single i j a) * (1 + Matrix.single j i (-a⁻¹)) * (1 + Matrix.single i j a) *
            (1 + Matrix.single i j (-1)) *
          (1 + Matrix.single j i 1) *
        (1 + Matrix.single i j (-1))
  simp only [mul_add, add_mul, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;>
      by_cases hlj : l = j <;>
    simp_all [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Every transvection is joined to the identity by a path in `SL(n, ℝ)`. -/
theorem LinearFramePaths.joined_one_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) (Matrix.SpecialLinearGroup.transvection hij a) := by
  refine
    ⟨{  toFun := fun t => Matrix.SpecialLinearGroup.transvection hij ((t : ℝ) * a)
        continuous_toFun := ?_
        source' := by simp
        target' := by simp }⟩
  apply Continuous.subtype_mk
  change Continuous (fun t : unitInterval => (1 : Matrix ι ι ℝ) + Matrix.single i j ((t : ℝ) * a))
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · simp only [h, and_self, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

/-- `SL(n, ℝ)` is path connected for `n ≥ 2`: every matrix of determinant one is joined to the
identity.
-/
theorem LinearFramePaths.joined_one_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (A : Matrix.SpecialLinearGroup ι ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) A := by
  apply
    Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Joined (1 : Matrix.SpecialLinearGroup ι ℝ) A) A
  · intro i j hij a ha
    rw [diag2n_decompose hij a ha]
    have hmul {A B : Matrix.SpecialLinearGroup ι ℝ} (hA : Joined 1 A) (hB : Joined 1 B) :
      Joined 1 (A * B) := by simpa only [one_mul] using hA.mul hB
    exact
      hmul
        (hmul
          (hmul
            (hmul (hmul (joined_one_transvection hij a) (joined_one_transvection hij.symm (-a⁻¹)))
              (joined_one_transvection hij a))
            (joined_one_transvection hij (-1)))
          (joined_one_transvection hij.symm 1))
        (joined_one_transvection hij (-1))
  · exact fun i j hij a => joined_one_transvection hij a
  · intro A B hA hB
    simpa only [one_mul] using hA.mul hB


/-- The diagonal matrix with entry `a` in position `i` and `1` elsewhere. -/
def LinearFramePaths.scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) (a : ℝ) :
    Matrix ι ι ℝ :=
  Matrix.diagonal (fun k => if k = i then a else 1)

/-- The determinant of the elementary scalar diagonal matrix is its entry. -/
theorem LinearFramePaths.det_scalarDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a : ℝ) : Matrix.det (scalarDiagonal i a) = a := by simp [scalarDiagonal, Matrix.det_diagonal]

/-- Elementary scalar diagonal matrices multiply by multiplying their entries. -/
theorem LinearFramePaths.scalarDiagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a b : ℝ) : scalarDiagonal i a * scalarDiagonal i b = scalarDiagonal i (a * b) := by
  rw [scalarDiagonal, scalarDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

/-- The elementary scalar diagonal matrix with entry one is the identity. -/
theorem LinearFramePaths.scalarDiagonal_one {ι : Type*} [DecidableEq ι] (i : ι) :
    scalarDiagonal i 1 = 1 := by simp [scalarDiagonal]

/-- The elementary scalar diagonal matrix depends continuously on its entry. -/
theorem LinearFramePaths.continuous_scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) :
    Continuous (scalarDiagonal i) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [scalarDiagonal, Matrix.diagonal_apply]
  by_cases hkl : k = l
  · simp only [hkl, ite_true]
    by_cases hli : l = i
    · simp only [hli, ite_true]
      fun_prop
    · simp only [hli, ite_false]
      fun_prop
  · simp only [hkl, ite_false]
    fun_prop

/-- The open set of matrices whose determinant has a prescribed sign, one of the two components of
`GL(n, ℝ)` when `σ = ±1`.
-/
def LinearFramePaths.determinantComponent {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ℝ) :
    TopologicalSpace.Opens (Matrix ι ι ℝ) :=
  ⟨{A | 0 < σ * Matrix.det A},
    isOpen_lt continuous_const (continuous_const.mul continuous_id.matrix_det)⟩

/-- The elementary scalar diagonal matrix with the same determinant as the given matrix, a normal
form in its determinant component.
-/
def LinearFramePaths.diagonalPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {σ : ℝ}
    (A : determinantComponent (ι := ι) σ) : determinantComponent (ι := ι) σ :=
  ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)),
    by
    change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)))
    rw [det_scalarDiagonal]
    exact A.property⟩

/-- For `n ≥ 2` a matrix is joined inside its determinant component to the elementary scalar
diagonal matrix of the same determinant.
-/
theorem LinearFramePaths.joined_diagonal_to_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (i : ι) {σ : ℝ} (A : determinantComponent (ι := ι) σ) :
    Joined (diagonalPoint i A) A := by
  have ha : Matrix.det (A : Matrix ι ι ℝ) ≠ 0 := by
    intro hz
    have hh : 0 < σ * Matrix.det (A : Matrix ι ι ℝ) := A.property
    rw [hz, MulZeroClass.mul_zero] at hh
    exact lt_irrefl _ hh
  let N : Matrix.SpecialLinearGroup ι ℝ :=
    ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ), by
      rw [Matrix.det_mul, det_scalarDiagonal, inv_mul_cancel₀ ha]⟩
  let ψ : Matrix.SpecialLinearGroup ι ℝ → determinantComponent (ι := ι) σ := fun L =>
    ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * (L : Matrix ι ι ℝ),
      by
      change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * L.val)
      rw [Matrix.det_mul, det_scalarDiagonal, L.property, mul_one]
      exact A.property⟩
  have hψ : Continuous ψ := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have h0 : ψ 1 = diagonalPoint i A := by
    apply Subtype.ext
    change scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * 1 = _
    rw [mul_one]
    rfl
  have h1 : ψ N = A := by
    apply Subtype.ext
    change
      scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) *
          (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ)) =
        _
    rw [← mul_assoc, scalarDiagonal_mul, mul_inv_cancel₀ ha, scalarDiagonal_one, one_mul]
  have h := (joined_one_specialLinear N).map hψ
  rwa [h0, h1] at h

/-- Two elementary scalar diagonal matrices in the same determinant component are joined by a path
in it.
-/
theorem LinearFramePaths.joined_diagonal_points {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) {σ : ℝ} (A B : determinantComponent (ι := ι) σ) :
    Joined (diagonalPoint i A) (diagonalPoint i B) := by
  let g := fun t : unitInterval =>
    (1 - (t : ℝ)) * Matrix.det (A : Matrix ι ι ℝ) + (t : ℝ) * Matrix.det (B : Matrix ι ι ℝ)
  have hg : Continuous g := by fun_prop
  have hpos (t : unitInterval) : 0 < σ * g t := by
    have hh :=
      (convex_Ioi (0 : ℝ)) A.property B.property (sub_nonneg.mpr t.property.2) t.property.1
        (show 1 - (t : ℝ) + (t : ℝ) = 1 by ring)
    change
      0 <
        (1 - (t : ℝ)) * (σ * Matrix.det (A : Matrix ι ι ℝ)) +
          (t : ℝ) * (σ * Matrix.det (B : Matrix ι ι ℝ)) at hh
    convert hh using 1
    dsimp only [g]
    ring
  refine
    ⟨{  toFun := fun t =>
          ⟨scalarDiagonal i (g t),
            by
            change 0 < σ * Matrix.det (scalarDiagonal i (g t))
            rw [det_scalarDiagonal]
            exact hpos t⟩
        continuous_toFun :=
          ((continuous_scalarDiagonal i).comp hg).subtype_mk
            (fun t => by
              change 0 < σ * Matrix.det (scalarDiagonal i (g t))
              rw [det_scalarDiagonal]
              exact hpos t)
        source' := ?_
        target' := ?_ }⟩
  · apply Subtype.ext
    simp [g, diagonalPoint]
  · apply Subtype.ext
    simp [g, diagonalPoint]

/-- For `n ≥ 2` the set of matrices of a given determinant sign is path connected; so `GL(n, ℝ)` has
exactly the two components cut out by the sign of the determinant.
-/
theorem LinearFramePaths.joined_determinantComponent {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nontrivial ι] {σ : ℝ} (A B : determinantComponent (ι := ι) σ) : Joined A B :=
  by
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact
    (joined_diagonal_to_matrix i A).symm.trans
      ((joined_diagonal_points i A B).trans (joined_diagonal_to_matrix i B))
