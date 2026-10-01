/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.SymmetricForm

/-!
# Signed coordinates for a nondegenerate symmetric form

Sylvester's law of inertia in the form needed by the Morse lemma: if `H` is a symmetric bilinear
form on a finite-dimensional real space `E` that is nondegenerate (`H : E → E →L[ℝ] ℝ`
bijective), there are weights `w i ∈ {-1, 1}` and a linear isomorphism
`C : E ≃ ℝ^(finrank E)` with `(1/2) H x x = ∑ i, w i * (C x i) ^ 2`
(`SmoothMorseLemma.exists_signed_coordinates`, `SmoothMorseLemma.exists_signed_diffeomorph`).
The proof applies Mathlib's `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` to the
quadratic form `SmoothMorseLemma.halfHessianQuadratic H`.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The quadratic form of half the Hessian. -/
def SmoothMorseLemma.halfHessianQuadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Bilinear E) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((1 / 2 : ℝ) • H.toLinearMap₁₂)

/-- The half-Hessian quadratic form evaluates the Hessian. -/
@[simp]
theorem SmoothMorseLemma.halfHessianQuadratic_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (x : E) : halfHessianQuadratic H x = (1 / 2 : ℝ) * H x x :=
  rfl

/-- The half-Hessian form is associated to the Hessian. -/
theorem SmoothMorseLemma.halfHessianQuadratic_associated {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x) :
    QuadraticMap.associated (halfHessianQuadratic H) = (1 / 2 : ℝ) • H.toLinearMap₁₂ := by
  apply QuadraticMap.associated_left_inverse ℝ (B₁ := (1 / 2 : ℝ) • H.toLinearMap₁₂)
  intro x y
  change (1 / 2 : ℝ) * H x y = (1 / 2 : ℝ) * H y x
  rw [hH]

/-- The nondegenerate half-Hessian form separates points. -/
theorem SmoothMorseLemma.halfHessianQuadratic_separatingLeft {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHinj : Function.Injective H) :
    (QuadraticMap.associated (halfHessianQuadratic H)).SeparatingLeft := by
  rw [halfHessianQuadratic_associated H hH]
  intro x hx
  apply hHinj
  ext y
  have hxy := hx y
  change (1 / 2 : ℝ) * H x y = 0 at hxy
  simpa using (mul_eq_zero.mp hxy).resolve_left (by norm_num)

/-- Signed coordinates diagonalizing the Hessian exist. -/
theorem SmoothMorseLemma.exists_signed_coordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ C : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
          ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, ⟨C⟩⟩ :=
    (halfHessianQuadratic H).equivalent_one_neg_one_weighted_sum_squared
      (halfHessianQuadratic_separatingLeft H hH hHbij.1)
  refine ⟨w, hw, C.toLinearEquiv.toContinuousLinearEquiv, ?_⟩
  intro x
  change (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2
  simpa only [QuadraticMap.weightedSumSquares_apply, halfHessianQuadratic_apply, smul_eq_mul,
    pow_two] using (C.map_app x).symm

/-- A signed coordinate diffeomorphism exists. -/
theorem SmoothMorseLemma.exists_signed_diffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ C : E ≃ₘ[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
          C 0 = 0 ∧ ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, C, hC⟩ := exists_signed_coordinates H hH hHbij
  exact ⟨w, hw, C.toDiffeomorph, C.map_zero, hC⟩
