/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.PrincipalRoot
import Shared.Proof.Analysis.Complex.RiemannMapping.SectorRoots

/-!
# Cube and rotated fourth roots for the corners of the project's triangles

Project material for `Hopf/Proof/LCP/AnalyticFillings.lean`: the corner-straightening maps at the
triangle corners of opening `π / 3` and `π / 4`, i.e. `principalRoot 3` (onto the sector
`0 < arg w < π / 3`) and `rotatedPrincipalRootFour = e^{-iπ/4} · principalRoot 4` (onto the sector
`-π/4 < arg w < 0`), with the images of the upper half-plane and of the real axis.
-/

open Set Function Filter Topology

noncomputable section

/-- The cube root of a nonnegative real has zero imaginary part. -/
theorem RiemannBoundary.principalRoot_three_ofReal_nonneg_im {x : ℝ} (hx : 0 ≤ x) :
    (principalRoot 3 (x : ℂ)).im = 0 := by
  rw [principalRoot_ofReal_nonneg 3 hx]
  exact Complex.ofReal_im _

/-- The cube root of a nonpositive real lies on the sector boundary. -/
theorem RiemannBoundary.principalRoot_three_ofReal_nonpos_boundary {x : ℝ} (hx : x ≤ 0) :
    Real.sqrt 3 * (principalRoot 3 (x : ℂ)).im = 3 * (principalRoot 3 (x : ℂ)).re := by
  rw [principalRoot_ofReal_nonpos 3 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  calc
    Real.sqrt 3 * ((-x) ^ (3 : ℝ)⁻¹ * (Real.sqrt 3 / 2)) =
        (Real.sqrt 3 * Real.sqrt 3) * ((-x) ^ (3 : ℝ)⁻¹ / 2) := by ring
    _ = _ := by rw [hsq]; ring

/-- The cube root maps the real axis to the sector boundary. -/
theorem RiemannBoundary.principalRoot_three_real_boundary {z : ℂ} (hz : z.im = 0) :
    (principalRoot 3 z).im = 0 ∨
      Real.sqrt 3 * (principalRoot 3 z).im = 3 * (principalRoot 3 z).re := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inl (principalRoot_three_ofReal_nonneg_im hp)
  · exact Or.inr (principalRoot_three_ofReal_nonpos_boundary hn)

/-- The quartic rotation is nonzero. -/
theorem RiemannBoundary.quarticRootRotation_ne_zero : quarticRootRotation ≠ 0 :=
  Complex.exp_ne_zero _

/-- The rotated fourth root maps the real axis to the sector boundary. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_real_boundary {z : ℂ} (hz : z.im = 0) :
    (rotatedPrincipalRootFour z).im = 0 ∨
      (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im = 0 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inr (rotatedPrincipalRootFour_ofReal_nonneg_boundary hp)
  · exact Or.inl (rotatedPrincipalRootFour_ofReal_nonpos_im hn)
