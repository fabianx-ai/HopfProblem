/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# Primitives of holomorphic functions on open rectangles

On an open rectangle `R = (a, b) × (c, d) ⊆ ℂ` a holomorphic function `f` has a primitive, given by
the wedge integral from a base point (Cauchy–Goursat for rectangles; Ahlfors, *Complex Analysis*,
Ch. 4 §1.3–1.4). If moreover `‖f‖ ≤ M` on `R`, the primitive is Lipschitz on the convex set `R` and
extends to a continuous (Lipschitz) function on `ℂ` with the same derivative on `R`; this continuous
extension to the closed rectangle is what the reflection argument across an edge uses.
-/

open Set Function Filter Topology

open scoped Interval NNReal

noncomputable section

/-- The open rectangle `(a, b) × (c, d)` in `ℂ`. -/
def RiemannBoundary.openRectangle (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d}

/-- The open rectangle is open. -/
theorem RiemannBoundary.isOpen_openRectangle (a b c d : ℝ) : IsOpen (openRectangle a b c d) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

/-- The open rectangle is convex. -/
theorem RiemannBoundary.convex_openRectangle (a b c d : ℝ) : Convex ℝ (openRectangle a b c d) :=
  ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).inter
    ((convex_halfSpace_im_gt c).inter (convex_halfSpace_im_lt d))

/-- For `z`, `w` in an open rectangle, the point `Re z + i Im w` lies in it. -/
theorem RiemannBoundary.mixed_mem_openRectangle {a b c d : ℝ} {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    z.re + w.im * Complex.I ∈ openRectangle a b c d := by
  simpa only [openRectangle, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] using
    And.intro hz.1 hw.2

/-- The rectangle `Complex.Rectangle z w` spanned by two points of an open rectangle lies in it. -/
theorem RiemannBoundary.rectangle_subset_openRectangle {a b c d : ℝ} {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    Complex.Rectangle z w ⊆ openRectangle a b c d :=
  Complex.Convex.rectangle_subset (convex_openRectangle a b c d) hz hw
    (mixed_mem_openRectangle hz hw) (mixed_mem_openRectangle hw hz)

/-- A horizontal segment lies in the rectangle. -/
theorem RiemannBoundary.horizontal_segment_subset {a b c d : ℝ} {x₁ x₂ y : ℝ}
    (h₁ : (x₁ : ℂ) + y * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * Complex.I ∈ openRectangle a b c d) :
    (fun x : ℝ => (x : ℂ) + y * Complex.I) '' [[x₁, x₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [Complex.horizontalSegment_eq x₁ x₂ y, Complex.Rectangle]

/-- A vertical segment lies in the rectangle. -/
theorem RiemannBoundary.vertical_segment_subset {a b c d : ℝ} {x y₁ y₂ : ℝ}
    (h₁ : (x : ℂ) + y₁ * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * Complex.I ∈ openRectangle a b c d) :
    (fun y : ℝ => (x : ℂ) + y * Complex.I) '' [[y₁, y₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [Complex.verticalSegment_eq x y₁ y₂, Complex.Rectangle]

/-- For `f` continuous and conservative on an open rectangle and `p`, `z`, `w` in it, `wedgeIntegral
p w f - wedgeIntegral p z f = wedgeIntegral z w f`. -/
theorem RiemannBoundary.wedgeIntegral_sub_wedgeIntegral_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (openRectangle a b c d))
    (hf : Complex.IsConservativeOn f (openRectangle a b c d)) {p z w : ℂ}
    (hp : p ∈ openRectangle a b c d) (hz : z ∈ openRectangle a b c d)
    (hw : w ∈ openRectangle a b c d) :
    Complex.wedgeIntegral p w f - Complex.wedgeIntegral p z f = Complex.wedgeIntegral z w f := by
  have integrableHoriz (x₁ x₂ y : ℝ) (h₁ : (x₁ : ℂ) + y * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * Complex.I ∈ openRectangle a b c d) :
    IntervalIntegrable (fun x : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume x₁
      x₂ :=
    ((hc.mono (horizontal_segment_subset h₁ h₂)).comp (by fun_prop)
        (Set.mapsTo_image _ _)).intervalIntegrable
  have integrableVert (x y₁ y₂ : ℝ) (h₁ : (x : ℂ) + y₁ * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * Complex.I ∈ openRectangle a b c d) :
    IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume y₁
      y₂ :=
    ((hc.mono (vertical_segment_subset h₁ h₂)).comp (by fun_prop)
        (Set.mapsTo_image _ _)).intervalIntegrable
  have hHoriz :
    (∫ x in p.re..w.re, f (x + p.im * Complex.I)) =
      (∫ x in p.re..z.re, f (x + p.im * Complex.I)) +
        (∫ x in z.re..w.re, f (x + p.im * Complex.I)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableHoriz
      · simpa only [Complex.re_add_im] using hp
      · exact mixed_mem_openRectangle hz hp
    · apply integrableHoriz
      · exact mixed_mem_openRectangle hz hp
      · exact mixed_mem_openRectangle hw hp
  have hVert :
    Complex.I * (∫ y in p.im..w.im, f (w.re + y * Complex.I)) =
      Complex.I * (∫ y in p.im..z.im, f (w.re + y * Complex.I)) +
        Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) := by
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hp
      · exact mixed_mem_openRectangle hw hz
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hz
      · simpa only [Complex.re_add_im] using hw
  have hRect :=
    hf (z.re + p.im * Complex.I) (w.re + z.im * Complex.I)
      (rectangle_subset_openRectangle (mixed_mem_openRectangle hz hp)
        (mixed_mem_openRectangle hw hz))
  have hBoundary :
    (∫ x in z.re..w.re, f (x + p.im * Complex.I)) -
            (∫ x in z.re..w.re, f (x + z.im * Complex.I)) +
          Complex.I * (∫ y in p.im..z.im, f (w.re + y * Complex.I)) -
        Complex.I * (∫ y in p.im..z.im, f (z.re + y * Complex.I)) =
      0 := by
    simpa [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] using hRect
  simp only [Complex.wedgeIntegral, smul_eq_mul]
  rw [hHoriz, hVert]
  linear_combination hBoundary

/-- For `f` holomorphic on an open rectangle containing `p`, `w ↦ wedgeIntegral p w f` has
derivative `f z` at every point `z` of the rectangle. -/
theorem RiemannBoundary.hasDerivAt_wedgeIntegral_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) {p z : ℂ} (hp : p ∈ openRectangle a b c d)
    (hz : z ∈ openRectangle a b c d) :
    HasDerivAt (fun w => Complex.wedgeIntegral p w f) (f z) z := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isOpen_openRectangle a b c d) z hz
  have hd : HasDerivAt (fun w => Complex.wedgeIntegral z w f) (f z) z :=
    (hf.isConservativeOn.mono hsub).hasDerivAt_wedgeIntegral (hf.continuousOn.mono hsub)
      (Metric.mem_ball_self hr)
  apply (hd.add_const (Complex.wedgeIntegral p z f)).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact
    sub_eq_iff_eq_add.mp
      (wedgeIntegral_sub_wedgeIntegral_openRectangle hf.continuousOn hf.isConservativeOn hp hz hw)

/-- A function holomorphic on an open rectangle has a primitive there. -/
theorem RiemannBoundary.isExactOn_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) :
    Complex.IsExactOn f (openRectangle a b c d) := by
  by_cases h : (openRectangle a b c d).Nonempty
  · obtain ⟨p, hp⟩ := h
    exact
      ⟨fun z => Complex.wedgeIntegral p z f, fun _ hz =>
        hasDerivAt_wedgeIntegral_openRectangle hf hp hz⟩
  · refine ⟨fun _ => 0, fun z hz => ?_⟩
    exact (h ⟨z, hz⟩).elim

/-- If `F' = f` on an open rectangle and `‖f‖₊ ≤ K` there, some `G : ℂ → ℂ` that is Lipschitz with
constant `lipschitzExtensionConstant ℂ * K` agrees with `F` on the rectangle and has `G' = f` there.
-/
theorem RiemannBoundary.exists_lipschitz_extension_primitive_openRectangle {a b c d : ℝ}
    {f : ℂ → ℂ} {F : ℂ → ℂ} {K : ℝ≥0} (hF : ∀ z ∈ openRectangle a b c d, HasDerivAt F (f z) z)
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ,
      LipschitzWith (lipschitzExtensionConstant ℂ * K) G ∧
        Set.EqOn F G (openRectangle a b c d) ∧
          ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  have hLip : LipschitzOnWith K F (openRectangle a b c d) :=
    (convex_openRectangle a b c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hF z hz).hasDerivWithinAt) hb
  obtain ⟨G, hG, heq⟩ := hLip.extend_finite_dimension
  refine ⟨G, hG, heq, fun z hz => ?_⟩
  apply (hF z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact (heq hw).symm

/-- A holomorphic function on an open rectangle with `‖f‖₊ ≤ K` has a primitive on the rectangle
that is continuous on `ℂ`. -/
theorem RiemannBoundary.exists_continuous_primitive_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    {K : ℝ≥0} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  obtain ⟨F, hF⟩ := isExactOn_openRectangle hf
  obtain ⟨G, hG, _, hd⟩ := exists_lipschitz_extension_primitive_openRectangle hF hb
  exact ⟨G, hG.continuous, hd⟩

/-- A holomorphic function on an open rectangle with `‖f‖ ≤ M` has a primitive on the rectangle that
is continuous on `ℂ`. -/
theorem RiemannBoundary.exists_continuous_primitive_openRectangle_of_norm_le {a b c d : ℝ}
    {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖ ≤ M) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  apply exists_continuous_primitive_openRectangle (K := M.toNNReal) hf
  intro z hz
  exact_mod_cast (hb z hz).trans (Real.le_coe_toNNReal M)
