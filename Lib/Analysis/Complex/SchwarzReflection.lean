/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.Mobius
import Lib.Geometry.Manifold.Instances.RiemannSphere

/-!
# Schwarz reflection

Reflection of holomorphic functions across a line and across an arc of the unit circle
(`SchwarzReflection.*`, Ahlfors Ch. 3–4 §6.5): a function holomorphic on one side with real
boundary values extends across by reflection.

## Main definitions and results

* `SchwarzReflection.*` : the reflection extension across lines and circle arcs.

## References

* [Lars Ahlfors, *Complex Analysis*][ahlfors], Ch. 3–4, §6.5 (reflection)

## Tags

Schwarz reflection, holomorphic extension
-/



open Set Function Filter Manifold Topology

open scoped Interval

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Rectangle integrals and continuity across the axis -/

/-- The integral of a function around a rectangle. -/
def SchwarzReflection.rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

/-- The rectangle integral splits into edge wedge integrals. -/
theorem SchwarzReflection.rectangleIntegral_eq_wedges (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w = Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f := by
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  rfl

/-- A horizontal line inside the rectangle's height lies in it. -/
theorem SchwarzReflection.horizontal_line_mem_rectangle {z w : ℂ} {x y : ℝ}
    (hx : x ∈ [[z.re, w.re]]) (hy : y ∈ [[z.im, w.im]]) :
    (x : ℂ) + y * Complex.I ∈ Complex.Rectangle z w := by
  simpa only [Complex.Rectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
    zero_add] using And.intro hx hy

/-- The vertical slices of a continuous function are integrable. -/
theorem SchwarzReflection.continuousOn_vertical_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Complex.Rectangle z w)) {x : ℝ} (hx : x ∈ [[z.re, w.re]]) {a b : ℝ}
    (hab : [[a, b]] ⊆ [[z.im, w.im]]) :
    IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume a
      b := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop)
  intro y hy
  exact horizontal_line_mem_rectangle hx (hab hy)

/-- The rectangle integral splits across a horizontal cut. -/
theorem SchwarzReflection.rectangleIntegral_split {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Complex.Rectangle z w)) {a : ℝ} (ha : a ∈ [[z.im, w.im]]) :
    rectangleIntegral f z w =
      rectangleIntegral f z (w.re + a * Complex.I) +
        rectangleIntegral f (z.re + a * Complex.I) w := by
  have hz : [[z.im, a]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc (Set.left_mem_uIcc) ha
  have hw : [[a, w.im]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc ha (Set.right_mem_uIcc)
  have hright :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuousOn_vertical_integrable hf (Set.right_mem_uIcc) hz)
      (continuousOn_vertical_integrable hf (Set.right_mem_uIcc) hw)
  have hleft :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuousOn_vertical_integrable hf (Set.left_mem_uIcc) hz)
      (continuousOn_vertical_integrable hf (Set.left_mem_uIcc) hw)
  simp only [rectangleIntegral, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rw [← hright, ← hleft]
  ring

/-- The lower half-rectangle lies in the rectangle. -/
theorem SchwarzReflection.rectangle_split_lower_subset {z w : ℂ} {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    Complex.Rectangle z (w.re + a * Complex.I) ⊆ Complex.Rectangle z w := by
  have hsub : [[z.im, a]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc Set.left_mem_uIcc ha
  intro x hx
  simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hx ⊢
  exact ⟨hx.1, hsub hx.2⟩

/-- The upper half-rectangle lies in the rectangle. -/
theorem SchwarzReflection.rectangle_split_upper_subset {z w : ℂ} {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    Complex.Rectangle (z.re + a * Complex.I) w ⊆ Complex.Rectangle z w := by
  have hsub : [[a, w.im]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc ha Set.right_mem_uIcc
  intro x hx
  simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hx ⊢
  exact ⟨hx.1, hsub hx.2⟩

/-- A rectangle integral of an off-axis analytic function vanishes. -/
theorem SchwarzReflection.rectangleIntegral_eq_zero_of_axis_not_interior {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Complex.Rectangle z w))
    (hd : ∀ x ∈ Complex.Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x)
    (haxis : (0 : ℝ) ∉ Set.Ioo (Min.min z.im w.im) (Max.max z.im w.im)) :
    rectangleIntegral f z w = 0 := by
  apply
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅
      Set.countable_empty hf
  intro x hx
  have hx' := hx.1
  simp only [Complex.mem_reProdIm, Set.mem_Ioo] at hx'
  apply hd x
  · exact ⟨⟨hx'.1.1.le, hx'.1.2.le⟩, ⟨hx'.2.1.le, hx'.2.2.le⟩⟩
  · intro hzero
    apply haxis
    simpa only [hzero, Set.mem_Ioo] using hx'.2

/-- Zero is not in an open interval ending at it. -/
theorem SchwarzReflection.zero_not_mem_open_interval_to_zero (a : ℝ) :
    (0 : ℝ) ∉ Set.Ioo (Min.min a 0) (Max.max a 0) := by
  rcases le_total a 0 with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h]

/-- A continuous function analytic off the real axis is differentiable. -/
theorem SchwarzReflection.differentiableOn_of_continuousOn_off_real {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hf⟩
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, ← rectangleIntegral_eq_wedges]
  have hc := hf.mono hzw
  have hd' : ∀ x ∈ Complex.Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x := fun x hx =>
    hd x (hzw hx)
  by_cases haxis : (0 : ℝ) ∈ Set.Ioo (Min.min z.im w.im) (Max.max z.im w.im)
  · have haxis' : (0 : ℝ) ∈ [[z.im, w.im]] := ⟨haxis.1.le, haxis.2.le⟩
    rw [rectangleIntegral_split hc haxis']
    have hlow := rectangle_split_lower_subset (z := z) (w := w) haxis'
    have hhigh := rectangle_split_upper_subset (z := z) (w := w) haxis'
    have h₁ : rectangleIntegral f z (w.re + (0 : ℝ) * Complex.I) = 0 := by
      apply
        rectangleIntegral_eq_zero_of_axis_not_interior (hc.mono hlow)
          (fun x hx => hd' x (hlow hx))
      simpa using zero_not_mem_open_interval_to_zero z.im
    have h₂ : rectangleIntegral f (z.re + (0 : ℝ) * Complex.I) w = 0 := by
      apply
        rectangleIntegral_eq_zero_of_axis_not_interior (hc.mono hhigh)
          (fun x hx => hd' x (hhigh hx))
      simpa [min_comm, max_comm] using zero_not_mem_open_interval_to_zero w.im
    rw [h₁, h₂, add_zero]
  · exact rectangleIntegral_eq_zero_of_axis_not_interior hc hd' haxis

/-- A continuous function analytic off the real axis is analytic. -/
theorem SchwarzReflection.analyticOnNhd_of_continuousOn_off_real {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    AnalyticOnNhd ℂ f U :=
  (differentiableOn_of_continuousOn_off_real hU hf hd).analyticOnNhd hU

/-! ### The reflection paste -/

/-- The Schwarz reflection paste of a function across the axis. -/
def SchwarzReflection.pasteUpper (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else g z

/-- On the upper half-plane the paste computes the upper branch `f`. -/
@[simp]
theorem SchwarzReflection.pasteUpper_of_nonneg (f g : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    pasteUpper f g z = f z :=
  if_pos hz

/-- On the lower half-plane the paste computes the lower branch `g`. -/
@[simp]
theorem SchwarzReflection.pasteUpper_of_neg (f g : ℂ → ℂ) {z : ℂ} (hz : z.im < 0) :
    pasteUpper f g z = g z :=
  if_neg (not_le.mpr hz)

/-- The paste of a real-on-axis function is continuous. -/
theorem SchwarzReflection.continuousOn_pasteUpper {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : ContinuousOn f (U ∩ {z | 0 ≤ z.im})) (hg : ContinuousOn g (U ∩ {z | z.im ≤ 0}))
    (hfg : ∀ z ∈ U, z.im = 0 → f z = g z) : ContinuousOn (pasteUpper f g) U := by
  change ContinuousOn (fun z => if 0 ≤ z.im then f z else g z) U
  apply ContinuousOn.if
  · intro z hz
    exact hfg z hz.1 ((frontier_le_subset_eq continuous_const Complex.continuous_im hz.2).symm)
  · simpa only [closure_le_eq continuous_const Complex.continuous_im] using hf
  · apply hg.mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    apply closure_lt_subset_le Complex.continuous_im continuous_const
    simpa only [not_le] using hz.2

/-- The paste of a real-on-axis analytic function is analytic. -/
theorem SchwarzReflection.analyticOnNhd_pasteUpper {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hfc : ContinuousOn f (U ∩ {z | 0 ≤ z.im})) (hgc : ContinuousOn g (U ∩ {z | z.im ≤ 0}))
    (hfd : ∀ z ∈ U, 0 < z.im → DifferentiableAt ℂ f z)
    (hgd : ∀ z ∈ U, z.im < 0 → DifferentiableAt ℂ g z) (hfg : ∀ z ∈ U, z.im = 0 → f z = g z) :
    AnalyticOnNhd ℂ (pasteUpper f g) U := by
  apply analyticOnNhd_of_continuousOn_off_real hU (continuousOn_pasteUpper hfc hgc hfg)
  intro z hz hn
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · apply (hgd z hz hneg).congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const hneg] with
      w hw
    exact pasteUpper_of_neg f g hw
  · apply (hfd z hz hpos).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hpos] with
      w hw
    exact pasteUpper_of_nonneg f g hw.le
