/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.Cutoff

/-!
# Smoothness of parametric interval integrals

If `G : P × ℝ → F` is `C^∞` then `p ↦ ∫ t in a..b, G (p, t)` is `C^∞`
(`SmoothMorseLemma.contDiff_parametric_intervalIntegral`; differentiation under the integral
sign). The proof writes the integral as a convolution with a compactly supported cutoff equal to
`1` on `[[a, b]]` and applies Mathlib's `contDiffOn_convolution_right_with_param_comp`.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Convolution

@[expose] public noncomputable section

/-- A parametric interval integral of a `C^n` integrand is `C^n`. -/
theorem SmoothMorseLemma.contDiff_parametric_intervalIntegral_of_le {P F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : P × ℝ → F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := LineBundleTransport.exists_interval_cutoff a b
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc a b)
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  let g : P → ℝ → F := fun p t => χ (-t) • G (p, -t)
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => g q.1 q.2) :=
    (hχ.comp contDiff_snd.neg).smul (hG.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hk : IsCompact (-tsupport χ) := hχc.isCompact.neg
  have hgs : ∀ p t, p ∈ (Set.univ : Set P) → t ∉ -tsupport χ → g p t = 0 := by
    intro p t _ ht
    have ht' : -t ∉ tsupport χ := by simpa using ht
    change χ (-t) • G (p, -t) = 0
    rw [image_eq_zero_of_notMem_tsupport ht', zero_smul]
  have hf : MeasureTheory.LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) μ :=
    MeasureTheory.locallyIntegrable_const _
  have hc :=
    MeasureTheory.contDiffOn_convolution_right_with_param_comp (μ := μ) (n := (⊤ : ℕ∞)) L (v :=
      fun _ : P => (0 : ℝ)) contDiffOn_const isOpen_univ hk hgs hf hg.contDiffOn
  have heq (p : P) : ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0 = ∫ t in a..b, G (p, t) := by
    rw [intervalIntegral.integral_of_le hab]
    change (∫ t, (1 : ℝ) • (χ (-(0 - t)) • G (p, -(0 - t))) ∂μ) = ∫ t in Set.Ioc a b, G (p, t)
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hχt : χ t = 1 := hχone (Set.mem_uIcc_of_le ht.1.le ht.2)
    simp only [zero_sub, neg_neg, hχt, one_smul]
  have hfun :
    (fun p => ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0) = (fun p => ∫ t in a..b, G (p, t)) :=
    funext heq
  rw [← hfun]
  exact contDiffOn_univ.mp hc

/-- A parametric interval integral is smooth. -/
theorem SmoothMorseLemma.contDiff_parametric_intervalIntegral {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] (G : P × ℝ → F)
    (hG : ContDiff ℝ ∞ G) (a b : ℝ) : ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  rcases le_total a b with hab | hba
  · exact contDiff_parametric_intervalIntegral_of_le G hG a b hab
  · have he : (fun p => ∫ t in a..b, G (p, t)) = (fun p => -(∫ t in b..a, G (p, t))) :=
      funext fun _ => intervalIntegral.integral_symm b a
    rw [he]
    exact (contDiff_parametric_intervalIntegral_of_le G hG b a hba).neg
