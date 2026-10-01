/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.SymmetricForm
public import Lib.Analysis.Calculus.MorseLemma.ParametricIntegral

/-!
# The second-order Taylor factor

For a `C^∞` function `f : E → ℝ` on a real normed space,
`secondTaylorFactor f x = 2 ∫₀¹ (1 - t) D²f(t x) dt` is a smooth family of symmetric bilinear
forms with `secondTaylorFactor f 0 = D²f(0)` and
`f x = f 0 + Df(0) x + (1/2) secondTaylorFactor f x x x`
(Taylor's formula with integral remainder). When `Df(0) = 0` this is the factorization
`f x = f 0 + (1/2) A(x)(x, x)` with `A` smooth and symmetric used in the proof of the Morse lemma
(Milnor, *Morse Theory*, proof of Lemma 2.2; cf. Lemma 2.1).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The Hessian integrand of the second-order Taylor expansion. -/
def SmoothMorseLemma.taylorHessianIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (q : E × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 - q.2) • fderiv ℝ (fderiv ℝ f) (q.2 • q.1)

/-- The second-order Taylor remainder factor. -/
def SmoothMorseLemma.secondTaylorFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, taylorHessianIntegrand f (x, t)

/-- The Taylor Hessian integrand is smooth. -/
theorem SmoothMorseLemma.contDiff_taylorHessianIntegrand {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (taylorHessianIntegrand f) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := .of_norm_smul_le (fun c B => norm_smul_le c B)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := (contDiff_infty_iff_fderiv.mp hdf).2
  exact (contDiff_const.sub contDiff_snd).smul (hH.comp (contDiff_snd.smul contDiff_fst))

/-- The second Taylor factor is smooth. -/
theorem SmoothMorseLemma.contDiff_secondTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (secondTaylorFactor f) :=
  (contDiff_parametric_intervalIntegral (taylorHessianIntegrand f)
        (contDiff_taylorHessianIntegrand hf) 0 1).const_smul
    (2 : ℝ)

/-- The second Taylor factor evaluates the integral formula. -/
theorem SmoothMorseLemma.secondTaylorFactor_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) u v := by
  have hc : Continuous (fun t : ℝ => taylorHessianIntegrand f (x, t)) :=
    (contDiff_taylorHessianIntegrand hf).continuous.comp (continuous_const.prodMk continuous_id)
  have hi :
    IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t))
      MeasureTheory.MeasureSpace.volume 0 1 :=
    hc.intervalIntegrable 0 1
  have hiu :
    IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t) u)
      MeasureTheory.MeasureSpace.volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  simp only [secondTaylorFactor, smul_apply]
  rw [ContinuousLinearMap.intervalIntegral_apply hi u,
    ContinuousLinearMap.intervalIntegral_apply hiu v]
  simp only [taylorHessianIntegrand, smul_apply, smul_eq_mul]

/-- The second Taylor factor vanishes at the basepoint. -/
theorem SmoothMorseLemma.secondTaylorFactor_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) : secondTaylorFactor f 0 = fderiv ℝ (fderiv ℝ f) 0 := by
  have hw : (∫ t in (0 : ℝ)..1, (1 - t)) = (1 / 2 : ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t)) = (∫ _t in (0 : ℝ)..1, (1 : ℝ)) - ∫ t in (0 : ℝ)..1, t :=
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)
      _ = 1 / 2 := by norm_num [integral_id]
  have hz :
    (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) 0) =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 :=
    (intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t) (fderiv ℝ (fderiv ℝ f) 0)).trans
      (congrArg (fun c : ℝ => c • fderiv ℝ (fderiv ℝ f) 0) hw)
  simp only [secondTaylorFactor, taylorHessianIntegrand, smul_zero]
  exact (congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => (2 : ℝ) • B) hz).trans (by norm_num [smul_smul])

/-- The second Taylor factor is symmetric. -/
theorem SmoothMorseLemma.secondTaylorFactor_symmetric {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v = secondTaylorFactor f x v u := by
  rw [secondTaylorFactor_apply hf, secondTaylorFactor_apply hf]
  apply congrArg (fun r : ℝ => 2 * r)
  apply intervalIntegral.integral_congr
  intro t _
  have hs : IsSymmSndFDerivAt ℝ f (t • x) :=
    hf.contDiffAt.isSymmSndFDerivAt
      (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun r : ℝ => (1 - t) * r) (hs u v)

/-- A function with vanishing jet is its second Taylor factor plus a linear term. -/
theorem SmoothMorseLemma.map_eq_add_linear_add_secondTaylorFactor {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    f x = f 0 + fderiv ℝ f 0 x + (1 / 2 : ℝ) * secondTaylorFactor f x x x := by
  have ht :=
    map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := x) (n := 1)
      (fun t _ => hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have ht' :
    f x = f 0 + fderiv ℝ f 0 x + ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x :=
    by simpa [Finset.sum_range_succ, iteratedFDeriv_two_apply, smul_eq_mul] using ht
  rw [secondTaylorFactor_apply hf]
  calc
    f x = f 0 + fderiv ℝ f 0 x + ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x :=
      ht'
    _ =
        f 0 + fderiv ℝ f 0 x +
          (1 / 2 : ℝ) * (2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x) := by
      ring

/-- The second Taylor factor as a symmetric form. -/
def SmoothMorseLemma.symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : SymmetricForm E :=
  symmetrize E (secondTaylorFactor f x)

/-- The symmetric Taylor factor is smooth. -/
theorem SmoothMorseLemma.contDiff_symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (symmetricTaylorFactor f) :=
  (symmetrize E).contDiff.comp (contDiff_secondTaylorFactor hf)

/-- The symmetric Taylor factor evaluates the second factor. -/
theorem SmoothMorseLemma.symmetricTaylorFactor_coe {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    (symmetricTaylorFactor f x).val = secondTaylorFactor f x := by
  ext u v
  change
    (2 : ℝ)⁻¹ * (secondTaylorFactor f x u v + secondTaylorFactor f x v u) =
      secondTaylorFactor f x u v
  rw [secondTaylorFactor_symmetric hf x v u]
  ring

/-- The symmetric Taylor factor vanishes at the basepoint. -/
theorem SmoothMorseLemma.symmetricTaylorFactor_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    (symmetricTaylorFactor f 0).val = fderiv ℝ (fderiv ℝ f) 0 := by
  rw [symmetricTaylorFactor_coe hf, secondTaylorFactor_zero]

/-- The function equals its linear term plus the symmetric quadratic factor. -/
theorem SmoothMorseLemma.map_eq_add_symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : fderiv ℝ f 0 = 0) (x : E) :
    f x = f 0 + (1 / 2 : ℝ) * (symmetricTaylorFactor f x).val x x := by
  rw [symmetricTaylorFactor_coe hf]
  simpa only [hc, zero_apply, add_zero] using map_eq_add_linear_add_secondTaylorFactor hf x
