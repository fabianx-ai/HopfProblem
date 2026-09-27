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
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative
public import Lib.Geometry.Manifold.LocalDiffeomorph
/-!
# Positivity of the derivative of `Real.smoothTransition`

Mathlib's `Real.smoothTransition` (`Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`)
is the smooth step `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`, with
`contDiff`, `zero`, `one`, `nonneg`, `le_one` and `pos_of_pos`; it lacks the derivative
formula and strict monotonicity. Here: `expNegInvGlue` has derivative `t⁻¹ ^ 2 * expNegInvGlue t`
(`expNegInvGlue.hasDerivAt`), the derivative of `Real.smoothTransition` is
positive on `Ioo 0 1` (`Real.smoothTransition.deriv_pos`), so `Real.smoothTransition` is strictly
monotone on `Icc 0 1` (`Real.smoothTransition.strictMonoOn`), and every level `c ∈ Ioo 0 1` is
attained at a unique time `τ ∈ Ioo 0 1`, with positive derivative there
(`Real.smoothTransition.exists_unique_eq_of_mem_Ioo`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Derivative of the smooth transition -/

/-- The exponential glue `exp(-1/t)` is differentiable. -/
theorem expNegInvGlue.hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

/-- The smooth transition has positive derivative on the interior. -/
theorem Real.smoothTransition.deriv_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < deriv Real.smoothTransition t := by
  let a := expNegInvGlue t
  let b := expNegInvGlue (1 - t)
  let a' := t⁻¹ ^ 2 * a
  let b' := (1 - t)⁻¹ ^ 2 * b
  have ha : 0 < a := expNegInvGlue.pos_of_pos ht.1
  have hb : 0 < b := expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)
  have ha' : 0 < a' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero ht.1.ne')) ha
  have hb' : 0 < b' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero (sub_pos.mpr ht.2).ne')) hb
  have hA : HasDerivAt expNegInvGlue a' t := expNegInvGlue.hasDerivAt t
  have hB : HasDerivAt (fun s : ℝ => expNegInvGlue (1 - s)) (-b') t := by
    convert!
      (expNegInvGlue.hasDerivAt (1 - t)).comp t
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) using
      1
    dsimp only [b', b]
    ring
  have hd := hA.div (hA.add hB) (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition ((a' * (a + b) - a * (a' + -b')) / (a + b) ^ 2) t at hd
  rw [hd.deriv]
  apply div_pos
  · have he : a' * (a + b) - a * (a' + -b') = a' * b + a * b' := by ring
    rw [he]
    exact add_pos (mul_pos ha' hb) (mul_pos ha hb')
  · exact sq_pos_of_pos (add_pos ha hb)

/-- The smooth transition is strictly monotone on its domain. -/
theorem Real.smoothTransition.strictMonoOn :
    StrictMonoOn Real.smoothTransition (Set.Icc (0 : ℝ) 1) := by
  apply
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) Real.smoothTransition.continuous.continuousOn
  intro t ht
  apply Real.smoothTransition.deriv_pos
  simpa only [interior_Icc] using ht

/-- Each level is crossed at a unique transition time. -/
theorem Real.smoothTransition.exists_unique_eq_of_mem_Ioo {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ τ : ℝ,
      τ ∈ Set.Ioo (0 : ℝ) 1 ∧
        Real.smoothTransition τ = c ∧
          0 < deriv Real.smoothTransition τ ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.smoothTransition t = c ↔ t = τ := by
  have hc' : c ∈ Set.Icc (Real.smoothTransition 0) (Real.smoothTransition 1) := by
    rw [Real.smoothTransition.zero, Real.smoothTransition.one]
    exact ⟨hc.1.le, hc.2.le⟩
  obtain ⟨τ, hτ, heq⟩ :=
    intermediate_value_Icc zero_le_one Real.smoothTransition.continuous.continuousOn hc'
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, Real.smoothTransition.zero] at heq
    linarith [hc.1]
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, Real.smoothTransition.one] at heq
    linarith [hc.2]
  have hτI : τ ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hτ.1 (Ne.symm hτ0), lt_of_le_of_ne hτ.2 hτ1⟩
  refine ⟨τ, hτI, heq, Real.smoothTransition.deriv_pos hτI, ?_⟩
  intro t ht
  exact
    ⟨fun h => Real.smoothTransition.strictMonoOn.injOn ht hτ (h.trans heq.symm), fun h => h ▸ heq⟩
