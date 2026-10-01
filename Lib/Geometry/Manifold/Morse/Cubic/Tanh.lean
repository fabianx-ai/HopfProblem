/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Calculus of `Real.tanh` and `Real.artanh`

The derivative of `tanh` is `1 - tanh²`, `tanh` is strictly increasing with limits `±1` at `±∞`,
and `artanh` is smooth on `(-1, 1)`.  These complement
`Mathlib/Analysis/SpecialFunctions/Artanh.lean` (`Real.tanh_bijOn`, `Real.artanh_tanh`) and are
candidates for upstreaming.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- `tanh` differentiates to `sech²`. -/
theorem MorseCancellation.hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hf : (fun x => Real.sinh x / Real.cosh x) = Real.tanh :=
    funext (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  change HasDerivAt (fun x => Real.sinh x / Real.cosh x) _ t at h
  rw [hf] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- `tanh` is strictly monotone. -/
theorem MorseCancellation.strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh (fun t => sub_pos.mpr (Real.tanh_sq_lt_one t))

/-- `tanh` tends to `1` at infinity. -/
theorem MorseCancellation.tendsto_tanh_atTop : Filter.Tendsto Real.tanh Filter.atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_atTop_isLUB strictMono_tanh.monotone
  rw [← Set.image_univ, Real.tanh_bijOn.image_eq]
  exact isLUB_Ioo (by norm_num)

/-- `tanh` tends to `−1` at negative infinity. -/
theorem MorseCancellation.tendsto_tanh_atBot : Filter.Tendsto Real.tanh Filter.atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_atBot_isGLB strictMono_tanh.monotone
  rw [← Set.image_univ, Real.tanh_bijOn.image_eq]
  exact isGLB_Ioo (by norm_num)

/-- `artanh` is smooth on `(−1,1)`. -/
theorem MorseCancellation.contDiffAt_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ Real.artanh x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hr : ContDiffAt ℝ ∞ (fun y : ℝ => (1 + y) / (1 - y)) x :=
    (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id)
      (by linarith [hx.2])
  exact (hr.sqrt hp.ne').log (Real.sqrt_pos.mpr hp).ne'
