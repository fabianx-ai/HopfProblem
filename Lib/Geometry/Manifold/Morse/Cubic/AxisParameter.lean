/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Cubic.Model
public import Lib.Geometry.Manifold.Morse.Cubic.DescentField
public import Lib.Geometry.Manifold.Morse.Cubic.Tanh

/-!
# The connecting orbit of the cubic model

For `a > 0` the axis `{(s, 0) | -a < s < a}` of the cubic model `cubic σ (-a²)` is the orbit of the
descent field `cubicDescent` joining the two critical points: the solution of `s' = a² - s²` with
`s 0 = 0` is `MorseCancellation.cubicAxisParameter a t = a * tanh (a * t)`
(`hasDerivAt_cubicAxisParameter`), a smooth bijection of `ℝ` onto `(-a, a)`
(`range_cubicAxisParameter`, `contDiff_cubicAxisParameter`) with limits `±a`, whose inverse is
`cubicAxisClock a s = artanh (s / a) / a` (`cubicAxisClock_parameter`, `cubicAxisParameter_clock`,
`contDiffOn_cubicAxisClock`).  `cubicModelOrbit a t = (cubicAxisParameter a t, 0)` is the
corresponding integral curve of `cubicDescent σ (-a²)` (`hasDerivAt_cubicModelOrbit`).  This is the
single trajectory from the critical point of index `λ + 1` to that of index `λ` in the
cancellation model, cf. Milnor, *Lectures on the h-cobordism theorem*, §5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The time parameter along the cubic axis. -/
def MorseCancellation.cubicAxisParameter (a t : ℝ) : ℝ :=
  a * Real.tanh (a * t)

/-- The cubic axis parameter is differentiable. -/
theorem MorseCancellation.hasDerivAt_cubicAxisParameter (a t : ℝ) :
    HasDerivAt (cubicAxisParameter a) (a ^ 2 - cubicAxisParameter a t ^ 2) t := by
  have h := ((Real.hasDerivAt_tanh (a * t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul a
  change HasDerivAt (cubicAxisParameter a) (a * ((1 - Real.tanh (a * t) ^ 2) * (a * 1))) t at h
  convert h using 1
  dsimp [cubicAxisParameter]
  ring

/-- The cubic axis parameter lies in the axis. -/
theorem MorseCancellation.cubicAxisParameter_mem {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisParameter a t ∈ Set.Ioo (-a) a := by
  have hlo := mul_lt_mul_of_pos_left (Real.neg_one_lt_tanh (a * t)) ha
  have hhi := mul_lt_mul_of_pos_left (Real.tanh_lt_one (a * t)) ha
  constructor
  · simpa only [cubicAxisParameter, mul_neg, mul_one] using hlo
  · simpa only [cubicAxisParameter, mul_one] using hhi

/-- The cubic axis parameter's range. -/
theorem MorseCancellation.range_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    Set.range (cubicAxisParameter a) = Set.Ioo (-a) a := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact cubicAxisParameter_mem ha t
  · intro hs
    have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · apply (lt_div_iff₀ ha).mpr
        simpa only [neg_one_mul] using hs.1
      · apply (div_lt_iff₀ ha).mpr
        simpa only [one_mul] using hs.2
    refine ⟨Real.artanh (s / a) / a, ?_⟩
    simp only [cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

/-- The axis parameter tends to the positive endpoint. -/
theorem MorseCancellation.tendsto_cubicAxisParameter_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 a) := by
  have h := (Real.tendsto_tanh_atTop.comp (Filter.tendsto_id.const_mul_atTop ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 (a * 1)) at h
  simpa only [mul_one] using h

/-- The axis parameter tends to the negative endpoint. -/
theorem MorseCancellation.tendsto_cubicAxisParameter_atBot {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (-a)) := by
  have h := (Real.tendsto_tanh_atBot.comp (Filter.tendsto_id.const_mul_atBot ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (a * -1)) at h
  simpa only [mul_neg, mul_one] using h

/-- The orbit of the cubic model. -/
def MorseCancellation.cubicModelOrbit {m : ℕ} (a t : ℝ) : Model m :=
  (cubicAxisParameter a t, 0)

/-- The cubic model orbit at time zero. -/
theorem MorseCancellation.cubicModelOrbit_zero {m : ℕ} (a : ℝ) : cubicModelOrbit (m := m) a 0 = 0 := by
  simp [cubicModelOrbit, cubicAxisParameter, Real.tanh_zero]

/-- The cubic model orbit solves the field. -/
theorem MorseCancellation.hasDerivAt_cubicModelOrbit {m : ℕ} (σ : Fin m → ℝ) (a t : ℝ) :
    HasDerivAt (cubicModelOrbit a) (cubicDescent σ (-(a ^ 2)) (cubicModelOrbit a t)) t := by
  have h := (hasDerivAt_cubicAxisParameter a t).prodMk (hasDerivAt_const t (0 : Fin m → ℝ))
  change HasDerivAt (cubicModelOrbit a) (a ^ 2 - cubicAxisParameter a t ^ 2, 0) t at h
  convert h using 1
  apply Prod.ext
  · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
    ring
  · funext i
    simp only [cubicDescent, cubicModelOrbit, Pi.zero_apply, MulZeroClass.mul_zero]

/-- The cubic model orbit's range. -/
theorem MorseCancellation.range_cubicModelOrbit {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Set.range (cubicModelOrbit (m := m) a) = Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨cubicAxisParameter_mem ha t, rfl⟩
  · rintro ⟨hs, hz⟩
    obtain ⟨t, ht⟩ := (range_cubicAxisParameter ha).symm ▸ hs
    refine ⟨t, ?_⟩
    exact Prod.ext ht (show (0 : Fin m → ℝ) = p.2 from hz.symm)

/-- The model orbit tends to the positive end. -/
theorem MorseCancellation.tendsto_cubicModelOrbit_atTop {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atTop (𝓝 (a, 0)) :=
  (tendsto_cubicAxisParameter_atTop ha).prodMk_nhds tendsto_const_nhds

/-- The model orbit tends to the negative end. -/
theorem MorseCancellation.tendsto_cubicModelOrbit_atBot {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atBot (𝓝 (-a, 0)) :=
  (tendsto_cubicAxisParameter_atBot ha).prodMk_nhds tendsto_const_nhds

/-- The cubic axis parameter is smooth. -/
theorem MorseCancellation.contDiff_cubicAxisParameter (a : ℝ) : ContDiff ℝ ∞ (cubicAxisParameter a) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    have hh : ContDiff ℝ ∞ (fun t => Real.sinh t / Real.cosh t) :=
      Real.contDiff_sinh.div Real.contDiff_cosh (fun t => (Real.cosh_pos t).ne')
    have he : (fun t => Real.sinh t / Real.cosh t) = Real.tanh :=
      funext (fun t => (Real.tanh_eq_sinh_div_cosh t).symm)
    rw [he] at hh
    exact hh
  change ContDiff ℝ ∞ (fun t => a * Real.tanh (a * t))
  exact contDiff_const.mul (ht.comp (contDiff_const.mul contDiff_id))

/-- The clock function inverse to the axis parameter. -/
def MorseCancellation.cubicAxisClock (a s : ℝ) : ℝ :=
  Real.artanh (s / a) / a

/-- The clock inverts the axis parameter. -/
theorem MorseCancellation.cubicAxisClock_parameter {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisClock a (cubicAxisParameter a t) = t := by
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel_left₀ _ ha.ne', Real.artanh_tanh]

/-- The axis parameter inverts the clock. -/
theorem MorseCancellation.cubicAxisParameter_clock {a s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Ioo (-a) a) :
    cubicAxisParameter a (cubicAxisClock a s) = s := by
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

/-- The cubic axis clock is smooth. -/
theorem MorseCancellation.contDiffOn_cubicAxisClock {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (cubicAxisClock a) (Set.Ioo (-a) a) := by
  intro s hs
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  exact
    (((Real.contDiffAt_artanh hs').comp s (contDiffAt_id.div_const a)).div_const a).contDiffWithinAt
