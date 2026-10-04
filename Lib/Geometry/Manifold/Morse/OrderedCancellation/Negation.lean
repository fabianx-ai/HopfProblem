/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.Index

/-!
# The Morse function `-f`

`-f` is Morse when `f` is (`MorseCancellation.isMorse_neg`), with the same critical points,
distinct critical values when `f` has them (`distinct_critical_values_neg`), and index
`n - index_f p` at each critical point (`nativeMorseIndex_neg_add`); hence the number of critical
points of `-f` of index `n - k` equals the number of critical points of `f` of index `k`
(`nativeMorseCount_neg`).  Cf. Milnor, *Morse Theory*, §2.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- If `f` is Morse at `p` then so is `-f`. -/
theorem MorseCancellation.isMorseAt_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : ManifoldMorse.IsMorseAt E f p) :
    ManifoldMorse.IsMorseAt E (fun x => -f x) p := by
  obtain ⟨e, he, hp, hregular | hH⟩ := hm
  · refine ⟨e, he, hp, Or.inl ?_⟩
    change fderiv ℝ (fun x => -f (e.symm x)) (e p) ≠ 0
    rw [fderiv_fun_neg, neg_ne_zero]
    exact hregular
  · refine ⟨e, he, hp, Or.inr ?_⟩
    have hd : fderiv ℝ ((fun x => -f x) ∘ e.symm) = fun z => -fderiv ℝ (f ∘ e.symm) z := by
      funext z
      exact fderiv_fun_neg
    rw [hd, fderiv_fun_neg]
    change Function.Bijective (fun v => -(fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p) v))
    exact neg_bijective.comp hH

/-- If `f` is a Morse function then so is `-f`. -/
theorem MorseCancellation.isMorse_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} (hm : ManifoldMorse.IsMorse E f) :
    ManifoldMorse.IsMorse E (fun x => -f x) := fun x => isMorseAt_neg (hm x)

attribute [local instance 100] Classical.propDecidable in
/-- For a signed Morse chart `c` of `f` at `p`, the negative coordinates of the chart `c.neg` of
`-f` have the dimension of the positive coordinates of `c`. -/
theorem MorseCancellation.negative_finrank_neg_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.neg.NegativeCoordinates = Module.finrank ℝ c.PositiveCoordinates := by
  simp only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    ManifoldMorse.SignedMorseChart.PositiveCoordinates, MorseHandle.NegativeSpace,
    MorseHandle.PositiveSpace, finrank_euclideanSpace]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change -c.weights i = -1 ↔ c.weights i ≠ -1
  rcases c.signs i with h | h <;> norm_num [h]

/-- Milnor, Morse Theory §2: at a critical point `p` with a signed Morse chart,
`index_{-f} p + index_f p = dim E`. -/
theorem MorseCancellation.nativeMorseIndex_neg_add {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E (fun x => -f x) p + nativeMorseIndex E f p = Module.finrank ℝ E := by
  rw [nativeMorseIndex_eq_chart c.neg, nativeMorseIndex_eq_chart c, negative_finrank_neg_chart]
  exact (Nat.add_comm _ _).trans c.finrank_negative_add_positive

/-- For a Morse function `f` on a finite-dimensional manifold and `k ≤ dim E`, the number of
critical points of `-f` of index `dim E - k` equals the number of critical points of `f` of
index `k`. -/
theorem MorseCancellation.nativeMorseCount_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) :
    nativeMorseCount E (fun x => -f x) (Module.finrank ℝ E - k) = nativeMorseCount E f k := by
  unfold nativeMorseCount
  congr 1
  ext z
  rw [ManifoldMorse.criticalPoints_neg]
  change
    (z ∈ ManifoldMorse.criticalPoints E f ∧
        nativeMorseIndex E (fun x => -f x) z = Module.finrank ℝ E - k) ↔
      (z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k)
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩

/-- If `f` is injective on its critical set then so is `-f` (on the same set). -/
theorem MorseCancellation.distinct_critical_values_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) :
    Set.InjOn (fun x => -f x) (ManifoldMorse.criticalPoints E (fun x => -f x)) := by
  rw [ManifoldMorse.criticalPoints_neg]
  intro x hx y hy hxy
  exact hinj hx hy (neg_injective hxy)

end
