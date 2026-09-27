/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Rearrangement
/-!
# Path connectedness of the middle level in dimension six (proof-specific)

Specialisations of `AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions`
to `Module.finrank ℝ E = 6` and index `3`, the W4W1 argument's middle level:
`AdaptedWindows.pathConnectedSpace_middle_level` (critical points above the regular value have
index `≥ 3`, those below have index `≤ 3`) and
`pathConnectedSpace_index_three_upper_level` (critical values ordered by index; the upper level
of the window of an index-`3` critical point).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! 

/-- In dimension six the middle regular level is path connected. -/
theorem AdaptedWindows.pathConnectedSpace_middle_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → 3 ≤ MorseCancellation.nativeMorseIndex E f p)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ 3)
    (z₀ : { z : M // f z = a }) : PathConnectedSpace { z : M // f z = a } :=
  S.pathConnectedSpace_regular_level_of_endpoint_dimensions hf hreg
    (fun p hp => by have hh := hhigh p hp; omega) hlow (by omega) z₀

/-- Above index-three critical points the upper level is path connected. -/
theorem AdaptedWindows.pathConnectedSpace_index_three_upper_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (p : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 3)
    (z₀ : (S.data p).UpperLevel) : PathConnectedSpace (S.data p).UpperLevel := by
  apply S.pathConnectedSpace_middle_level hf hdim (S.data p).upper_regular (z₀ := z₀)
  · intro r hr
    have hpr : f p < f r := (S.toSurgeryWindows.value_lt_upper p).trans_le hr
    simpa only [hp] using horder p r hpr
  · intro r hr
    rcases lt_trichotomy (f r) (f p) with h | h | h
    · simpa only [hp] using horder r p h
    · have he : r = p := Subtype.ext (S.distinct r.property p.property h)
      rw [he, hp]
    · have hsep := S.separated p r h
      have hlow := S.toSurgeryWindows.lower_lt_value r
      exact ((not_lt_of_ge hr) (hsep.trans hlow)).elim
