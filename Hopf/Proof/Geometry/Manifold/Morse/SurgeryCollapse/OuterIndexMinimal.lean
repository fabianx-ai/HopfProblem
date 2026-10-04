/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Cubic
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.OrderedCancellation.MinimalSystem
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.IndexOrdering
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.MinimumReduction

/-!
# The outer-index-minimal ordered Morse system (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  `MorseCancellation.exists_outer_index_minimal_ordered_morse_system`
combines the minimal excellent Morse system, the index ordering and the one-minimum/one-maximum
counts of `Lib.Geometry.Manifold.Morse.SurgeryCollapse` with the project's secondary minimality
of the count `c₁ + c₅` of critical points of the outer indices `1` and `5` of the six-dimensional
argument.

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statement unchanged.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

theorem MorseCancellation.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        ManifoldMorse.IsMorse E g →
                          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                            (ManifoldMorse.criticalPoints E f).ncard ≤
                              (ManifoldMorse.criticalPoints E g).ncard) ∧
                    ∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        ManifoldMorse.IsMorse E g →
                          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                            (ManifoldMorse.criticalPoints E g).ncard =
                                (ManifoldMorse.criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  classical
  obtain ⟨f₀, hf₀, hm₀, S₀, hminimal₀⟩ := exists_minimal_excellent_morse_system E M
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
            (ManifoldMorse.criticalPoints E f).ncard =
                (ManifoldMorse.criticalPoints E f₀).ncard ∧
              nativeMorseCount E f 1 + nativeMorseCount E f 5 = n
  have hex : ∃ n, P n := ⟨_, f₀, hf₀, hm₀, S₀.distinct, rfl, rfl⟩
  obtain ⟨g, hg, hmg, hinjg, hcardg, hcostg⟩ := Nat.find_spec hex
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨f, hf, hm, hcrit, -, S, horder, hcounts⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points T hg hmg
  have hcardf :
    (ManifoldMorse.criticalPoints E f).ncard =
      (ManifoldMorse.criticalPoints E f₀).ncard := by rw [hcrit, hcardg]
  have hminimal :
    ∀ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
        ManifoldMorse.IsMorse E h →
          Set.InjOn h (ManifoldMorse.criticalPoints E h) →
            (ManifoldMorse.criticalPoints E f).ncard ≤
              (ManifoldMorse.criticalPoints E h).ncard := by
    intro h hh hmh hinjh
    rw [hcardf]
    exact hminimal₀ h hh hmh hinjh
  obtain ⟨hmin, hmax⟩ := minimal_excellent_morse_extreme_counts_one S hf hm hminimal
  refine ⟨f, hf, hm, S, horder, hmin, hmax, hminimal, ?_⟩
  intro h hh hmh hinjh hcardh
  rw [hcounts 1, hcounts 5, hcostg]
  exact Nat.find_min' hex ⟨h, hh, hmh, hinjh, hcardh.trans hcardf, rfl⟩

end
