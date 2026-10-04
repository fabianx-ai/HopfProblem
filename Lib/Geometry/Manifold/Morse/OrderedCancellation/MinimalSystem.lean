/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Existence.DistinctCriticalValues
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation

/-!
# Morse functions with the least number of critical points

On a compact manifold there is a Morse function with distinct critical values (an *excellent*
Morse function) and the least number of critical points among all such, together with an
`AdaptedWindows` package for it (`MorseCancellation.exists_minimal_excellent_morse_system`).
Minimality is preserved by `f ↦ -f` (`minimal_excellent_morse_neg`) and forbids the removal of a
pair of critical points (`minimal_excellent_morse_forbids_pair_removal`).  This is the starting
point of Smale's minimal Morse function programme, cf. Milnor, *Lectures on the h-cobordism
theorem*, §8.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- On a compact manifold `M` modelled on the finite-dimensional space `E` there is a Morse
function `f` with an `AdaptedWindows E f` package whose number of critical points is at most that
of every Morse function with distinct critical values. -/
theorem MorseCancellation.exists_minimal_excellent_morse_system (E : Type*) (M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            ∀ g : M → ℝ,
              ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                ManifoldMorse.IsMorse E g →
                  Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                    (ManifoldMorse.criticalPoints E f).ncard ≤
                      (ManifoldMorse.criticalPoints E g).ncard := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
            (ManifoldMorse.criticalPoints E f).ncard = n
  obtain ⟨f₀, hf₀, hm₀, -, hinj₀⟩ :=
    ManifoldMorse.exists_morse_function_with_distinct_critical_values E M
  have hex : ∃ n, P n :=
    ⟨(ManifoldMorse.criticalPoints E f₀).ncard, f₀, hf₀, hm₀, hinj₀, rfl⟩
  obtain ⟨f, hf, hm, hinj, hcard⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  refine ⟨f, hf, hm, S, ?_⟩
  intro g hg hmg hinjg
  rw [hcard]
  exact Nat.find_min' hex ⟨g, hg, hmg, hinjg, rfl⟩

/-- If `f` has the least number of critical points among Morse functions with distinct critical
values, then no such Morse function `g` has exactly two critical points fewer than `f`. -/
theorem MorseCancellation.minimal_excellent_morse_forbids_pair_removal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ}
    (hminimal :
      ∀ h : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
          ManifoldMorse.IsMorse E h →
            Set.InjOn h (ManifoldMorse.criticalPoints E h) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E h).ncard)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g)) :
    (ManifoldMorse.criticalPoints E g).ncard + 2 ≠
      (ManifoldMorse.criticalPoints E f).ncard := by
  have hle := hminimal g hg hmg hinjg
  omega

/-- If `f` has the least number of critical points among Morse functions with distinct critical
values, then so has `-f`. -/
theorem MorseCancellation.minimal_excellent_morse_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E g).ncard) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        ManifoldMorse.IsMorse E g →
          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
            (ManifoldMorse.criticalPoints E (fun x => -f x)).ncard ≤
              (ManifoldMorse.criticalPoints E g).ncard := by
  intro g hg hmg hinjg
  have hh :=
    hminimal (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
  simpa only [ManifoldMorse.criticalPoints_neg] using hh

end
