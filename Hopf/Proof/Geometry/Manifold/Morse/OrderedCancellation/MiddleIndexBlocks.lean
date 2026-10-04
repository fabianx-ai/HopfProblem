/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts
import Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation

/-!
# Middle index blocks of a six-dimensional ordered Morse system (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement is pinned to dimension `6` or to the indices `2`, `3`
of the W4W1 argument: the attaching `2`-sphere of an index-`3` window
(`MorseCancellation.nativeIndexThreeAttachingSphere`), families of such spheres in a regular level
(`IsNativeMiddleBasinFamily`), the index-`2` prefix / index-`3` block decomposition of an
index-ordered system with one minimum and no index `1` (`exists_middle_index_blocks`,
`nativeMiddleBlockPoint`), and the invariance of the secondary count `c₁ + c₅` under `f ↦ -f`
(`outer_index_minimality_neg`).

Moved from `Lib.Geometry.Manifold.Morse.OrderedCancellation`; statements unchanged.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

def MorseCancellation.nativeIndexThreeAttachingSphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) : C((Hemisphere.Sphere 2), (S.data p).LowerLevel) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  exact
    (S.data p).surgery.attachingSphere.comp
      ((SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
            2).toHomeomorph :
        C((Hemisphere.Sphere 2),
          Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1))

def MorseCancellation.IsNativeMiddleBasinFamily {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (α : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = a }) : Prop :=
  let _ := RegularLevel.chartedSpace hf ha
  (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) ∧
    (∀ j, Topology.IsClosedEmbedding (α j)) ∧
      (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) ∧
        Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) ∧
          ∀ j y,
            y ∈ Set.range (α j) ↔
              Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 (p j).val)

theorem MorseCancellation.outer_index_minimality_neg {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E g).ncard =
                  (ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        ManifoldMorse.IsMorse E g →
          Set.InjOn g (ManifoldMorse.criticalPoints E g) →
            (ManifoldMorse.criticalPoints E g).ncard =
                (ManifoldMorse.criticalPoints E (fun x => -f x)).ncard →
              nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  intro g hg hmg hinjg hcard
  have hh :=
    hsecondary (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
      (by simpa only [ManifoldMorse.criticalPoints_neg] using hcard)
  have hf1 := nativeMorseCount_neg hf hm (k := 1) (by omega)
  have hf5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hg1 := nativeMorseCount_neg hg hmg (k := 1) (by omega)
  have hg5 := nativeMorseCount_neg hg hmg (k := 5) (by omega)
  simp only [hdim, Nat.reduceSub] at hf1 hf5 hg1 hg5
  omega

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_middle_index_blocks {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ,
      S.HasIndexTwoPrefix r ∧
        ∃ _ : r + c < S.count,
          S.HasIndexThreeBlock r c ∧
            r + c + 1 < S.count ∧
              ∀ i : Fin S.count,
                r + c < i.val →
                  4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates := by
  have hn := S.count_pos hf
  let index := fun i : Fin S.count => nativeMorseIndex E f (S.point i)
  have hmono : Monotone index := native_indices_monotone S horder
  have hfirst : index ⟨0, hn⟩ = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hlast : index ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ = 6 :=
    (nativeMorseIndex_eq_chart (S.data (S.last hn)).chart).trans
      ((S.last_index_dimension hf hn).trans hdim)
  have hcut (k : ℕ) : ∃ j : Fin S.count, ∀ i : Fin S.count, i ≤ j ↔ index i ≤ k := by
    let K := Finset.univ.filter (fun i : Fin S.count => index i ≤ k)
    have hK : K.Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfirst]; exact Nat.zero_le k⟩⟩
    let j := K.max' hK
    have hj : index j ≤ k := (Finset.mem_filter.mp (K.max'_mem hK)).2
    refine ⟨j, fun i => ⟨fun hij => (hmono hij).trans hj, ?_⟩⟩
    intro hi
    exact K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  obtain ⟨a, ha⟩ := hcut 2
  obtain ⟨b, hb⟩ := hcut 3
  have hab : a ≤ b := (hb a).mpr (((ha a).mp le_rfl).trans (by omega))
  have hbLast : b.val + 1 < S.count := by
    have hb3 := (hb b).mp le_rfl
    have hne : b ≠ ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      intro he
      rw [he, hlast] at hb3
      omega
    have hvalne : b.val ≠ S.count - 1 := fun he => hne (Fin.ext he)
    omega
  have hnonzero (i : Fin S.count) (hi : 0 < i.val) : index i ≠ 0 := by
    intro hz
    have he : S.point i = S.first hn :=
      Subtype.ext (native_index_zero_point_unique S hf hn hzero _ (S.point i).property hz)
    have hi0 : i.val = 0 := congrArg Fin.val (S.point.injective he)
    omega
  have hnonone (i : Fin S.count) : index i ≠ 1 :=
    native_index_one_excluded S hone _ (S.point i).property
  refine ⟨a.val, b.val - a.val, ?_, by omega, ?_, by omega, ?_⟩
  · intro i hi hia
    have hi2 := (ha i).mp (show i ≤ a from hia)
    have hi0 := hnonzero i hi
    have hi1 := hnonone i
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 2
    omega
  · intro i hai hib
    have hi3 := (hb i).mp (show i ≤ b by change i.val ≤ b.val; omega)
    have hi2 : ¬index i ≤ 2 := fun he => (not_le_of_gt hai) ((ha i).mpr he)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 3
    omega
  · intro i hbi
    have hi3 : ¬index i ≤ 3 := fun he =>
      (by
        have hh : i.val ≤ b.val := (hb i).mpr he
        omega)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change 4 ≤ index i
    omega

def MorseCancellation.nativeMiddleBlockPoint {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) (j : Fin n) :
    ManifoldMorse.criticalPoints E f :=
  S.toSurgeryWindows.point ⟨r + j.val + 1, by omega⟩

end
