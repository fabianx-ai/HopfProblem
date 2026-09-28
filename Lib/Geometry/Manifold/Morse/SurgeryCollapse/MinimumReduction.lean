/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.Cubic
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts
import Lib.Geometry.Manifold.Morse.OrderedCancellation.MinimalSystem
import Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PairCancellation
import Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport

/-!
# A minimal Morse function on a connected manifold has one minimum and one maximum

If a Morse function on a compact path-connected manifold has more than one local minimum, some
`1`-handle joins two path components of the sublevel set below it
(`MorseCancellation.exists_native_one_handle_joining_components`); cancelling that `1`-handle
against the higher of the two minima (`cancel_realized_higher_minimum`, by the index-`0`/`1`
cancellation theorem) removes two critical points
(`exists_excellent_morse_reduction_of_multiple_minima`).  Hence a Morse function with the least
number of critical points among those with distinct critical values has exactly one minimum
(`minimal_excellent_morse_minimum_count_one`) and, applying this to `-f`, exactly one maximum
(`minimal_excellent_morse_extreme_counts_one`).  Cf. Milnor, *Lectures on the h-cobordism
theorem*, Theorem 8.1 and its corollary.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Let `S` be a surgery-window system of `f` on a compact path-connected manifold such that for
every index-`1` critical point `p` all core boundary points are joined in the lower sublevel set
to one point.  Then `f` has exactly one critical point of index `0`. -/
theorem MorseCancellation.native_minimum_count_one_of_one_handle_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcomponents :
      ∀ p : ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f p = 1 →
          ∃ a : { z : M // f z ≤ f p - (S.data p).radius ^ 2 },
            ∀ u, Joined ((S.data p).coreBoundaryMap u) a) :
    nativeMorseCount E f 0 = 1 := by
  classical
  have hn := S.count_pos hf
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => nativeMorseIndex E f (S.point i) = 0)
  have hK : K.Nonempty := ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩⟩
  let j : Fin S.count := K.max' hK
  have hjzero : nativeMorseIndex E f (S.point j) = 0 := (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have htail (i : Fin S.count) (hji : j.val < i.val)
    (hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) }) :
    PathConnectedSpace { x : M // f x ≤ S.lower (S.point i) } := by
    let : PathConnectedSpace { x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2 } :=
      hupper
    have hne : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hi
      have hm : i.val ≤ j.val := hmax i hi
      omega
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · obtain ⟨a, ha⟩ := hcomponents (S.point i) hone
      exact
        native_lower_pathConnected_of_attaching_component (S.data (S.point i)) hf.continuous a ha
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace { x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2 } :=
    ordered_upper_pathConnected_of_later_transfers S hf j htail
  let : IsEmpty { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 } :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  have hjfirst : j.val = 0 := by
    by_contra hj
    have hlt : (⟨0, hn⟩ : Fin S.count) < j := by change 0 < j.val; omega
    have hbelow : f (S.first hn) ≤ S.lower (S.point j) :=
      (S.value_lt_upper (S.first hn)).le.trans (S.ordered_windows _ _ hlt).le
    exact
      isEmptyElim
        (⟨S.first hn, hbelow⟩ :
          { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 })
  have hset :
    {x : M | x ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} =
      {(S.first hn).val} := by
    ext x
    constructor
    · rintro ⟨hx, hi⟩
      obtain ⟨i, he⟩ := S.point.surjective ⟨x, hx⟩
      have hi0 : nativeMorseIndex E f (S.point i) = 0 := by simpa only [he] using hi
      have hle : i.val ≤ j.val := hmax i hi0
      have hi0' : i.val = 0 := by omega
      have hip : S.point i = S.first hn := congrArg S.point (Fin.ext hi0')
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (he.symm.trans hip))
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ ⟨(S.first hn).property, hfirst⟩
  exact Set.ncard_eq_one.mpr ⟨(S.first hn).val, hset⟩

/-- If `f` on a compact path-connected manifold does not have exactly one minimum, there is an
index-`1` critical point `p` whose two core boundary points are not joined in the lower sublevel
set. -/
theorem MorseCancellation.exists_native_one_handle_joining_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : nativeMorseCount E f 0 ≠ 1) :
    ∃ p : ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f p = 1 ∧
        ∃ u v, ¬Joined ((S.data p).coreBoundaryMap u) ((S.data p).coreBoundaryMap v) := by
  classical
  by_contra h
  apply hmin
  apply native_minimum_count_one_of_one_handle_components S hf
  intro p hp
  have hindex : 0 < Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rw [← nativeMorseIndex_eq_chart (S.data p).chart, hp]
    exact zero_lt_one
  apply native_attaching_component_of_pairwise_joined (S.data p) hindex
  intro u v
  by_contra huv
  exact h ⟨p, hp, u, v, huv⟩

/-- Let `p`, `r`, `q` be critical points of `f₀` of indices `0`, `?`, `1` with `f₀ r < f₀ p < S.lower q`,
`V` a gradient-like field with flow `G` whose backward basin of `q` in the lower level is the
attaching sphere, with the attaching points `u`, `v` flowing to `p`, `r`, and no flow line from `q`
to another critical point.  Then there is a Morse function with distinct critical values and two
critical points fewer than `f₀`. -/
theorem MorseCancellation.cancel_realized_higher_minimum {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f₀ : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : ManifoldMorse.IsMorse E f₀) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ ManifoldMorse.criticalPoints E f₀,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : ManifoldMorse.criticalPoints E f₀) (hpzero : nativeMorseIndex E f₀ p = 0)
    (hqone : nativeMorseIndex E f₀ q = 1) (hrp : f₀ r < f₀ p) (hp : f₀ p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val))
    (hnoconnection :
      ∀ j : ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 j.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f₀).ncard := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => f₀ x.val) h).symm
  obtain ⟨hzback, hunique⟩ :=
    unique_connection_of_distinct_minimum_branches S hf₀.continuous G p r q hqone hpr hp u v hback
      hu hv
  obtain ⟨f, hf, hm, hcrit, hinj, -, -, hpq, hconsecutive, hdesc, hmodels, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf₀ hm₀ S.distinct hV G hG hzero hdesc₀ hmodels₀ p r q
      hrp (hp.trans (S.lower_lt_value q)) hnoconnection
  let pf : ManifoldMorse.criticalPoints E f := ⟨p.val, by rw [hcrit]; exact p.property⟩
  let qf : ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
  have hconsecutivef : ∀ z : ManifoldMorse.criticalPoints E f, ¬(f pf < f z ∧ f z < f qf) :=
    by
    intro z hz
    exact hconsecutive ⟨z.val, by rw [← hcrit]; exact z.property⟩ hz
  obtain ⟨T⟩ := ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels pf pf.property
  obtain ⟨cq, hcq⟩ := hmodels qf qf.property
  obtain ⟨g, hg, hmg, hcard, hcritg, hexterior⟩ :=
    cancel_unique_zero_one_connection cp cq hf hm ((hindices p p.property).trans hpzero)
      ((hindices q q.property).trans hqone) hV G hG (fun x hx => hzero x (hcrit ▸ hx)) hdesc hinj
      pf.property qf.property hpq (T.lower_lt_value pf) (T.value_lt_upper qf)
      (surgery_pair_band_isolation T pf qf hconsecutivef) hu hzback hunique hcp hcq
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation T pf qf hconsecutivef)
      hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinj (fun x hx => ((hcritg x).mp hx).1) hkeep
  exact ⟨g, hg, hmg, hinjg, hcard.trans (congrArg Set.ncard hcrit)⟩

/-- If a Morse function `f₀` with an `AdaptedWindows` package on a compact path-connected manifold
does not have exactly one minimum, there is a Morse function with distinct critical values and two
critical points fewer. -/
theorem MorseCancellation.exists_excellent_morse_reduction_of_multiple_minima {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f₀ : M → ℝ} (S : AdaptedWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : ManifoldMorse.IsMorse E f₀)
    (hmin : nativeMorseCount E f₀ 0 ≠ 1) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f₀).ncard := by
  obtain ⟨q, hqone, u, v, hnot⟩ :=
    exists_native_one_handle_joining_components S.toSurgeryWindows hf₀ hmin
  obtain
    ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr, hp, hr, hback, hu, hv, -,
      hnoconnection⟩ :=
    S.realize_one_handle_minimum_branches hf₀ q hqone u v hnot
  have hmodels (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f₀) :
    ∃ c : ManifoldMorse.SignedMorseChart (E := E) f₀ x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(S.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, S.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hne : f₀ p ≠ f₀ r := fun h => hpr (Subtype.ext (S.distinct p.property r.property h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels r p q
        hrzero hqone hlt hr v u hback hv hu (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels p r q
        hpzero hqone hgt hp u v hback hu hv hnoconnection

/-- Milnor, h-cobordism Theorem 8.1: a Morse function with an `AdaptedWindows` package on a compact
path-connected manifold with the least number of critical points among Morse functions with
distinct critical values has exactly one critical point of index `0`. -/
theorem MorseCancellation.minimal_excellent_morse_minimum_count_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 := by
  by_contra hmin
  obtain ⟨g, hg, hmg, hinjg, hcount⟩ :=
    exists_excellent_morse_reduction_of_multiple_minima S hf hm hmin
  exact minimal_excellent_morse_forbids_pair_removal hminimal hg hmg hinjg hcount

/-- A minimal Morse function as in `minimal_excellent_morse_minimum_count_one` has exactly one
critical point of index `0` and exactly one of index `dim E`. -/
theorem MorseCancellation.minimal_excellent_morse_extreme_counts_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 := by
  refine ⟨minimal_excellent_morse_minimum_count_one S hf hm hminimal, ?_⟩
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have hmin :=
    minimal_excellent_morse_minimum_count_one T hf.neg (isMorse_neg hm)
      (minimal_excellent_morse_neg hminimal)
  have hcounts := nativeMorseCount_neg hf hm (le_refl (Module.finrank ℝ E))
  rw [Nat.sub_self] at hcounts
  exact hcounts.symm.trans hmin

end
