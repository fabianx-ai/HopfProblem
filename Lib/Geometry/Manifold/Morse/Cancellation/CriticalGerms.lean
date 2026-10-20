/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Cubic.SurgeryWindowsExistence
import Lib.Geometry.Manifold.Morse.CubicFlow

/-!
# Critical points, germs and the Morse count after removing a pair

If two consecutive critical points `p`, `q` of a Morse function `f` are removed
by a modification supported in the band between the surgery windows, every
surviving critical point keeps its germ, the critical values stay distinct and
adapted surgery windows exist for the new function
(`surgery_pair_band_isolation`, `surviving_critical_germs_of_pair_band`,
`distinct_critical_values_of_surviving_germs`,
`adapted_surgeries_after_pair_removal`).

The Morse index depends only on the germ: a signed Morse chart of `f` at `p` is
a signed Morse chart of any `g` with the same germ
(`exists_signed_morse_chart_of_germ`), so `nativeMorseIndex E g p =
nativeMorseIndex E f p` (`nativeMorseIndex_congr_germ`), and the index is at
most the dimension (`nativeMorseIndex_le`). A function whose critical germs
are Morse is Morse (`MorseCancellationPreservation.isMorse_of_critical_germs`).

`nativeMorseCount E f k` is the number of critical points of index `k`.
Removing a pair of indices `k`, `k + 1` lowers the two counts by one and fixes
the others (`nativeMorseCount_after_pair_removal`,
`nativeMorseCount_adjacent_pair`), which is the bookkeeping of the
cancellation theorem, Milnor, *Lectures on the h-cobordism theorem*, §5.
The band strictly between two consecutive critical values contains no
critical point (`surgery_pair_inner_band_regular`).

## Tags

morse-theory, morse-index, critical-points
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Quadratic germs and surviving critical points -/

/-- A surgery pair's band isolation. -/
theorem MorseCancellation.surgery_pair_band_isolation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f,
      f z ∈ Set.Icc (S.lower p) (S.upper q) → z = p.val ∨ z = q.val := by
  intro z hz hband
  by_cases hzp : f z ≤ f p
  · exact Or.inl (S.isolated p z hz ⟨hband.1, hzp.trans (S.value_lt_upper p).le⟩)
  by_cases hqz : f q ≤ f z
  · exact Or.inr (S.isolated q z hz ⟨(S.lower_lt_value q).le.trans hqz, hband.2⟩)
  exact (hconsecutive ⟨z, hz⟩ ⟨lt_of_not_ge hzp, lt_of_not_ge hqz⟩).elim

/-- The surviving critical germs after removing a pair band. -/
theorem MorseCancellation.surviving_critical_germs_of_pair_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {l u : ℝ}
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hexterior : ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f) :
    ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f := by
  intro z hz
  obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
  apply hexterior z
  intro hband
  exact (hpair z hzf ⟨hband.1.le, hband.2.le⟩).elim hzp hzq

/-- The surviving critical points have distinct values. -/
theorem MorseCancellation.distinct_critical_values_of_surviving_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hsub : ManifoldMorse.criticalPoints E g ⊆ ManifoldMorse.criticalPoints E f)
    (hgerms : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) :
    Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
  intro x hx y hy hxy
  apply hinj (hsub hx) (hsub hy)
  rw [← (hgerms x hx).self_of_nhds, ← (hgerms y hy).self_of_nhds]
  exact hxy

/-- A signed Morse chart of a germ exists. -/
theorem MorseCancellation.exists_signed_morse_chart_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : ManifoldMorse.SignedMorseChart (E := E) g p,
      d.weights = c.weights ∧
        d.chart.source ⊆ c.chart.source ∧
          (∀ x, d.chart x = c.chart x) ∧ ∀ z, d.chart.symm z = c.chart.symm z := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let P := PartialChart.restrictSource c.chart hU
  let d : ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := P
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl, Set.inter_subset_left, fun _ => rfl, fun _ => rfl⟩

/-- Adapted surgeries after the pair removal. -/
theorem MorseCancellation.adapted_surgeries_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : ManifoldMorse.IsMorse E g)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val)
    (hexterior : ∀ z, f z ∉ Set.Ioo (S.lower p) (S.upper q) → g =ᶠ[𝓝 z] f) :
    (∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) ∧
      Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation S p q hconsecutive) hcrit
      hexterior
  have hinj :=
    distinct_critical_values_of_surviving_germs S.distinct (fun z hz => ((hcrit z).mp hz).1) hkeep
  exact ⟨hkeep, hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

attribute [local instance 100] Classical.propDecidable in
/-- The negative rank depends only on the germ. -/
theorem MorseCancellation.signed_morse_chart_negative_finrank_eq_of_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (d : ManifoldMorse.SignedMorseChart (E := E) g p) (hgerm : g =ᶠ[𝓝 p] f) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  obtain ⟨c', hw, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
  have heq := signed_morse_chart_negative_card_eq c' d
  rw [hw] at heq
  simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    MorseHandle.NegativeSpace, finrank_euclideanSpace] using heq

/-! ### The native Morse index -/

/-- The native index depends only on the germ. -/
theorem MorseCancellation.nativeMorseIndex_congr_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hgerm : g =ᶠ[𝓝 p] f) : nativeMorseIndex E g p = nativeMorseIndex E f p := by
  classical
  by_cases h : Nonempty (ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    obtain ⟨d, -, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
    rw [nativeMorseIndex_eq_chart c, nativeMorseIndex_eq_chart d]
    exact (signed_morse_chart_negative_finrank_eq_of_germ c d hgerm).symm
  · have hg : ¬Nonempty (ManifoldMorse.SignedMorseChart (E := E) g p) := by
      rintro ⟨d⟩
      obtain ⟨c, -, -, -, -⟩ := exists_signed_morse_chart_of_germ d hgerm.symm
      exact h ⟨c⟩
    simp only [nativeMorseIndex, dif_neg h, dif_neg hg]

/-- The native index is at most the dimension. -/
theorem MorseCancellation.nativeMorseIndex_le {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} :
    nativeMorseIndex E f p ≤ Module.finrank ℝ E := by
  classical
  by_cases h : Nonempty (ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    rw [nativeMorseIndex_eq_chart c]
    have hc := c.finrank_negative_add_positive
    omega
  · simp only [nativeMorseIndex, dif_neg h, Nat.zero_le]

/-! ### Morse functions from critical germs -/

/-- The Morse property transfers across equal germs. -/
theorem MorseCancellationPreservation.isMorseAt_of_same_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {x : M} (hf : ManifoldMorse.IsMorseAt E f x) (heq : g =ᶠ[𝓝 x] f) :
    ManifoldMorse.IsMorseAt E g x := by
  obtain ⟨e, he, hx, hgood⟩ := hf
  refine ⟨e, he, hx, ?_⟩
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.symm.continuousAt (e.map_source hx)
    rw [ContinuousAt, e.left_inv hx] at h
    exact h
  have hc : g ∘ e.symm =ᶠ[𝓝 (e x)] f ∘ e.symm := heq.comp_tendsto ht
  rw [hc.fderiv_eq, (hc.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact hgood

/-- A regular point of the replacement is Morse. -/
theorem MorseCancellationPreservation.isMorseAt_of_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {x : M}
    (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x ≠ 0) : ManifoldMorse.IsMorseAt E g x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  refine ⟨e, he, hx, Or.inl ?_⟩
  intro hc
  exact hreg ((ManifoldMorse.mem_criticalPoints_iff hg he hx).mpr hc)

/-- A function whose critical germs are Morse is Morse. -/
theorem MorseCancellationPreservation.isMorse_of_critical_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} (hf : ManifoldMorse.IsMorse E f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hkeep : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 → g =ᶠ[𝓝 x] f) :
    ManifoldMorse.IsMorse E g := by
  intro x
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
  · exact isMorseAt_of_same_germ (hf x) (hkeep x hx)
  · exact isMorseAt_of_regular hg hx

/-! ### The Morse count after pair removal -/

/-- The number of Morse critical points. -/
def MorseCancellation.nativeMorseCount (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (k : ℕ) : ℕ :=
  {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.ncard

/-- The indexed critical points after removing a pair. -/
theorem MorseCancellation.indexed_criticalPoints_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    {z : M | z ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hzg, hindex⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hzg
    rw [nativeMorseIndex_congr_germ (hkeep z hzg)] at hindex
    exact ⟨⟨hzf, hindex⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hindex⟩, hzp, hzq⟩
    have hzg := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hzg, (nativeMorseIndex_congr_germ (hkeep z hzg)).trans hindex⟩

attribute [local instance 100] Classical.propDecidable in
/-- The index-`k` Morse count of the new function plus the removed pair's index-`k` contributions equals that of the old. -/
theorem MorseCancellation.nativeMorseCount_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, if_pos hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, if_neg hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_after_pair_removal hcrit hkeep k]
  exact (Nat.add_assoc _ _ _).trans hc

attribute [local instance 100] Classical.propDecidable in
/-- Removing an adjacent-index pair lowers the counts at the two indices by one each and fixes the others. -/
theorem MorseCancellation.nativeMorseCount_adjacent_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) {k : ℕ}
    (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_after_pair_removal hfinite hp hq hpq hcrit hkeep
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

end

/-- If no critical value of `f` lies strictly between the values of the critical points `p` and
`q`, then a band `f ⁻¹' (Set.Icc a b)` with `f p < a` and `b < f q` contains no critical point of
`f`. -/
theorem MorseCancellation.surgery_pair_inner_band_regular {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    {a b : ℝ} (ha : f p < a) (hb : b < f q) :
    ∀ z, f z ∈ Set.Icc a b → z ∉ ManifoldMorse.criticalPoints E f := by
  intro z hz hcrit
  exact hconsecutive ⟨z, hcrit⟩ ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
