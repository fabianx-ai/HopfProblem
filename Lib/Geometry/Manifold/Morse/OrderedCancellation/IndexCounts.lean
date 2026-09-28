/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents

/-!
# Counting critical points by index

Bookkeeping for the numbers `nativeMorseCount E f k` of critical points of index `k`: removing a
pair of critical points of indices `k`, `k + 1` lowers the two counts by one and keeps the others
(`MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq`); when exactly one critical
point has index `0` it is the first window of a surgery system
(`native_index_zero_point_unique`); when index `1` does not occur no critical point has it
(`native_index_one_excluded`); indices along the value-ordered windows are monotone when the
function is index-ordered (`native_indices_monotone`); and the sublevel set below a window is
path-connected when all later windows transfer path-connectedness downward
(`ordered_upper_pathConnected_of_later_transfers`).  The attaching sphere of an index-`0` handle
is empty and that of an index-`1` handle has two points
(`unitSphere_isEmpty_of_finrank_zero`, `exists_distinct_unitSphere_points_of_finrank_one`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Let `S` be a surgery-window system of `f` on a compact path-connected manifold and `i` a
window index.  If for every later window `j > i` path-connectedness of the sublevel set at
`upper j` implies path-connectedness of the sublevel set at `lower j`, then the sublevel set at
`upper i` is path-connected. -/
theorem MorseCancellation.ordered_upper_pathConnected_of_later_transfers {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (htransfer :
      ∀ j : Fin S.count,
        i.val < j.val →
          PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
            PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) :
    PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
  have hall :
    ∀ k : ℕ,
      ∀ i : Fin S.count,
        S.count - 1 - i.val = k →
          (∀ j : Fin S.count,
              i.val < j.val →
                PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
                  PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) →
            PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki hindices
      have hpos : 0 < S.count := (Nat.zero_le i.val).trans_lt i.isLt
      by_cases hlast : i.val = S.count - 1
      · have hi : S.point i = S.last hpos := congrArg S.point (Fin.ext hlast)
        have hset : {x : M | f x ≤ S.upper (S.point i)} = Set.univ := by
          rw [hi]
          exact S.last_upper_univ hf hpos
        have hp : IsPathConnected {x : M | f x ≤ S.upper (S.point i)} :=
          hset.symm ▸ isPathConnected_univ
        exact isPathConnected_iff_pathConnectedSpace.mp hp
      · have hjlt : i.val + 1 < S.count := by omega
        let j : Fin S.count := ⟨i.val + 1, hjlt⟩
        have hjmeasure : S.count - 1 - j.val < k := by
          dsimp [j]
          omega
        have hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } :=
          ih _ hjmeasure j rfl (fun q hq => hindices q (by dsimp [j] at hq; omega))
        let : PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) } :=
          hindices j (by dsimp [j]; omega) hupper
        have hij : i < j := by change i.val < i.val + 1; omega
        obtain ⟨e, -⟩ :=
          FlowConstruction.exists_regularSublevelHomotopyEquiv hf
            (S.ordered_windows i j hij).le (S.consecutive_regular i j rfl)
        exact pathConnectedSpace_of_homotopyEquiv e
  exact hall _ i rfl htransfer

/-- If a surgery-window system `S` of `f` is nonempty and `f` has exactly one critical point of
index `0`, then every critical point of index `0` is the first window point `S.first hn`. -/
theorem MorseCancellation.native_index_zero_point_unique {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hn : 0 < S.count) (hcount : nativeMorseCount E f 0 = 1) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f z = 0 → z = (S.first hn).val := by
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  change
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hcount
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hfirstmem :
    (S.first hn).val ∈
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨(S.first hn).property, hfirst⟩
  rw [hz₀, Set.mem_singleton_iff] at hfirstmem
  intro z hz hi
  have hzmem :
    z ∈ {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨hz, hi⟩
  rw [hz₀, Set.mem_singleton_iff] at hzmem
  exact hzmem.trans hfirstmem.symm

/-- If `f` has no critical point of index `1` (`nativeMorseCount E f 1 = 0`), then no critical
point has index `1`. -/
theorem MorseCancellation.native_index_one_excluded {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hcount : nativeMorseCount E f 1 = 0) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 1 := by
  have hfinite :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

/-- The unit sphere of a normed space of dimension `0` is empty. -/
theorem MorseCancellation.unitSphere_isEmpty_of_finrank_zero {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] (hA : Module.finrank ℝ A = 0) :
    IsEmpty (PuncturedHandle.UnitSphere A) := by
  let _ : Subsingleton A := (Module.finrank_eq_zero_iff_of_free ℝ A).mp hA
  refine ⟨fun v => ?_⟩
  have hh := mem_sphere_zero_iff_norm.mp v.property
  rw [Subsingleton.elim (v : A) 0, norm_zero] at hh
  norm_num at hh

/-- The unit sphere of a normed space of dimension `1` has two distinct points. -/
theorem MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) : ∃ u v : Metric.sphere (0 : V) 1, u ≠ v := by
  obtain ⟨L⟩ :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := UnitSphereEquiv.homeomorph L
  let u : Metric.sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  let v : Metric.sphere (0 : ℝ) 1 := ⟨-1, by simp⟩
  refine ⟨e.symm u, e.symm v, ?_⟩
  intro heq
  have hh : u = v := e.symm.injective heq
  have hval : (1 : ℝ) = -1 := congrArg Subtype.val hh
  norm_num at hval

/-- If the critical set of `g` is that of `f` minus `{p, q}` with the same indices, the set of
critical points of `g` of index `k` is that of `f` minus `{p, q}`. -/
theorem MorseCancellation.indexed_criticalPoints_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M}
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    {z : M | z ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
    exact ⟨⟨hzf, (hindex z hz).symm.trans hi⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hi⟩, hzp, hzq⟩
    have hz := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hz, (hindex z hz).trans hi⟩

attribute [local instance 100] Classical.propDecidable in
/-- If the critical set of `g` is the finite critical set of `f` minus the two distinct critical
points `p`, `q`, with the same indices elsewhere, then
`count_g k + [index_f p = k] + [index_f q = k] = count_f k` for every `k`. -/
theorem MorseCancellation.nativeMorseCount_removed_of_index_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
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
  rw [indexed_criticalPoints_removed_of_index_eq hcrit hindex k]
  exact (Nat.add_assoc _ _ _).trans hc

/-- Removing two critical points of indices `k` and `k + 1` (as in
`nativeMorseCount_removed_of_index_eq`) lowers the counts of indices `k` and `k + 1` by one and
keeps all other counts. -/
theorem MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {k : ℕ} (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_removed_of_index_eq hfinite hp hq hpq hcrit hindex
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

/-- If the indices of `f` increase with the critical values, the function
`i ↦ nativeMorseIndex E f (S.point i)` on the windows of `S` is monotone. -/
theorem MorseCancellation.native_indices_monotone {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) :
    Monotone (fun i : Fin S.count => nativeMorseIndex E f (S.point i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact horder _ _ (S.point_strictMono hlt)
  · exact le_rfl

end
