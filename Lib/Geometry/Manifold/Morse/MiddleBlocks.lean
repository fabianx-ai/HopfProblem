/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.CutTransport

/-!
# Middle blocks of adapted Morse windows

Second batch of stock results on the middle critical points of a Morse function on a compact
manifold between two regular cut values, joining the ordered-cancellation chain
(`Lib.Geometry.Manifold.Morse.AdaptedWindows`) with the belt chain
(`Lib.Geometry.Manifold.Morse.BeltCancellation`):

* counting of the native middle block (`MorseCancellation.nativeMorseCount_eq_interval_length`,
  `native_middle_block_counts`, `native_middle_block_complete_and_cut`,
  `middle_blocks_complete_of_no_four_five`, `critical_pair_of_surgery_count_two`);
* the canonical cut sequence (`MorseCancellation.nativeMiddleBaseCut`, `nativeMiddleCutSequence`,
  `nativeMiddleCutSequence_bands`, `lower_cuts_preserved_of_critical_bound`,
  `AdaptedWindows.no_connection_above_canonical_cut`, `exists_common_cut_value_exchange`,
  `exists_relative_surgery_cut_transport`);
* native middle basin families (`MorseCancellation.nativeMiddleBasinFamily_equalCut`,
  `nativeMiddleBasinFamily_labels_injective`, `nativeMiddleBasinFamily_replace_zero`,
  `nativeMiddleBasinFamily_reindex`, `nativeIndexThreeAttachingSphere_regular`);
* basin sections reaching compact sections and core inclusions
  (`AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section`,
  `backward_basin_reaches_compact_section`, `exists_native_core_inclusion_equiv`,
  `cancel_single_basin_section_isotopy`);
* sphere maps with the same image (`MorseCancellation.same_image_sphere_maps_unit`,
  `same_image_section_classes_unit`, `attaching_contributions_opposite_of_relative_det_neg`);
* centered passages with prescribed normal factors
  (`MorseCancellation.exists_centered_passage_normal_factors`,
  `opposite_centered_passages_of_normal_factors`, `exists_native_opposite_centered_passages`);
* belt intersections (`ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul`,
  `exists_transverse_representative`) and separated neighborhoods
  (`LocalDegree.SeparatedNeighborhoods.pointComplementInclusion`,
  `componentConnecting_singlePoint`).

Moved verbatim from `Hopf/Recognition.lean` (statements unchanged; qualifier retarget
`PeriodTorusHigherHomology.{homeomorphHomologyEquiv, singularHomologyMap_comp,
singularHomologyMap_id} -> SingularHomology.*`, naming the same constants).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

theorem MorseCancellation.nativeMorseCount_eq_interval_length {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (k a b : ℕ) (hab : a ≤ b) (hb : b ≤ S.count)
    (hindex : ∀ i : Fin S.count, nativeMorseIndex E f (S.point i) = k ↔ a ≤ i.val ∧ i.val < b) :
    nativeMorseCount E f k = b - a := by
  let K : Set M := {x | x ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k}
  let u : Fin (b - a) → K := fun j =>
    ⟨(S.point ⟨a + j.val, by omega⟩).val, (S.point ⟨a + j.val, by omega⟩).property,
      (hindex ⟨a + j.val, by omega⟩).mpr
        (show a ≤ a + j.val ∧ a + j.val < b from ⟨by omega, by omega⟩)⟩
  have hu : Function.Bijective u := by
    constructor
    · intro i j hij
      have hv : (u i).val = (u j).val := congrArg Subtype.val hij
      have hp : S.point ⟨a + i.val, by omega⟩ = S.point ⟨a + j.val, by omega⟩ := Subtype.ext hv
      have he := congrArg Fin.val (S.point.injective hp)
      exact Fin.ext (by simpa only [Nat.add_left_cancel_iff] using he)
    · intro x
      let i := S.point.symm ⟨x.val, x.property.1⟩
      have hi : S.point i = ⟨x.val, x.property.1⟩ := S.point.apply_symm_apply _
      have hxi : nativeMorseIndex E f (S.point i) = k := by
        rw [hi]
        exact x.property.2
      have hib := (hindex i).mp hxi
      refine ⟨⟨i.val - a, by omega⟩, ?_⟩
      apply Subtype.ext
      change (S.point ⟨a + (i.val - a), _⟩).val = x.val
      have he : (⟨a + (i.val - a), by omega⟩ : Fin S.count) = i :=
        Fin.ext (show a + (i.val - a) = i.val by omega)
      rw [he, hi]
  have hc := (Nat.card_congr (Equiv.ofBijective u hu)).symm
  change K.ncard = b - a
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_fin] using hc

theorem MorseCancellation.native_middle_block_counts {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    nativeMorseCount E f 2 = r ∧ nativeMorseCount E f 3 = c := by
  have hn := S.count_pos hf
  have hi0 (i : Fin S.count) (hi : i.val = 0) : nativeMorseIndex E f (S.point i) = 0 := by
    have he : i = ⟨0, hn⟩ := Fin.ext hi
    rw [he]
    exact (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hi2 (i : Fin S.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
    nativeMorseIndex E f (S.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin S.count) (hri : r < i.val) (hic : i.val ≤ r + c) :
    nativeMorseIndex E f (S.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (hthree i hri hic)
  have hi4 (i : Fin S.count) (hic : r + c < i.val) : 4 ≤ nativeMorseIndex E f (S.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    exact hafter i hic
  have hcases (i : Fin S.count) :
    (i.val = 0 ∧ nativeMorseIndex E f (S.point i) = 0) ∨
      (0 < i.val ∧ i.val ≤ r ∧ nativeMorseIndex E f (S.point i) = 2) ∨
        (r < i.val ∧ i.val ≤ r + c ∧ nativeMorseIndex E f (S.point i) = 3) ∨
          (r + c < i.val ∧ 4 ≤ nativeMorseIndex E f (S.point i)) := by
    by_cases hz : i.val = 0
    · exact Or.inl ⟨hz, hi0 i hz⟩
    by_cases hr : i.val ≤ r
    · exact Or.inr (Or.inl ⟨by omega, hr, hi2 i (by omega) hr⟩)
    by_cases hrc : i.val ≤ r + c
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, hrc, hi3 i (by omega) hrc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hi4 i (by omega)⟩))
  constructor
  · have hh :=
      nativeMorseCount_eq_interval_length S 2 1 (r + 1) (by omega) (by omega)
        (fun i => by have h := hcases i; omega)
    simpa only [Nat.add_sub_cancel_right] using hh
  · have hh :=
      nativeMorseCount_eq_interval_length S 3 (r + 1) (r + c + 1) (by omega) (by omega)
        (fun i => by have h := hcases i; omega)
    have he : r + c + 1 - (r + 1) = c := by omega
    simpa only [he] using hh

theorem AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section {E M X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [TopologicalSpace X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)]
    [PreconnectedSpace (Hemisphere.Sphere n)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (α : C(X, { y : M // f y = a })) (x₀ : X)
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val)) :
    ∀ u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((S.data p).surgery.attachingSphere u).val ∈
        FlowCancellation.levelBasin S.flow f a := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  have hback (x : X) := (hfull (α x)).mp (Set.mem_range_self x)
  have hreach (x : X) :=
    S.backward_basin_reaches_attaching_level hf p (ha (α x).val (α x).property) (hback x)
  obtain ⟨t₀, ht₀⟩ := hreach x₀
  obtain ⟨D, hsource, htarget, horbit⟩ :=
    S.exists_native_level_basin_transport hf ha (S.data p).lower_regular (α x₀)
      ⟨S.flow t₀ (α x₀).val, ht₀⟩
  have hsrc (x : X) : α x ∈ D.source := hsource.symm ▸ hreach x
  let β : X → (S.data p).LowerLevel := D ∘ α
  have hβ : Continuous β := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact
      (D.contMDiffOn_toFun.continuousOn.continuousAt (D.open_source.mem_nhds (hsrc x))).comp
        α.continuous.continuousAt
  have hβback (x : X) : Filter.Tendsto (fun t => S.flow t (β x).val) Filter.atBot (𝓝 p.val) := by
    obtain ⟨t, ht⟩ := horbit (α x) (hsrc x)
    change Filter.Tendsto (fun t => S.flow t (D (α x)).val) Filter.atBot (𝓝 p.val)
    rw [← ht]
    exact (MorseCancellation.flow_time_atBot_limit_iff S.flow t (α x).val p.val).mpr (hback x)
  let e :=
    (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
        n).toHomeomorph
  let A : C(Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    (S.data p).surgery.attachingSphere.comp (e : C(_, _))
  let U : Set (Hemisphere.Sphere n) := A ⁻¹' D.target
  have hUeq : U = A ⁻¹' Set.range β := by
    ext u
    constructor
    · intro hu
      have hxu : D.symm (A u) ∈ D.source := D.map_target' hu
      have hright : D (D.symm (A u)) = A u := D.right_inv' hu
      obtain ⟨t, ht⟩ := horbit (D.symm (A u)) hxu
      rw [hright] at ht
      have hAback : Filter.Tendsto (fun t => S.flow t (A u).val) Filter.atBot (𝓝 p.val) :=
        (S.attaching_basin_iff hf p (A u)).mpr ⟨e u, rfl⟩
      have hxb : Filter.Tendsto (fun t => S.flow t (D.symm (A u)).val) Filter.atBot (𝓝 p.val) := by
        rw [← ht] at hAback
        exact (MorseCancellation.flow_time_atBot_limit_iff S.flow t (D.symm (A u)).val p.val).mp hAback
      obtain ⟨x, hx⟩ := (hfull (D.symm (A u))).mpr hxb
      exact ⟨x, (congrArg D hx).trans hright⟩
    · rintro ⟨x, hx⟩
      change A u ∈ D.target
      rw [← hx]
      exact D.map_source' (hsrc x)
  have hUopen : IsOpen U := D.open_target.preimage A.continuous
  have hUclosed : IsClosed U := by
    rw [hUeq]
    exact (isCompact_range hβ).isClosed.preimage A.continuous
  have hUne : U.Nonempty := by
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p (β x₀)).mp (hβback x₀)
    obtain ⟨v, hv⟩ := e.surjective u
    refine ⟨v, ?_⟩
    change A v ∈ D.target
    have heq : A v = β x₀ := by change (S.data p).surgery.attachingSphere (e v) = _; rw [hv, hu]
    rw [heq]
    exact D.map_source' (hsrc x₀)
  have hUall : U = Set.univ := IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne
  intro u
  obtain ⟨v, rfl⟩ := e.surjective u
  have hv : A v ∈ D.target := show v ∈ U from hUall.symm ▸ Set.mem_univ v
  rw [htarget] at hv
  exact hv

theorem MorseCancellation.nativeIndexThreeAttachingSphere_regular {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) :
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (nativeIndexThreeAttachingSphere S p hp) ∧
      Topology.IsClosedEmbedding (nativeIndexThreeAttachingSphere S p hp) ∧
        ∀ x,
          Function.Injective
            (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E)
              (nativeIndexThreeAttachingSphere S p hp) x) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2
  have hs :
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (nativeIndexThreeAttachingSphere S p hp) :=
    ((S.data p).attaching_smooth hf 2).comp e.contMDiff
  have hi : Function.Injective (nativeIndexThreeAttachingSphere S p hp) :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  refine ⟨hs, hs.continuous.isClosedEmbedding hi, ?_⟩
  intro x
  change
    Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e) x)
  rw [mfderiv_comp x (((S.data p).attaching_smooth hf 2).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
  exact
    ((S.data p).attaching_derivative_injective hf 2 (e x)).comp
      (e.mfderivToContinuousLinearEquiv (by simp) x).injective

theorem AdaptedWindows.exists_native_core_inclusion_equiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) :
    ∃ e :
      ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range (S.data p).coreMap) ≃ₕ
        { y : M // f y ≤ S.toSurgeryWindows.upper p },
      ∀ x, (e x).val = x.val := by
  let d := S.data p
  have hagreement :
    ∀ x ∈ Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block),
      ∀ᶠ y in 𝓝 x, S.field y = d.chart.descentField y := by
    rintro x ⟨z, rfl⟩
    exact S.model_germ p _ (MorseHandle.modelMap_mem_product d.radius_pos z)
  obtain ⟨B, hB⟩ :=
    d.chart.exists_attachingUnionHomotopyEquiv hf S.smooth S.zero S.descent S.flow S.integral
      d.radius d.radius_pos d.block hagreement (S.isolated p)
  let C :=
    ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ S.toSurgeryWindows.lower p}
      d.handleMap (isClosed_le hf.continuous continuous_const)
      (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
      (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)
  exact ⟨C.trans B, fun x => hB (C x)⟩

def MorseCancellation.nativeMiddleBaseCut {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) : ℝ :=
  S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r, by omega⟩)

def MorseCancellation.nativeMiddleCutSequence {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) :
    Fin (n + 1) → ℝ :=
  Fin.cases (nativeMiddleBaseCut S r n hn)
    (fun j => T.toSurgeryWindows.upper (nativeMiddleBlockPoint S r n hn j))

theorem MorseCancellation.nativeMiddleCutSequence_bands {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hn <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j)) :
    let p := nativeMiddleBlockPoint S r n hn
    let cut := nativeMiddleCutSequence S T r n hn
    (∀ i, cut 0 ≤ cut i) ∧
      (∀ j, cut j.succ = T.toSurgeryWindows.upper (p j)) ∧
        (∀ j, cut j.castSucc < T.toSurgeryWindows.lower (p j)) ∧
          ∀ j y,
            f y ∈ Set.Icc (cut j.castSucc) (T.toSurgeryWindows.lower (p j)) →
              y ∉ ManifoldMorse.criticalPoints E f := by
  let p := nativeMiddleBlockPoint S r n hn
  let cut := nativeMiddleCutSequence S T r n hn
  have hbase (i : Fin (n + 1)) : cut 0 ≤ cut i := by
    cases i using Fin.cases with
    | zero => exact le_rfl
    | succ j =>
      exact
        ((hbefore j).trans
            ((T.toSurgeryWindows.lower_lt_value (p j)).trans
              (T.toSurgeryWindows.value_lt_upper (p j)))).le
  have hstep (j : Fin n) : cut j.castSucc < T.toSurgeryWindows.lower (p j) := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact hbefore 0
      | succ
        j =>
        change T.toSurgeryWindows.upper (p j.castSucc) < T.toSurgeryWindows.lower (p j.succ)
        apply T.separated
        apply S.toSurgeryWindows.point_strictMono
        change r + j.val + 1 < r + (j.val + 1) + 1
        omega
  have hpred (j : Fin n) : f (S.toSurgeryWindows.point ⟨r + j.val, by omega⟩) < cut j.castSucc := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact S.toSurgeryWindows.value_lt_upper _
      | succ j => exact T.toSurgeryWindows.value_lt_upper (p j.castSucc)
  refine ⟨hbase, fun _ => rfl, hstep, ?_⟩
  intro j y hy hcrit
  have hconsecutive :=
    S.toSurgeryWindows.point_consecutive ⟨r + j.val, by omega⟩ ⟨r + j.val + 1, by omega⟩ rfl
  exact
    hconsecutive ⟨y, hcrit⟩
      ⟨(hpred j).trans_le hy.1, hy.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p j))⟩

theorem AdaptedWindows.no_connection_above_canonical_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hq : MorseCancellation.nativeMorseIndex E f q = 3) {a : ℝ} (hap : a < f p)
    (γ : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  let e := SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2
  intro x hx
  have hplower : f p < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq)
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hx.1
      hx.2 (S.toSurgeryWindows.lower_lt_value q) hplower
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff S.flow t x q.val).mpr hx.1
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  obtain ⟨z, hz⟩ := e.surjective u
  have hpoint : MorseCancellation.nativeIndexThreeAttachingSphere S q hq z = y := by
    change (S.data q).surgery.attachingSphere (e z) = y
    exact (congrArg (S.data q).surgery.attachingSphere (show e z = u from hz)).trans hu
  obtain ⟨s, hs⟩ := horbit z
  rw [hpoint] at hs
  have hyforward : Filter.Tendsto (fun v => S.flow v y.val) Filter.atTop (𝓝 p.val) :=
    (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mpr hx.2
  have hγforward := (MorseCancellation.flow_time_atTop_limit_iff S.flow s y.val p.val).mpr hyforward
  rw [hs] at hγforward
  have hheight : Filter.Tendsto (fun v => f (S.flow v (γ z).val)) Filter.atTop (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hγforward
  have hh :=
    (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
          (γ z).val).le_of_tendsto
      hheight 0
  have hpa : f p ≤ a := by simpa only [S.flow.map_zero_apply, (γ z).property] using hh
  exact not_le_of_gt hap hpa

theorem MorseCancellation.lower_cuts_preserved_of_critical_bound {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l a : ℝ} (ha : a < l) (hexterior : ∀ y, f y ≤ l → g =ᶠ[𝓝 y] f)
    (hcritical : ∀ y ∈ ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    (∀ y, g y ≤ a ↔ f y ≤ a) ∧ (∀ y, g y = a ↔ f y = a) ∧ ∀ y, f y ≤ a → g =ᶠ[𝓝 y] f := by
  have hbound :=
    superlevel_bound_of_critical_bound hf hg
      (fun y hy => (hexterior y hy.le).self_of_nhds.trans hy) hcritical
  have hbelow (y : M) (hy : g y ≤ a) : f y ≤ l := by
    by_contra h
    exact (ha.trans_le (hbound y (le_of_not_ge h))).not_ge hy
  refine ⟨?_, ?_, fun y hy => hexterior y (hy.trans ha.le)⟩
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy)).self_of_nhds) ▸ hy
    · intro hy
      rw [(hexterior y (hy.trans ha.le)).self_of_nhds]
      exact hy
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy.le)).self_of_nhds).symm.trans hy
    · intro hy
      exact (hexterior y (hy ▸ ha.le)).self_of_nhds.trans hy

theorem AdaptedWindows.exists_common_cut_value_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hq : MorseCancellation.nativeMorseIndex E f q = 3) (hal : a < S.toSurgeryWindows.lower p)
    (γ : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ z,
                      f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                        g =ᶠ[𝓝 z] f) ∧
                    (∀ z ∈ ManifoldMorse.criticalPoints E f,
                        z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                      (∀ z ∈ ManifoldMorse.criticalPoints E f,
                          MorseCancellation.nativeMorseIndex E g z =
                            MorseCancellation.nativeMorseIndex E f z) ∧
                        (∀ k,
                            MorseCancellation.nativeMorseCount E g k =
                              MorseCancellation.nativeMorseCount E f k) ∧
                          (∀ y, g y ≤ a ↔ f y ≤ a) ∧
                            (∀ y, g y = a ↔ f y = a) ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                (∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g) ∧
                                  ∃ T : AdaptedWindows E g,
                                    T.field = S.field ∧
                                      T.flow = S.flow ∧
                                        (∀ r : ManifoldMorse.criticalPoints E g,
                                            g r < a → T.toSurgeryWindows.upper r < a) ∧
                                          ∀ r : ManifoldMorse.criticalPoints E g,
                                            a < g r → a < T.toSurgeryWindows.lower r := by
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  have hnoconnection :=
    S.no_connection_above_canonical_cut hf p q hpq hq
      (hal.trans (S.toSurgeryWindows.lower_lt_value p)) γ horbit
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdesc, hexterior, hpgerm, hqgerm, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm S.smooth S.flow
      S.integral S.zero S.descent S.distinct (S.data p).chart (S.data q).chart
      (S.critical_model_germ p) (S.critical_model_germ q) hpband hqband hpq hqband hpband
      (MorseCancellation.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hnoconnection
  have hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      MorseCancellation.injOn_of_exchanged_values S.distinct p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels (r : ManifoldMorse.criticalPoints E g) :
    ∃ c : ManifoldMorse.SignedMorseChart (E := E) g r.val,
      ∀ᶠ y in 𝓝 r.val, S.field y = c.descentField y := by
    have hr : r.val ∈ ManifoldMorse.criticalPoints E f := hcrit ▸ r.property
    by_cases hrp : r.val = p.val
    · obtain ⟨c, hc⟩ :=
        MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field (S.data p).chart
          hpgerm
      rw [hrp]
      exact ⟨c, hc ▸ S.critical_model_germ p⟩
    by_cases hrq : r.val = q.val
    · obtain ⟨c, hc⟩ :=
        MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field (S.data q).chart
          hqgerm
      rw [hrq]
      exact ⟨c, hc ▸ S.critical_model_germ q⟩
    obtain ⟨c, hc⟩ :=
      MorseCancellation.exists_signed_morse_chart_of_germ_preserving_field (S.data ⟨r.val, hr⟩).chart
        (hothers r hr hrp hrq)
    exact ⟨c, hc ▸ S.critical_model_germ ⟨r.val, hr⟩⟩
  have hout (y : M) (hy : f y ≤ S.toSurgeryWindows.lower p) : g =ᶠ[𝓝 y] f :=
    hexterior y (fun h => h.1.not_ge hy)
  have hbound (y : M) (hy : y ∈ ManifoldMorse.criticalPoints E g)
    (hfy : S.toSurgeryWindows.lower p ≤ f y) : S.toSurgeryWindows.lower p ≤ g y := by
    by_cases hyp : y = p.val
    · rw [hyp, hgp]
      exact hqband.1.le
    by_cases hyq : y = q.val
    · rw [hyq, hgq]
      exact hpband.1.le
    rw [(hothers y (hcrit ▸ hy) hyp hyq).self_of_nhds]
    exact hfy
  obtain ⟨hsub, hlevel, hgerm⟩ :=
    MorseCancellation.lower_cuts_preserved_of_critical_bound hf.continuous hg hal hout hbound
  have hga (y : M) (hy : g y = a) : y ∉ ManifoldMorse.criticalPoints E g := by
    rw [hcrit]
    exact ha y ((hlevel y).mp hy)
  choose c hc using hnewmodels
  obtain ⟨T₀, hfield₀, hflow₀, -⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow hg hmg hinjg S.smooth S.flow
      S.integral (fun x hx => S.zero x (hcrit ▸ hx)) (fun x hx => hdesc x (hcrit ▸ hx)) c hc
  obtain ⟨T, hfield, hflow, -, hbelow, habove⟩ :=
    T₀.exists_same_flow_windows_avoiding_level hg hmg hga
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hexterior, hothers, hindices,
      MorseCancellation.nativeMorseCount_eq_of_preserved_indices hcrit hindices, hsub, hlevel, hgerm,
      hga, T, hfield.trans hfield₀, hflow.trans hflow₀, hbelow, habove⟩

theorem MorseCancellation.nativeMiddleBasinFamily_equalCut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} {a : ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hlevel : ∀ y, g y = a ↔ f y = a) (hflow : T.flow = S.flow) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) :
    IsNativeMiddleBasinFamily T hg hga (fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩)
      (fun j => equalCutSection hlevel (γ j)) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hg hga
  let e := equalLevelDiffeomorph hf hg ha hga hlevel
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hγ
  have hβs (j : Fin n) :
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (equalCutSection hlevel (γ j)) := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (e ∘ γ j)
    exact e.contMDiff.comp (hs j)
  refine ⟨hβs, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (hβs j).continuous.isClosedEmbedding
    change Function.Injective (e ∘ γ j)
    exact e.injective.comp (he j).injective
  · intro j x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ γ j) x)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp))
        ((hs j).mdifferentiableAt (by simp))]
    exact (e.mfderivToContinuousLinearEquiv (by simp) (γ j x)).injective.comp (hi j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hiy hjy
    obtain ⟨x, hx⟩ := hiy
    obtain ⟨z, hz⟩ := hjy
    have hsame : γ i x = γ j z := e.injective (hx.trans hz.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨z, hsame.symm⟩
  · intro j y
    have hmem : y ∈ Set.range (equalCutSection hlevel (γ j)) ↔ e.symm y ∈ Set.range (γ j) := by
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply e.injective
        exact hx.trans (e.apply_symm_apply y).symm
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem, hfull j]
    rw [hflow]
    rfl

theorem MorseCancellation.nativeMiddleBasinFamily_labels_injective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) : Function.Injective p := by
  intro i j hij
  by_contra hne
  let x : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
  have hbasin := (hγ.2.2.2.2 i (γ i x)).mp (Set.mem_range_self x)
  have hj : γ i x ∈ Set.range (γ j) := by
    apply (hγ.2.2.2.2 j (γ i x)).mpr
    simpa only [hij] using hbasin
  exact Set.disjoint_left.mp (hγ.2.2.2.1 hne) (Set.mem_range_self x) hj

theorem AdaptedWindows.backward_basin_reaches_compact_section {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (α : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val))
    {x : M} (hx : x ∉ ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)) :
    x ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach :=
    S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α
      (Hemisphere.point Bool.true ⟨0, by simp⟩) hfull
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p hx hback
  let y : (S.data p).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 p.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff S.flow t x p.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p y).mp hyback
  apply (FlowCancellation.levelBasin_flow_iff S.flow f a t x).mp
  change y.val ∈ FlowCancellation.levelBasin S.flow f a
  rw [← hu]
  exact hreach u

theorem AdaptedWindows.exists_relative_surgery_cut_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (q : ManifoldMorse.criticalPoints E f) (z : (S.data q).UpperLevel)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K P : Set (S.data q).UpperLevel),
      IsCompact K →
        SupportedDiffeomorph.SupportedRelativeIsotopy D K P →
          ∃ T : AdaptedWindows E f,
            (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < ε p) ∧
                (∀ p ∈ ManifoldMorse.criticalPoints E f,
                    ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
                  (∀ x : (S.data q).UpperLevel,
                      ∀ p : M,
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
                          Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p)) ∧
                    (∀ x : (S.data q).UpperLevel,
                        ∀ p : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
                            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        (∀ x : (S.data q).UpperLevel,
                            ∀ {b : ℝ},
                              b < f q →
                                (∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) →
                                  ∀ y : { z : M // f z = b },
                                    (∃ t : ℝ, T.flow t x.val = y.val) ↔
                                      ∃ t : ℝ, S.flow t (D x).val = y.val) ∧
                          ∀ p : M,
                            f p ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t p) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t p) Filter.atTop (𝓝 v) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro D K P hK I
  obtain ⟨l, u, hl, hu, hband⟩ := S.regular_interval_around_level (S.data q).upper_regular
  have hql : f q < l := by
    by_contra h
    exact
      hband q ⟨le_of_not_gt h, (S.toSurgeryWindows.value_lt_upper q).le.trans hu.le⟩ q.property
  obtain
    ⟨r, C, W, V, H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright, hprotected⟩ :=
    FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hu hband (S.data q).upper_regular z D K P hK I
  have hmodel (p : ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct hV G hG
      (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback₀, hforward₀⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val D
      (fun x p => (hgeometry x).2.1 p) (fun x p => (hgeometry x).2.2 p) hend hleft hright
  have hback (x : (S.data q).UpperLevel) (p : M) :
    Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
      Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) := by
    rw [hflow]
    exact hback₀ x p
  have hforward (x : (S.data q).UpperLevel) (p : M) :
    Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
      Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p) := by
    rw [hflow]
    exact hforward₀ x p
  have hlowexit {b : ℝ} (hb : b < f q) : b < S.toSurgeryWindows.upper q - r := by
    have hr' : r < S.toSurgeryWindows.upper q - l := hrbound
    linarith
  have htransport (x : (S.data q).UpperLevel) {b : ℝ} (hb : b < f q) (y : { z : M // f z = b })
    (hxy : ∃ t : ℝ, T.flow t x.val = y.val) : ∃ t : ℝ, S.flow t (D x).val = y.val := by
    obtain ⟨t, ht⟩ := hxy
    have hstart : f (T.flow 1 x.val) = S.toSurgeryWindows.upper q - r := by
      rw [hflow, hend, hheight]
      rfl
    have htone : 1 < t := by
      by_contra h
      have hh :=
        (FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x.val)
          (le_of_not_gt h)
      change f (T.flow 1 x.val) ≤ f (T.flow t x.val) at hh
      rw [hstart, ht, y.property] at hh
      exact (hlowexit hb).not_ge hh
    have heq : G t x.val = H t (D x).val := by
      calc
        G t x.val = G (t - 1) (G 1 x.val) := by rw [← G.map_add, sub_add_cancel]
        _ = H (t - 1) (H 1 (D x).val) := by
          rw [hend, hright (D x) (t - 1) (sub_nonneg.mpr htone.le)]
        _ = H t (D x).val := by rw [← H.map_add, sub_add_cancel]
    have hmem : H t (D x).val ∈ Set.range (fun s => S.flow s (D x).val) :=
      (hgeometry (D x).val).1 ▸ Set.mem_range_self t
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.trans (heq.symm.trans (hflow ▸ ht))⟩
  refine ⟨T, hcharts, hradii, ?_, hback, hforward, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = fun t => H t x.val := funext (hprotected x hx)
    rw [heq]
    exact (hgeometry x.val).1
  · intro x b hbq hb y
    refine ⟨htransport x hbq y, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ :=
      S.reaches_cut_of_forward_holonomy T hf (hbq.trans (S.toSurgeryWindows.value_lt_upper q)) hb
        (S.data q).upper_regular D hforward x y ⟨t, ht⟩
    let y' : { z : M // f z = b } := ⟨T.flow s x.val, hs⟩
    obtain ⟨v, hv⟩ := htransport x hbq y' ⟨s, rfl⟩
    have hshared : S.flow 0 y'.val = S.flow (v - t) y.val := by
      rw [S.flow.map_zero_apply, ← hv, ← ht, ← S.flow.map_add, sub_add_cancel]
    have heq : y'.val = y.val :=
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) y'.property y.property hshared
    exact ⟨s, heq⟩
  · intro p hp
    have hlow (y : M) (hy : f y ≤ l) : T.field y = W y := by
      rw [hfield]
      exact (houtside y (fun h => (hCband h).1.not_ge hy)).self_of_nhds
    have hb :=
      MorseCancellation.lower_backward_basins_preserved S T hf hW H hH hgeometry hlow p
        (hp.trans hql.le)
    exact
      ⟨hb.1, hb.2,
        MorseCancellation.lower_forward_basins_preserved S T hf hW H hH (fun x v => (hgeometry x).2.1 v)
          hlow p (hp.trans hql.le)⟩

theorem MorseCancellation.same_image_sphere_maps_unit {Y : Type} [TopologicalSpace Y]
    (α β : C((Hemisphere.Sphere 2), Y)) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap β 2 =
          k • SingularMayerVietoris.singularHomologyMap α 2 := by
  let e : (Hemisphere.Sphere 2) ≃ₜ (Hemisphere.Sphere 2) :=
    hβ.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans hα.toHomeomorph.symm)
  have heq : α.comp (e : C((Hemisphere.Sphere 2), (Hemisphere.Sphere 2))) = β := by
    apply ContinuousMap.ext
    intro x
    have hh :=
      congrArg Subtype.val
        (hα.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hβ.toHomeomorph x)))
    exact hh
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (e : C((Hemisphere.Sphere 2), (Hemisphere.Sphere 2))) 2) :=
    (SingularHomology.homeomorphHomologyEquiv e 2).bijective
  obtain ⟨k, hk, hu⟩ :=
    two_sphere_map_unit_of_homology_bijective (Homeomorph.refl (Hemisphere.Sphere 2))
      (e : C((Hemisphere.Sphere 2), (Hemisphere.Sphere 2))) hbij
  rcases hk with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul] at hu ⊢
    rw [← heq, SingularHomology.singularHomologyMap_comp, hu]
    change
      (SingularMayerVietoris.singularHomologyMap α 2).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.id (Hemisphere.Sphere 2)) 2) =
        _
    rw [SingularHomology.singularHomologyMap_id, LinearMap.comp_id]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_zsmul] at hu ⊢
    rw [← heq, SingularHomology.singularHomologyMap_comp, hu, LinearMap.comp_neg]
    change
      -((SingularMayerVietoris.singularHomologyMap α 2).comp
            (SingularMayerVietoris.singularHomologyMap
              (ContinuousMap.id (Hemisphere.Sphere 2)) 2)) =
        _
    rw [SingularHomology.singularHomologyMap_id, LinearMap.comp_id]

theorem MorseCancellation.same_image_section_classes_unit {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} {a : ℝ}
    (α β : C((Hemisphere.Sphere 2), { y : M // f y = a })) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ middleSectionClass β = k • middleSectionClass α := by
  obtain ⟨k, hk, hm⟩ := same_image_sphere_maps_unit α β hα hβ hrange
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap α 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap α 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap α 2)
  refine ⟨k, hk, ?_⟩
  simp only [middleSectionClass, SingularHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, hm, heval, map_zsmul]

theorem MorseCancellation.nativeMiddleBasinFamily_replace_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {n : ℕ}
    (q : ManifoldMorse.criticalPoints E f)
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (αq βq : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily : IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (hrange : Set.range βq = Set.range αq) :
    let _ := RegularLevel.chartedSpace hf ha
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ βq →
      Topology.IsClosedEmbedding βq →
        (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) βq x)) →
          IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases βq (fun j => α j)) := by
  let _ := RegularLevel.chartedSpace hf ha
  dsimp only
  intro hβs hβe hβi
  have hr (j : Fin (n + 1)) :
    Set.range (Fin.cases βq (fun j => α j) j) = Set.range (Fin.cases αq (fun j => α j) j) := by
    cases j using Fin.cases with
    | zero => exact hrange
    | succ j => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hβs
    | succ j => exact hfamily.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβe
    | succ j => exact hfamily.2.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβi
    | succ j => exact hfamily.2.2.1 j.succ
  · intro j k hjk
    rw [hr j, hr k]
    exact hfamily.2.2.2.1 hjk
  · intro j y
    rw [hr j]
    exact hfamily.2.2.2.2 j y

theorem MorseCancellation.attaching_contributions_opposite_of_relative_det_neg {N Y : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y]
    (a : C(Metric.sphere (0 : N) 1, Y)) (L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N)
    (hdet : (L₁.trans L₀.symm).toLinearEquiv.toLinearMap.det < 0) :
    SingularMayerVietoris.singularHomologyMap
        (a.comp (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)) 2 =
      -SingularMayerVietoris.singularHomologyMap
          (a.comp (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)) 2 :=
  by
  rw [SingularHomology.singularHomologyMap_comp,
    SingularHomology.singularHomologyMap_comp]
  apply LinearMap.ext
  intro u
  have h := LinearSphereAction.homology_relative_sign 1 L₁ L₀ 1 u
  rw [sign_eq_neg_one_iff.mpr hdet] at h
  simp only [SignType.coe_neg, SignType.coe_one, neg_one_zsmul] at h
  change
    SingularMayerVietoris.singularHomologyMap a 2
        (SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 u) =
      -SingularMayerVietoris.singularHomologyMap a 2
          (SingularMayerVietoris.singularHomologyMap
            (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 u)
  rw [h, map_neg]

theorem MorseCancellation.exists_centered_passage_normal_factors {E M Y Z N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y] [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y]
    [SecondCountableTopology Y] [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z]
    [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {f : (Hemisphere.Sphere 2) → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : Topology.IsEmbedding f) (hge : Topology.IsEmbedding g)
    (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (Set.range f) (Set.range g)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5)
    (x : (Hemisphere.Sphere 2)) (y : Y) (hbx : f x ∉ Set.range b) (hby : g y ∉ Set.range b)
    (γ : Path (f x) (g y)) (n : M → N) (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (g y))
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) g y) = 0)
    (hdimN : Module.finrank ℝ N = 3) :
    ∃ (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2)))) (B :
      (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N),
      ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
        ∃ (c : ℝ) (hc : 0 < c),
          ∃ A : CenteredSheetPassage E f g x y (Set.range b),
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  n
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        f (radialParameterChart (1 / 2) x z).2)))
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
              Function.Bijective
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) := by
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, _, hchoices⟩ :=
    exists_relative_sheet_passages_with_normal_change hf hg hfe hge hfi hgi hdisj hb hbc hdim x y
      hbx hby γ
  let Ψ := radialParameterChart (1 / 2) x
  have hΨ0 : (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Ψ.source :=
    radialParameterChart_zero_mem_source (1 / 2) x
  have hΨpoint : Ψ 0 = ((1 / 2 : ℝ), x) := radialParameterChart_zero (1 / 2) x
  let J : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))) :=
    mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Ψ 0
  let K : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] (EuclideanSpace ℝ (Fin 2)) :=
    mfderiv (𝓡 2) 𝓘(ℝ, (EuclideanSpace ℝ (Fin 2)))
      (fun q : (Hemisphere.Sphere 2) => (Φ₀.symm (f q)).2.1) x
  let P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))) :=
    ((ContinuousLinearMap.id ℝ ℝ).prodMap K).comp J
  let G : (ℝ × (EuclideanSpace ℝ (Fin 2))) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  let B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N := fderiv ℝ G 0
  have hnΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ₁ (1, 0)) := by rw [hΦy]; exact hn
  have hB : HasFDerivAt G B 0 := hasFDerivAt_terminal_normal_factor Φ₁ hΦ₁ hnΦ
  refine ⟨P, B, ?_⟩
  intro C
  obtain ⟨R, ε, hε, Φ, A, hprod, _, _, hleft, hright, _, _, havoid, _, hcross, htrans⟩ :=
    hchoices C
  have h0 : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source :=
    hprod ⟨⟨le_rfl, zero_le_one⟩, Metric.mem_closedBall_self hε.le⟩
  obtain ⟨D, hD0, _, hDpoint, _, hDinterval, _, hDder⟩ := exists_centered_passage_clock A.time_mem
  let T := A.centeredSheetPassage D hD0 hDpoint hDinterval havoid hcross
  let c : ℝ := deriv Real.smoothTransition A.time * A.destination
  have hc : 0 < c := A.time_rate
  let F : ℝ × (Hemisphere.Sphere 2) → M := fun p => A.family (p.1, f p.2)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ F :=
    A.smooth.comp (contMDiff_fst.prodMk (hf.comp contMDiff_snd))
  have hpoint : F (A.time, x) = g y :=
    (hcross A.time ⟨A.time_mem.1.le, A.time_mem.2.le⟩ x y).mpr ⟨rfl, rfl, rfl⟩
  have hnF : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (F (A.time, x)) := by rw [hpoint]; exact hn
  let NF : ℝ × (Hemisphere.Sphere 2) → N := n ∘ F
  have hNF : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :=
    (hnF.comp (A.time, x) hF.contMDiffAt).mdifferentiableAt (by simp)
  have hNFbij : Function.Bijective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x)) :=
    bijective_trace_normal_of_native_transverse (hF.mdifferentiable (by simp) (A.time, x))
      (hn.mdifferentiableAt (by simp)) hpoint.symm htrans hsurj hzero
      (by simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdimN])
  have hret :
    fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
            (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N).comp
        J :=
    fderiv_retimed_trace_parameter hNF hDder hDpoint Ψ hΨ0 hΨpoint
  have hfactor :
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
        (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).prodMap
          (C.toContinuousLinearMap.comp K)) :=
    A.normal_trace_mfderiv Φ₀ Φ₁ C R (hf.mdifferentiable (by simp) x) h0 hΦ₀ hΦx hrec₀ hleft
      hright n B hB
  have heq :
    fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P) := by
    rw [hret, hfactor]
    apply ContinuousLinearMap.ext
    intro z
    change B ((J z).1 * c, C (K (J z).2)) = B (c * (J z).1, C (K (J z).2))
    rw [mul_comm]
  let H : ℝ × (Hemisphere.Sphere 2) → N := fun p => NF (D p.1, p.2)
  have hNF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (D (1 / 2), x) := by
    rw [hDpoint]
    exact hNF
  have hH : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (1 / 2, x) :=
    MDifferentiableAt.comp (g := NF) (f := fun p : ℝ × (Hemisphere.Sphere 2) =>
      (D p.1, p.2)) (1 / 2, x) hNF'
      ((hDder.differentiableAt.mdifferentiableAt.comp (1 / 2, x) mdifferentiableAt_fst).prodMk
        mdifferentiableAt_snd)
  have hH' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (Ψ 0) := by
    rw [hΨpoint]
    exact hH
  have hdiff :
    DifferentiableAt ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2)))
      0 :=
    (hH'.comp 0 (Ψ.mdifferentiableAt (by simp) hΨ0)).differentiableAt
  have hder :
    HasFDerivAt (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2)))
      (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 := by
    rw [← heq]
    exact hdiff.hasFDerivAt
  have hbij :
    Function.Bijective
      (fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0) := by
    rw [hret]
    exact hNFbij.comp (PartialChart.bijective_mfderiv Ψ hΨ0)
  exact ⟨c, hc, T, hder, heq ▸ hbij⟩

theorem MorseCancellation.opposite_centered_passages_of_normal_factors {E M Y N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {f : (Hemisphere.Sphere 2) → M} {g : Y → M} {x : (Hemisphere.Sphere 2)} {y : Y}
    {O : Set M} (n : M → N) (hdim : Module.finrank ℝ N = 3)
    (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N)
    (hchoices :
      ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
        ∃ (c : ℝ) (hc : 0 < c),
          ∃ A : CenteredSheetPassage E f g x y O,
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  n
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        f (radialParameterChart (1 / 2) x z).2)))
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
              Function.Bijective
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P))) :
    ∃ A₀ A₁ : CenteredSheetPassage E f g x y O,
      ∃ L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N,
        HasFDerivAt
            (fun z : (EuclideanSpace ℝ (Fin 3)) =>
              n
                (A₀.family
                  ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
            L₀.toContinuousLinearMap 0 ∧
          HasFDerivAt
              (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                n
                  (A₁.family
                    ((radialParameterChart (1 / 2) x z).1,
                      f (radialParameterChart (1 / 2) x z).2)))
              L₁.toContinuousLinearMap 0 ∧
            (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  obtain ⟨C, hC⟩ :=
    SupportedGerms.exists_linearEquiv_with_det (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (0 : Fin 2) (show (-1 : ℝ) ≠ 0 by norm_num)
  have hCneg : C.toLinearMap.det < 0 := by rw [hC]; norm_num
  obtain ⟨c₀, hc₀, A₀, hA₀, hbij₀⟩ :=
    hchoices (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨c₁, hc₁, A₁, hA₁, _⟩ := hchoices C
  let Q₀ :=
    passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
  let Q₁ := passageNormalProduct c₁ hc₁.ne' C
  obtain ⟨P', B', hP, hB⟩ := exists_shared_passage_frames P B Q₀ hdim hbij₀
  let L₀ := (P'.trans Q₀).trans B'
  let L₁ := (P'.trans Q₁).trans B'
  have hL₀ : L₀.toContinuousLinearMap = B.comp (Q₀.toContinuousLinearMap.comp P) := by
    change
      B'.toContinuousLinearMap.comp (Q₀.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  have hL₁ : L₁.toContinuousLinearMap = B.comp (Q₁.toContinuousLinearMap.comp P) := by
    change
      B'.toContinuousLinearMap.comp (Q₁.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  refine ⟨A₀, A₁, L₀, L₁, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact hA₀
  · rw [hL₁]
    exact hA₁
  · exact passage_normal_relative_det_neg P' B' hc₀ hc₁ C hCneg

theorem MorseCancellation.exists_native_opposite_centered_passages {E M Z : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C((Hemisphere.Sphere 2), d.UpperLevel)) (hαe : Topology.IsEmbedding α)
    (hdisj : Disjoint (Set.range α) (Set.range d.surgery.beltSphere)) (b : Z → d.UpperLevel)
    (hbc : IsClosed (Set.range b)) (x : (Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (hx : α x ∉ Set.range b)
    (hv : d.surgery.beltSphere v ∉ Set.range b) (γ : Path (α x) (d.surgery.beltSphere v)) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) α z)) →
        ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ b →
          ∃ A₀ A₁ :
            CenteredSheetPassage (RegularLevel.Model E) α d.surgery.beltSphere x v
              (Set.range b),
            ∃ L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
              HasFDerivAt
                  (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                    d.beltNormal
                      (A₀.family
                        ((radialParameterChart (1 / 2) x z).1,
                          α (radialParameterChart (1 / 2) x z).2)))
                  L₀.toContinuousLinearMap 0 ∧
                HasFDerivAt
                    (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                      d.beltNormal
                        (A₁.family
                          ((radialParameterChart (1 / 2) x z).1,
                            α (radialParameterChart (1 / 2) x z).2)))
                    L₁.toContinuousLinearMap 0 ∧
                  (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  dsimp only
  intro hα hαi hb
  have hleveldim : Module.finrank ℝ (RegularLevel.Model E) = 5 := by
    simp [RegularLevel.Model, hdim]
  have hn :=
    d.contMDiffOn_beltNormal hf |>.contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  obtain ⟨P, B, hchoices⟩ :=
    exists_centered_passage_normal_factors hα (d.belt_smooth hf 2) hαe
      d.belt_isClosedEmbedding.isEmbedding hαi (d.belt_derivative_injective hf 2) hdisj hb hbc
      hleveldim x v hx hv γ d.beltNormal hn (d.surjective_beltNormal_derivative hf v)
      (d.beltNormal_derivative_comp_belt hf 2 v) (by exact Fact.out)
  exact opposite_centered_passages_of_normal_factors d.beltNormal (by exact Fact.out) P B hchoices

attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem MorseCancellation.nativeMiddleBasinFamily_reindex {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {n m : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (γ : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = a })
    (hγ : IsNativeMiddleBasinFamily S hf ha p γ) (e : Fin m → Fin n) (he : Function.Injective e) :
    IsNativeMiddleBasinFamily S hf ha (p ∘ e) (γ ∘ e) := by
  obtain ⟨hs, hi, hd, hpair, hfull⟩ := hγ
  exact
    ⟨fun j => hs (e j), fun j => hi (e j), fun j => hd (e j), fun i j hij =>
      hpair (fun h => hij (he h)), fun j => hfull (e j)⟩

theorem MorseCancellation.native_middle_block_complete_and_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    (∀ z : ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, nativeMiddleBlockPoint S r n hrc j = z) ∧
      (∀ z : ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < nativeMiddleBaseCut S r n hrc) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr] at htwo
  rw [hrr, hnn] at hthree hafter
  let W := S.toSurgeryWindows
  have hrcW : r + n < W.count := hrc
  have hpos := W.count_pos hf
  have hi0 (i : Fin W.count) (hi : i.val = 0) : nativeMorseIndex E f (W.point i) = 0 := by
    have he : i = ⟨0, hpos⟩ := Fin.ext hi
    rw [he]
    exact
      (nativeMorseIndex_eq_chart (S.data (W.first hpos)).chart).trans (W.first_index_zero hf hpos)
  have hi2 (i : Fin W.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
    nativeMorseIndex E f (W.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin W.count) (hri : r < i.val) (hin : i.val ≤ r + n) :
    nativeMorseIndex E f (W.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (hthree i hri hin)
  have hi4 (i : Fin W.count) (hin : r + n < i.val) : 4 ≤ nativeMorseIndex E f (W.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (W.point i)).chart]
    exact hafter i hin
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hiz : i.val ≠ 0 := by
      intro hi
      have hh := hi0 i hi
      omega
    have hri : r < i.val := by
      by_contra hnot
      have hh := hi2 i (by omega) (le_of_not_gt hnot)
      omega
    have hin : i.val ≤ r + n := by
      by_contra hnot
      have hh := hi4 i (lt_of_not_ge hnot)
      omega
    refine ⟨⟨i.val - (r + 1), by omega⟩, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (i.val - (r + 1)) + 1 = i.val
    omega
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hir : i.val ≤ r := by
      by_contra hnot
      by_cases hin : i.val ≤ r + n
      · have hh := hi3 i (lt_of_not_ge hnot) hin
        omega
      · have hh := hi4 i (lt_of_not_ge hin)
        omega
    exact
      (W.point_strictMono.monotone (show i ≤ ⟨r, by omega⟩ from hir)).trans_lt
        (W.value_lt_upper _)

def LocalDegree.SeparatedNeighborhoods.pointComplementInclusion {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), ↥({(x : M)}ᶜ ∩ D.neighborhood x)) :=
  (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

theorem LocalDegree.SeparatedNeighborhoods.componentConnecting_singlePoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    SingularMayerVietoris.singularHomologyMap (D.pointComplementInclusion x) k
        (CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a := by
  have hsub : Pᶜ ⊆ {(x : M)}ᶜ := by
    intro y hy hxy
    exact hy (hxy ▸ x.property)
  exact
    CoverLocalContributions.componentConnecting_enlarge Pᶜ {(x : M)}ᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl isClosed_singleton.isOpen_compl D.isOpen_neighborhood
      D.pairwise_disjoint D.open_cover hsub x
      (LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a

attribute [local instance] ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) [Fintype (d.beltIntersectionPoints m g)]
    (hfin : (d.beltIntersectionPoints m g).Finite) {A : Type*} [AddCommGroup A] (a : A) :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ) • a) =
      d.beltIntersectionCount m j g hfin • a := by
  have hcount :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ)) =
      d.beltIntersectionCount m j g hfin :=
    (Finset.sum_subtype hfin.toFinset (fun _ => hfin.mem_toFinset)
        (fun x => (d.beltIntersectionSign m j g x : ℤ))).symm
  exact Finset.sum_smul.symm.trans (congrArg (fun z : ℤ => z • a) hcount)

theorem ManifoldMorse.MorseSurgeryData.exists_transverse_representative {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (g₀ : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg₀ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g₀)
      (_hinj : Function.Injective g₀)
      (_himm : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g₀ x)),
      ∃ e :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) d.UpperLevel
          d.UpperLevel ∞,
        ∃ g : C(Hemisphere.Sphere 2, d.UpperLevel),
          SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g x = e (g₀ x)) ∧ d.IsTransverseBeltSphere hf hdim hindex g ∧ g₀.Homotopic g := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  intro hg₀ hinj himm
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (RegularLevel.Model E) := by simp [RegularLevel.Model, hdim]
  obtain ⟨e, hiso, ht⟩ :=
    NativeTransversality.exists_ambient_transverse_diffeomorph hg₀ (d.belt_smooth hf 3)
      hdim'
  let g := e.toHomeomorph.toHomotopyEquiv.toFun.comp g₀
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g := e.contMDiff.comp hg₀
  have hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ g₀) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg₀.mdifferentiable (by simp) x)]
    exact
      ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by trivial)).comp
        (himm x)
  exact ⟨e, g, hiso, fun _ => rfl, ⟨hg, e.injective.comp hinj, hi, ht⟩, hiso.comp_homotopic g₀⟩

theorem AdaptedWindows.cancel_single_basin_section_isotopy {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hp : MorseCancellation.nativeMorseIndex E f p = 2) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {c : ℝ} (hpc : f p < c) (hcq : c < f q)
    (hc : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hc
    ∀ (α : Hemisphere.Sphere 2 → { z : M // f z = c }) (β : Y → { z : M // f z = c }),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
        ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β →
          (∀ z,
              z ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t z.val) Filter.atBot (𝓝 q.val)) →
            (∀ z,
                z ∈ Set.range β ↔
                  Filter.Tendsto (fun t => S.flow t z.val) Filter.atTop (𝓝 p.val)) →
              ∀ D :
                Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                  { z : M // f z = c } { z : M // f z = c } ∞,
                SupportedDiffeomorph.IsotopicToIdentity D →
                  (∀ x y,
                      NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
                        (D ∘ α) β x y) →
                    (Set.range (D ∘ α) ∩ Set.range β).ncard = 1 →
                      ∃ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                          ManifoldMorse.IsMorse E g ∧
                            (ManifoldMorse.criticalPoints E g).ncard + 2 =
                                (ManifoldMorse.criticalPoints E f).ncard ∧
                              (∀ z,
                                  z ∈ ManifoldMorse.criticalPoints E g ↔
                                    z ∈ ManifoldMorse.criticalPoints E f ∧
                                      z ≠ p.val ∧ z ≠ q.val) ∧
                                ∀ z,
                                  f z ∉
                                      Set.Ioo (S.toSurgeryWindows.lower p)
                                        (S.toSurgeryWindows.upper q) →
                                    g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf hc
  intro α β hα hβ hback hforward D hD htrans hsingle
  let δ := D.symm ∘ β
  have hδ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ δ := D.symm.contMDiff.comp hβ
  have hDα : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ α) := D.contMDiff.comp hα
  have hαeq : D.symm ∘ (D ∘ α) = α := by
    funext x
    exact D.symm_apply_apply (α x)
  have hrange (z : { w : M // f w = c }) : z ∈ Set.range α ↔ D z ∈ Set.range (D ∘ α) := by
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_range_self x
    · rintro ⟨x, hx⟩
      exact ⟨x, D.injective hx⟩
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hsingle
  have hzmem : z ∈ Set.range (D ∘ α) ∩ Set.range β := by
    rw [hz]
    exact Set.mem_singleton z
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hzmem
  have hcross : β y = (D ∘ α) x := hy.trans hx.symm
  have hcross' : δ y = α x := by exact (congrArg D.symm hcross).trans (D.symm_apply_apply (α x))
  have ht : NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) α δ x y := by
    have hh :=
      (TransverseGerms.native_transversality_partial_diffeomorph_iff
            D.symm.toPartialDiffeomorph (hDα.mdifferentiableAt (by simp))
            (hβ.mdifferentiableAt (by simp)) hcross (Set.mem_univ _)).mp
        (htrans x y)
    change
      NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
        (D.symm ∘ (D ∘ α)) δ x y at hh
    rwa [hαeq] at hh
  have hcount :
    {w : { z : M // f z = c } |
          Filter.Tendsto (fun t => S.flow t w.val) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => S.flow t (D w).val) Filter.atTop (𝓝 p.val)}.ncard =
      1 := by
    have heq :
      {w : { z : M // f z = c } |
          Filter.Tendsto (fun t => S.flow t w.val) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => S.flow t (D w).val) Filter.atTop (𝓝 p.val)} =
        {D.symm z} := by
      ext w
      change (_ ∧ _) ↔ w = D.symm z
      rw [← hback w, ← hforward (D w), hrange w]
      change D w ∈ Set.range (D ∘ α) ∩ Set.range β ↔ w = D.symm z
      rw [hz, Set.mem_singleton_iff]
      exact
        ⟨fun h => (D.symm_apply_apply w).symm.trans (congrArg D.symm h), fun h =>
          (congrArg D h).trans (D.apply_symm_apply z)⟩
    rw [heq, Set.ncard_singleton]
  have hαbasin :
    ∀ᶠ w in 𝓝 x, Filter.Tendsto (fun t => S.flow t (α w).val) Filter.atBot (𝓝 q.val) :=
    Filter.Eventually.of_forall (fun w => (hback (α w)).mp (Set.mem_range_self w))
  have hδbasin :
    ∀ᶠ w in 𝓝 y, Filter.Tendsto (fun t => S.flow t (D (δ w)).val) Filter.atTop (𝓝 p.val) := by
    apply Filter.Eventually.of_forall
    intro w
    change Filter.Tendsto (fun t => S.flow t (D (D.symm (β w))).val) Filter.atTop (𝓝 p.val)
    rw [D.apply_symm_apply]
    exact (hforward (β w)).mp (Set.mem_range_self w)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b, hcb, hbq⟩ := exists_between hcq
  have hweightp : Fintype.card { i // (S.data p).chart.weights i = -1 } = 2 := by
    have hh := (MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
    simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      MorseHandle.NegativeSpace, finrank_euclideanSpace] using hh
  have hweightq : Fintype.card { i // (S.data q).chart.weights i = -1 } = 3 := by
    have hh := (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
    simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      MorseHandle.NegativeSpace, finrank_euclideanSpace] using hh
  exact
    MorseCancellation.cancel_of_transverse_level_isotopy (m := 5) (S.data p).chart (S.data q).chart hf
      hm hdim (by omega) S.field S.smooth S.zero S.descent S.flow S.integral S.distinct p.property
      q.property (S.toSurgeryWindows.lower_lt_value p) (S.toSurgeryWindows.value_lt_upper q)
      (MorseCancellation.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hac hcb hpc
      hcq (MorseCancellation.surgery_pair_inner_band_regular p q hconsecutive hpa hbq) hc
      (S.critical_model_germ p) (S.critical_model_germ q) D hD hcount α δ x y
      (hα.mdifferentiableAt (by simp)) (hδ.mdifferentiableAt (by simp)) hcross' ht hαbasin hδbasin

theorem MorseCancellation.middle_blocks_complete_of_no_four_five {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (htwo : S.HasIndexTwoPrefix r)
    (hrc : r + n < S.count) (hthree : S.HasIndexThreeBlock r n)
    (hafter :
      ∀ i : Fin S.count,
        r + n < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates)
    (hsix : nativeMorseCount E f 6 = 1) (hfour : nativeMorseCount E f 4 = 0)
    (hfive : nativeMorseCount E f 5 = 0) : r + n + 2 = S.count := by
  have hpos := S.count_pos hf
  have hidx (i : Fin S.count) :
    nativeMorseIndex E f (S.point i) = 6 ↔ r + n + 1 ≤ i.val ∧ i.val < S.count := by
    have hle : nativeMorseIndex E f (S.point i) ≤ 6 := by
      simpa only [hdim] using (nativeMorseIndex_le (E := E) (f := f) (p := (S.point i).val))
    have hne4 := native_index_excluded_of_count_zero S hfour _ (S.point i).property
    have hne5 := native_index_excluded_of_count_zero S hfive _ (S.point i).property
    by_cases ha : r + n < i.val
    · have hh := hafter i ha
      rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart] at hh
      have hi := i.isLt
      omega
    · have hh : nativeMorseIndex E f (S.point i) ≤ 3 := by
        by_cases hz : i.val = 0
        · have he : i = ⟨0, hpos⟩ := Fin.ext hz
          have hzidx : nativeMorseIndex E f (S.point i) = 0 := by
            rw [he]
            exact
              (nativeMorseIndex_eq_chart (S.data (S.first hpos)).chart).trans
                (S.first_index_zero hf hpos)
          omega
        · by_cases hr : i.val ≤ r
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart, htwo i (by omega) hr]
            omega
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart,
              hthree i (by omega) (by omega)]
      omega
  have hcount :=
    nativeMorseCount_eq_interval_length S 6 (r + n + 1) S.count (by omega) le_rfl hidx
  omega

theorem MorseCancellation.critical_pair_of_surgery_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hcount : S.count = 2) :
    ∃ p q : M, f p < f q ∧ ManifoldMorse.criticalPoints E f = { p, q } := by
  let p := S.point ⟨0, by omega⟩
  let q := S.point ⟨1, by omega⟩
  refine ⟨p.val, q.val, S.point_strictMono (by change (0 : ℕ) < 1; omega), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := S.point.surjective ⟨z, hz⟩
    have hib := i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 := by omega
    rcases hcases with hzero | hone
    · have he : i = ⟨0, by omega⟩ := Fin.ext hzero
      have hv := congrArg (fun x : ManifoldMorse.criticalPoints E f => x.val) hi
      rw [he] at hv
      exact Set.mem_insert_iff.mpr (Or.inl hv.symm)
    · have he : i = ⟨1, by omega⟩ := Fin.ext hone
      have hv := congrArg (fun x : ManifoldMorse.criticalPoints E f => x.val) hi
      rw [he] at hv
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hv.symm))
  · intro hz
    rcases Set.mem_insert_iff.mp hz with hp | hq
    · exact hp ▸ p.property
    · exact (Set.mem_singleton_iff.mp hq) ▸ q.property


end
