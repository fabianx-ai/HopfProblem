/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField.BoundaryArcs

/-!
# Recognising a sheet in a chart

`SheetRecognition.eventually_mem_sheet_iff`: if a chart `Φ` agrees with a sheet chart `ψ` (in
which the sheet `S` is the zero section) along a parametrisation `ι` up to a homeomorphism of the
parameters, then near each point of `ι`, `Φ` meets `S` exactly in the range of `ι`.
`SheetRecognition.exists_open_recognition_domain`: for a closed set `S`, such local recognition
along a subset `A` together with recognition on a compact set `K` gives an open neighbourhood of
`K` on which `Φ` meets `S` exactly in `A`. For a tubular bigon, the bigon meets the first sheet
exactly along its lower boundary arc and the second sheet exactly along its parabolic upper
boundary arc (`TubularBigon.map_mem_first_iff`, `TubularBigon.map_mem_second_iff`).

These are point-set statements about charts, used to show that a chart adapted to two sheets along
a compact disc meets them only in the model sheets; cf. Milnor, *Lectures on the h-cobordism
theorem*, §6.

## Tags

chart, submanifold, compactness
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- Sheet recognition: if a chart is parametrised by a sheet through a bijective reparametrisation,
then near a sheet point the chart meets the sheet exactly in the image of the parametrisation. -/
theorem SheetRecognition.eventually_mem_sheet_iff {W D B E M : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    (ψ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {S : Set M}
    (hsheet : ∀ q ∈ ψ.source, ψ q ∈ S ↔ q.2 = 0) {ι : D → W} (hι : Continuous ι) {σ τ : D → D}
    (hτ : Continuous τ) (hτσ : Function.LeftInverse τ σ) (hστ : Function.RightInverse τ σ)
    (hparam : ∀ q : D, ι q ∈ Φ.source → (σ q, (0 : B)) ∈ ψ.source ∧ Φ (ι q) = ψ (σ q, 0)) {q₀ : D}
    (hq₀ : ι q₀ ∈ Φ.source) : ∀ᶠ z in 𝓝 (ι q₀), z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ Set.range ι) := by
  let recover : W → W := fun z => ι (τ ((ψ.symm (Φ z)).1))
  have htarget : Φ (ι q₀) ∈ ψ.target := by
    rw [(hparam q₀ hq₀).2]
    exact ψ.map_source' (hparam q₀ hq₀).1
  have hΦ : ContinuousAt Φ (ι q₀) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hq₀)).continuousAt
  have hψ : ContinuousAt ψ.symm (Φ (ι q₀)) :=
    (ψ.contMDiffOn_invFun.contMDiffAt (ψ.open_target.mem_nhds htarget)).continuousAt
  have hrec : ContinuousAt recover (ι q₀) :=
    hι.continuousAt.comp (hτ.continuousAt.comp (continuousAt_fst.comp (hψ.comp hΦ)))
  have hreczero : recover (ι q₀) = ι q₀ := by
    have hcoord : ψ.symm (Φ (ι q₀)) = (σ q₀, (0 : B)) := by
      rw [(hparam q₀ hq₀).2]
      exact ψ.left_inv' (hparam q₀ hq₀).1
    change ι (τ ((ψ.symm (Φ (ι q₀))).1)) = ι q₀
    rw [hcoord]
    exact congrArg ι (hτσ q₀)
  have hrecSource : ∀ᶠ z in 𝓝 (ι q₀), recover z ∈ Φ.source :=
    hrec.preimage_mem_nhds (by rw [hreczero]; exact Φ.open_source.mem_nhds hq₀)
  have htargetNear : ∀ᶠ z in 𝓝 (ι q₀), Φ z ∈ ψ.target :=
    hΦ.preimage_mem_nhds (ψ.open_target.mem_nhds htarget)
  filter_upwards [Φ.open_source.mem_nhds hq₀, htargetNear, hrecSource] with z hz hzψ hzrec
  refine ⟨hz, ?_⟩
  constructor
  · intro hzS
    let q := ψ.symm (Φ z)
    have hq : q ∈ ψ.source := ψ.map_target' hzψ
    have hqzero : q.2 = 0 :=
      (hsheet q hq).mp
        (by
          change ψ (ψ.symm (Φ z)) ∈ S
          have he : ψ (ψ.symm (Φ z)) = Φ z := ψ.right_inv' hzψ
          rw [he]
          exact hzS)
    have heq : Φ (recover z) = Φ z := by
      change Φ (ι (τ q.1)) = Φ z
      rw [(hparam (τ q.1) hzrec).2, hστ q.1]
      have hqeq : (q.1, (0 : B)) = q := by
        apply Prod.ext
        · rfl
        · exact hqzero.symm
      rw [hqeq]
      exact ψ.right_inv' hzψ
    exact ⟨τ q.1, Φ.toPartialEquiv.injOn hzrec hz heq⟩
  · rintro ⟨q, hqz⟩
    have hq : ι q ∈ Φ.source := hqz.symm ▸ hz
    rw [← hqz, (hparam q hq).2]
    exact (hsheet _ (hparam q hq).1).mpr rfl


/-- The centre line of the bigon lies in the first sheet. -/
theorem TubularBigon.lower_center_mem_sheet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tube.map (2 * t - 1, 0) ∈ S := by
  rw [tube.lower t ht, ← k.center t ht]
  exact
    (k.first_sheet (t, 0)
          (k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩)).mpr
      rfl

/-- The upper boundary arc of the bigon lies in the second sheet. -/
theorem TubularBigon.upper_center_mem_sheet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tube.map (WhitneyPairModel.upperBoundaryArc h t) ∈ T := by
  change tube.map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ T
  rw [tube.upper t ht, ← l.center t ht]
  exact
    (l.first_sheet (t, 0)
          (l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩)).mpr
      rfl

/-- In the bigon, the tubular map meets the first sheet exactly along the lower boundary arc `{y =
0}`. -/
theorem TubularBigon.map_mem_first_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) : tube.map p ∈ S ↔ p.2 = 0 := by
  constructor
  · intro hpS
    have hfront : p ∈ frontier (WhitneyPairModel.bigon h) := by
      rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inl hpS)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · rfl
    · have hlt : (t, (0 : ℝ)) ∈ l.domain :=
        l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
      rw [tube.upper t ht, ← l.center t ht] at hpS
      rcases (l.second_sheet (t, 0) hlt).mp hpS with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
  · intro hpzero
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * WhitneyPairModel.arcTime p - 1 := by
      dsimp [WhitneyPairModel.arcTime]; ring
    have heq : p = (2 * WhitneyPairModel.arcTime p - 1, 0) := Prod.ext hbase hpzero
    rw [heq]
    exact tube.lower_center_mem_sheet ht

/-- In the bigon, the tubular map meets the second sheet exactly along the parabolic upper boundary
arc. -/
theorem TubularBigon.map_mem_second_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) : tube.map p ∈ T ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · intro hpT
    have hfront : p ∈ frontier (WhitneyPairModel.bigon h) := by
      rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inr hpT)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · have hkt : (t, (0 : ℝ)) ∈ k.domain :=
        k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
      rw [tube.lower t ht, ← k.center t ht] at hpT
      rcases (k.second_sheet (t, 0) hkt).mp hpT with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
    · rfl
  · intro hpupper
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * WhitneyPairModel.arcTime p - 1 := by
      dsimp [WhitneyPairModel.arcTime]; ring
    have heq : p = WhitneyPairModel.upperBoundaryArc h (WhitneyPairModel.arcTime p) :=
      by
      apply Prod.ext hbase
      change p.2 = h * (1 - (2 * WhitneyPairModel.arcTime p - 1) ^ 2)
      rw [← hbase]
      exact hpupper
    rw [heq]
    exact tube.upper_center_mem_sheet ht

/-- If a chart meets a closed set exactly in a prescribed subset locally near that subset, and does
so on a compact set, then it does so on an open neighbourhood of that compact set. -/
theorem SheetRecognition.exists_open_recognition_domain {W E M : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    {S : Set M} {A K : Set W} (hS : IsClosed S) (hK : K ⊆ Φ.source)
    (hforward : ∀ z ∈ Φ.source, z ∈ A → Φ z ∈ S)
    (hlocal : ∀ z ∈ Φ.source, z ∈ A → ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A))
    (hcontact : ∀ z ∈ K, Φ z ∈ S ↔ z ∈ A) :
    ∃ U : Set W, IsOpen U ∧ K ⊆ U ∧ U ⊆ Φ.source ∧ ∀ z ∈ U, Φ z ∈ S ↔ z ∈ A := by
  have hnear : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A) := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hlocal z (hK hz) hzA
    have hzS : Φ z ∉ S := fun hs => hzA ((hcontact z hz).mp hs)
    have hΦ : ContinuousAt Φ z :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hK hz))).continuousAt
    have havoid : ∀ᶠ w in 𝓝 z, Φ w ∉ S := hΦ.preimage_mem_nhds (hS.isOpen_compl.mem_nhds hzS)
    filter_upwards [Φ.open_source.mem_nhds (hK hz), havoid] with w hw hwS
    exact ⟨hw, ⟨fun hs => (hwS hs).elim, fun ha => (hwS (hforward w hw ha)).elim⟩⟩
  let U := interior {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)}
  have hsub : U ⊆ {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)} := interior_subset
  exact
    ⟨U, isOpen_interior, fun z hz => mem_interior_iff_mem_nhds.mpr (hnear z hz), fun _ hz =>
      (hsub hz).1, fun _ hz => (hsub hz).2⟩


end
