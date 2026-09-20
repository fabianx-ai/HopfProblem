/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs

/-!
# The rank-three Whitney model

The last step of the Whitney trick in the rank-three model: the graph motion pushing one sheet
across the Whitney disc, charts of a tubular bigon adapted first to the tangent planes of the two
sheets, then to their parametrisations, and finally compatible with the two sheets themselves, the
sheet corrections and the sheet recognition that produce them, and the supported diffeomorphisms
that turn the model motion into an ambient isotopy.

The conclusion (`TubularBigon.exists_rankThree_relative_cancellation`) is Whitney's lemma in this
model: a bigon whose two corner intersection signs are opposite yields an ambient isotopy,
supported away from the other intersection points, removing exactly those two points from the
intersection of the two sheets.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6 (Whitney's lemma and the
  cancellation of a pair of intersection points of opposite sign).

## Twin

No Mathlib counterpart exists.

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The bigon embedding rescaled by `r`: the reparametrisation `p ↦ (r p₁, r² p₂)` of the planar
bigon, which keeps the family of parabolas `y = h(1 - x²)` invariant up to the height. -/
def WhitneyPairModel.scaledBigonEmbedding (r : ℝ) (p : ℝ × ℝ) : Space :=
  bigonEmbedding (r * p.1, r ^ 2 * p.2)

/-- Rescaling by one is the bigon embedding itself. -/
theorem WhitneyPairModel.scaledBigonEmbedding_one (p : ℝ × ℝ) :
    scaledBigonEmbedding 1 p = bigonEmbedding p := by
  simp only [scaledBigonEmbedding, one_mul, one_pow, Prod.eta]

/-- The rescaled bigon embedding is jointly continuous in the scale and the point. -/
theorem WhitneyPairModel.continuous_scaledBigonEmbedding :
    Continuous (fun z : ℝ × (ℝ × ℝ) => scaledBigonEmbedding z.1 z.2) := by
  unfold scaledBigonEmbedding bigonEmbedding
  fun_prop

/-- If an open set contains the image of the bigon, it contains the image of a slightly enlarged
bigon. -/
theorem WhitneyPairModel.exists_scaled_bigon_in_open {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    ∃ r : ℝ, 1 < r ∧ Set.MapsTo (scaledBigonEmbedding r) (bigon h) U := by
  have hnear : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bigon h, scaledBigonEmbedding r p ∈ U := by
    apply (isCompact_bigon hh).eventually_forall_of_forall_eventually
    intro p hp
    apply (continuous_scaledBigonEmbedding.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [scaledBigonEmbedding_one] using hKU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hrball : (1 + ε / 2 : ℝ) ∈ Metric.ball 1 ε := by
    change Dist.dist (1 + ε / 2) 1 < ε
    rw [Real.dist_eq]
    have heq : 1 + ε / 2 - 1 = ε / 2 := by ring
    rw [heq, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨1 + ε / 2, by linarith, fun p hp => hball hrball p hp⟩

/-- A point of the bigon enlarged to height `h r²` is the image of a point of the bigon under the
rescaled embedding. -/
theorem WhitneyPairModel.enlarged_cap_parametrization {h r : ℝ} (hr : 0 < r) {p : ℝ × ℝ}
    (hp : 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h * r ^ 2) :
    ∃ q ∈ bigon h, scaledBigonEmbedding r q = bigonEmbedding p := by
  let q : ℝ × ℝ := (p.1 / r, p.2 / r ^ 2)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hcalc : h * (p.1 / r) ^ 2 + p.2 / r ^ 2 = (h * p.1 ^ 2 + p.2) / r ^ 2 := by field_simp
  have hq : q ∈ bigon h := by
    refine ⟨div_nonneg hp.1 hr2.le, ?_⟩
    change h * (p.1 / r) ^ 2 + p.2 / r ^ 2 ≤ h
    rw [hcalc]
    exact (div_le_iff₀ hr2).mpr hp.2
  refine ⟨q, hq, ?_⟩
  apply congrArg bigonEmbedding
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · change r ^ 2 * (p.2 / r ^ 2) = p.2
    field_simp

/-- The vertical graph of the height function `B` at time `t`: the point `((s, t B s), 0)`, i.e. the
graph pushed up by the fraction `t` of its height. -/
def WhitneyPairModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

/-- There is a smooth compactly supported height function lying above the upper boundary arc of the
bigon whose whole vertical trace stays in a prescribed open neighbourhood of the bigon. -/
theorem WhitneyPairModel.exists_supported_graph_height {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    ∃ B : ℝ → ℝ,
      ContDiff ℝ ∞ B ∧
        HasCompactSupport B ∧
          (∀ s, 0 ≤ B s) ∧
            (∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < B s) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U := by
  obtain ⟨r, hr, hscaled⟩ := exists_scaled_bigon_in_open hh hU hKU
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  let α : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := r
      rIn_pos := zero_lt_one
      rIn_lt_rOut := hr }
  let B : ℝ → ℝ := fun s => α s * (h * (r ^ 2 - s ^ 2))
  have hB : ContDiff ℝ ∞ B := α.contDiff.mul (by fun_prop)
  have hcompact : HasCompactSupport B := α.hasCompactSupport.mul_right
  have hsupp : tsupport B ⊆ tsupport (α : ℝ → ℝ) := by
    apply closure_mono
    intro s hs hα
    apply hs
    change α s * (h * (r ^ 2 - s ^ 2)) = 0
    rw [hα, MulZeroClass.zero_mul]
  have hbound : ∀ s ∈ tsupport B, |s| ≤ r := by
    intro s hs
    have hx := hsupp hs
    rw [α.tsupport_eq] at hx
    change Dist.dist s 0 ≤ r at hx
    simpa only [Real.dist_eq, sub_zero] using hx
  have hheight {s : ℝ} (hs : |s| ≤ r) : 0 ≤ h * (r ^ 2 - s ^ 2) := by
    have hsq : s ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrpos.le).mpr hs
    exact mul_nonneg hh.le (sub_nonneg.mpr hsq)
  have hnonneg : ∀ s, 0 ≤ B s := by
    intro s
    by_cases hs : α s = 0
    · simp only [B, hs, MulZeroClass.zero_mul, le_refl]
    have hmem : s ∈ Function.support α := hs
    rw [α.support_eq] at hmem
    have hsr : |s| ≤ r := by
      have hl : |s| < r := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hmem
      exact hl.le
    exact mul_nonneg α.nonneg (hheight hsr)
  refine ⟨B, hB, hcompact, hnonneg, ?_, ?_⟩
  · intro s hs
    have hα : α s = 1 :=
      α.one_of_mem_closedBall
        (by
          change Dist.dist s 0 ≤ 1
          simpa only [Real.dist_eq, sub_zero] using hs)
    change h * (1 - s ^ 2) < α s * (h * (r ^ 2 - s ^ 2))
    rw [hα, one_mul]
    have hgap : 0 < h * (r ^ 2 - 1) := mul_pos hh (by nlinarith [sq_nonneg (r - 1)])
    nlinarith
  · intro t ht s hs
    have hts : t * α s ≤ 1 := by
      calc
        t * α s ≤ 1 * α s := mul_le_mul_of_nonneg_right ht.2 α.nonneg
        _ ≤ 1 := by simpa only [one_mul] using (α.le_one (x := s))
    have hy : t * B s ≤ h * (r ^ 2 - s ^ 2) := by
      calc
        t * B s = (t * α s) * (h * (r ^ 2 - s ^ 2)) := by dsimp [B]; ring
        _ ≤ h * (r ^ 2 - s ^ 2) := mul_le_of_le_one_left (hheight (hbound s hs)) hts
    have hcap : 0 ≤ t * B s ∧ h * s ^ 2 + t * B s ≤ h * r ^ 2 :=
      ⟨mul_nonneg ht.1 (hnonneg s), by nlinarith⟩
    obtain ⟨q, hq, heq⟩ := enlarged_cap_parametrization (h := h) (p := (s, t * B s)) hrpos hcap
    have hmem := hscaled hq
    rw [heq] at hmem
    exact hmem

/-- The trace of the vertical graph motion: the set of pairs (time, point) swept out over the
support of the height function. -/
def WhitneyPairModel.graphTrace (B : ℝ → ℝ) : Set (ℝ × Space) :=
  (fun p : ℝ × ℝ => (p.1, verticalGraph B p.1 p.2)) '' (Set.Icc (0 : ℝ) 1 ×ˢ tsupport B)

/-- The trace of a compactly supported continuous height function is compact. -/
theorem WhitneyPairModel.isCompact_graphTrace {B : ℝ → ℝ} (hB : Continuous B)
    (hcompact : HasCompactSupport B) : IsCompact (graphTrace B) := by
  apply (CompactIccSpace.isCompact_Icc.prod hcompact.isCompact).image
  unfold verticalGraph
  fun_prop

/-- A smooth compactly supported cut-off supported in a prescribed open set whose value at a point
of the vertical graph at time `t` is the height at that point; it is the weight driving the
graph motion. -/
theorem WhitneyPairModel.exists_graph_motion_cutoff {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B)
    (hcompact : HasCompactSupport B) (hnonneg : ∀ s, 0 ≤ B s) {U : Set Space} (hU : IsOpen U)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U) :
    ∃ β : ℝ × Space → ℝ,
      ContDiff ℝ ∞ β ∧
        HasCompactSupport β ∧
          tsupport β ⊆ Prod.snd ⁻¹' U ∧
            (∀ p, 0 ≤ β p) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℝ, β (t, verticalGraph B t s) = B s :=
  by
  have hCU : graphTrace B ⊆ Prod.snd ⁻¹' U := by
    rintro _ ⟨p, hp, rfl⟩
    exact htrace p.1 hp.1 p.2 hp.2
  obtain ⟨η, hη, hηcompact, hηsupport, hηone, hηrange⟩ :=
    exists_compact_smooth_cutoff (isCompact_graphTrace hB.continuous hcompact)
      (hU.preimage continuous_snd) hCU
  let β : ℝ × Space → ℝ := fun p => η p * B p.2.1.1
  have hβ : ContDiff ℝ ∞ β := hη.mul (hB.comp (by fun_prop))
  have hβcompact : HasCompactSupport β := hηcompact.mul_right
  have hsupp : tsupport β ⊆ tsupport η := by
    apply closure_mono
    intro p hp hηp
    apply hp
    change η p * B p.2.1.1 = 0
    rw [hηp, MulZeroClass.zero_mul]
  refine
    ⟨β, hβ, hβcompact, hsupp.trans hηsupport, fun p => mul_nonneg (hηrange p).1 (hnonneg _), ?_⟩
  intro t ht s
  by_cases hs : B s = 0
  · change η (t, verticalGraph B t s) * B s = B s
    rw [hs, MulZeroClass.mul_zero]
  have hpoint : (t, verticalGraph B t s) ∈ graphTrace B :=
    ⟨(t, s), ⟨ht, subset_tsupport B hs⟩, rfl⟩
  have hηpoint : η (t, verticalGraph B t s) = 1 := hηone.self_of_nhdsSet _ hpoint
  change η (t, verticalGraph B t s) * B s = B s
  rw [hηpoint, one_mul]

/-- The data of a graph motion of the planar model: a height function above the bigon and a cut-off
tracking it, both compactly supported in a prescribed open set. -/
structure WhitneyPairModel.GraphMotionData (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  smooth_height : ContDiff ℝ ∞ height
  compact_height : HasCompactSupport height
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  trace_source : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport height, verticalGraph height t s ∈ U
  cutoff : ℝ × Space → ℝ
  smooth_cutoff : ContDiff ℝ ∞ cutoff
  compact_cutoff : HasCompactSupport cutoff
  support_cutoff : tsupport cutoff ⊆ Prod.snd ⁻¹' U
  nonneg_cutoff : ∀ p, 0 ≤ cutoff p
  tracking : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, cutoff (t, verticalGraph height t s) = height s

/-- Graph-motion data exist over any open neighbourhood of the image of the bigon. -/
theorem WhitneyPairModel.nonempty_graphMotionData {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    Nonempty (GraphMotionData h U) := by
  obtain ⟨B, hB, hcompact, hnonneg, habove, htrace⟩ := exists_supported_graph_height hh hU hKU
  obtain ⟨β, hβ, hβcompact, hβsupport, hβnonneg, hβtrack⟩ :=
    exists_graph_motion_cutoff hB hcompact hnonneg hU htrace
  exact
    ⟨{  height := B
        smooth_height := hB
        compact_height := hcompact
        nonneg_height := hnonneg
        above := habove
        trace_source := htrace
        cutoff := β
        smooth_cutoff := hβ
        compact_cutoff := hβcompact
        support_cutoff := hβsupport
        nonneg_cutoff := hβnonneg
        tracking := hβtrack }⟩

/-- The vertical vector `((0, δ), 0)` of the model, of norm `δ`. -/
def WhitneyPairModel.verticalVector (δ : ℝ) : Space :=
  ((0, δ), 0)

/-- The vertical vector of a nonnegative parameter has that parameter as its norm. -/
theorem WhitneyPairModel.norm_verticalVector {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖verticalVector δ‖ = δ := by
  simp [verticalVector, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ, hδ]

/-- One step of the graph motion: the translation by the cut-off weight at time `i δ` times the
vertical vector `δ`, smoothed in the time parameter. -/
def WhitneyPairModel.graphStep (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (p : ℝ × Space) :
    Space :=
  p.2 + β ((i : ℝ) * δ, p.2) • (Real.smoothTransition p.1 • verticalVector δ)

/-- Each step of the graph motion is smooth. -/
theorem WhitneyPairModel.contDiff_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (δ : ℝ) (i : ℕ) : ContDiff ℝ ∞ (graphStep β δ i) := by
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact
    contDiff_snd.add
      ((hβ.comp (contDiff_const.prodMk contDiff_snd)).smul
        ((hθ.comp contDiff_fst).smul contDiff_const))

/-- Each step is the identity at time zero. -/
theorem WhitneyPairModel.graphStep_zero (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (z : Space) :
    graphStep β δ i (0, z) = z := by
  simp only [graphStep, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero]

/-- Each step leaves the first horizontal coordinate unchanged. -/
theorem WhitneyPairModel.graphStep_horizontal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    (z : Space) : (graphStep β δ i (t, z)).1.1 = z.1.1 := by simp [graphStep, verticalVector]

/-- Each step leaves the normal coordinates unchanged. -/
theorem WhitneyPairModel.graphStep_normal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    (z : Space) : (graphStep β δ i (t, z)).2 = z.2 := by simp [graphStep, verticalVector]

/-- Each step is the identity outside the support of the cut-off. -/
theorem WhitneyPairModel.graphStep_fixed (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    {z : Space} (hz : z ∉ Prod.snd '' tsupport β) : graphStep β δ i (t, z) = z := by
  have hzero : β ((i : ℝ) * δ, z) = 0 := by
    by_contra hne
    exact hz ⟨((i : ℝ) * δ, z), subset_tsupport β hne, rfl⟩
  simp only [graphStep, hzero, zero_smul, add_zero]

/-- Below a uniform radius, every step of the graph motion is realised by a diffeomorphism of the
model. -/
theorem WhitneyPairModel.exists_radius_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ δ : ℝ,
          0 ≤ δ →
            δ < ε →
              ∀ i : ℕ,
                ∀ t : ℝ,
                  ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
                    ∀ z, d z = graphStep β δ i (t, z) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    SmallPerturbation.exists_uniform_radius_bumpTranslation hβ hcompact
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε i t
  have hnorm : ‖Real.smoothTransition t • verticalVector δ‖ ≤ δ := by
    rw [norm_smul, norm_verticalVector hδ, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact mul_le_of_le_one_left hδ (Real.smoothTransition.le_one t)
  obtain ⟨d, hd, _⟩ :=
    hsmall ((i : ℝ) * δ) (Real.smoothTransition t • verticalVector δ) (hnorm.trans_lt hδε)
  exact ⟨d, hd⟩

/-- The tracking property of the steps: the step at index `i` carries the vertical graph at time `i
δ` to the vertical graph at time `(i + 1) δ`. -/
theorem WhitneyPairModel.graphStep_tracking {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) {δ : ℝ} {i : ℕ} (hi : (i : ℝ) * δ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    graphStep g.cutoff δ i (1, verticalGraph g.height ((i : ℝ) * δ) s) =
      verticalGraph g.height (((i : ℝ) + 1) * δ) s := by
  rw [graphStep, g.tracking _ hi, Real.smoothTransition.one, one_smul]
  ext <;> simp [verticalGraph, verticalVector, smul_eq_mul]
  ring

/-- A graph motion of the planar model: a compactly supported smooth ambient isotopy preserving the
horizontal and normal coordinates and pushing the lower sheet onto the vertical graph of the
height function. -/
structure WhitneyPairModel.GraphMotion {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) where
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph g.height 1 s

/-- Graph-motion data give rise to a graph motion: iterating the steps of a sufficiently fine
subdivision. -/
theorem WhitneyPairModel.GraphMotionData.nonempty_graphMotion {h : ℝ}
    {U : Set WhitneyPairModel.Space} (g : WhitneyPairModel.GraphMotionData h U) :
    Nonempty (WhitneyPairModel.GraphMotion g) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    WhitneyPairModel.exists_radius_graphStep g.smooth_cutoff g.compact_cutoff
  obtain ⟨N, hN, hNsmall⟩ := Real.exists_nat_pos_inv_lt hε
  let δ : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hδ : 0 ≤ δ := (inv_pos.mpr hNreal).le
  have htotal : (N : ℝ) * δ = 1 := mul_inv_cancel₀ hNreal.ne'
  let B : ℕ → ℝ × WhitneyPairModel.Space → WhitneyPairModel.Space :=
    WhitneyPairModel.graphStep g.cutoff δ
  let A : ℝ × WhitneyPairModel.Space → WhitneyPairModel.Space :=
    SmallPerturbation.composeFamily B N
  have htrack :
    ∀ j ≤ N,
      ∀ s,
        SmallPerturbation.composeFamily B j (1, WhitneyPairModel.firstSheet (s, 0)) =
          WhitneyPairModel.verticalGraph g.height ((j : ℝ) * δ) s := by
    intro j
    induction j with
    | zero =>
      intro _ s
      simp [SmallPerturbation.composeFamily, WhitneyPairModel.firstSheet,
        WhitneyPairModel.verticalGraph]
    | succ j ih =>
      intro hj s
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      have htime : (j : ℝ) * δ ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (Nat.cast_nonneg j) hδ, ?_⟩
        calc
          (j : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN) hδ
          _ = 1 := htotal
      change
        WhitneyPairModel.graphStep g.cutoff δ j
            (1,
              SmallPerturbation.composeFamily B j
                (1, WhitneyPairModel.firstSheet (s, 0))) =
          _
      rw [ih hjN s, WhitneyPairModel.graphStep_tracking g htime s, Nat.cast_add,
        Nat.cast_one]
  refine
    ⟨{  support := Prod.snd '' tsupport g.cutoff
        compact_support := g.compact_cutoff.isCompact.image continuous_snd
        support_subset := ?_
        family := A
        smooth :=
          SmallPerturbation.contDiff_composeFamily
            (fun i => WhitneyPairModel.contDiff_graphStep g.smooth_cutoff δ i) N
        initial :=
          SmallPerturbation.composeFamily_zero
            (WhitneyPairModel.graphStep_zero g.cutoff δ) N
        diffeomorph :=
          SmallPerturbation.exists_diffeomorph_composeFamily (hsmall δ hδ hNsmall) N
        fixed := fun t z hz =>
          SmallPerturbation.composeFamily_fixed
            (fun i t _ hz => WhitneyPairModel.graphStep_fixed g.cutoff δ i t hz) N t hz
        horizontal := fun t z =>
          SmallPerturbation.composeFamily_preserves (B := B) (f :=
            fun z : WhitneyPairModel.Space => z.1.1)
            (WhitneyPairModel.graphStep_horizontal g.cutoff δ) N t z
        normal := fun t z =>
          SmallPerturbation.composeFamily_preserves (B := B) (f :=
            fun z : WhitneyPairModel.Space => z.2)
            (WhitneyPairModel.graphStep_normal g.cutoff δ) N t z
        tracking := ?_ }⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact g.support_cutoff hp
  · intro s
    change
      SmallPerturbation.composeFamily B N (1, WhitneyPairModel.firstSheet (s, 0)) = _
    rw [htrack N le_rfl s, htotal]

/-- After the graph motion the lower sheet has been pushed above the upper sheet, so the two no
longer meet. -/
theorem WhitneyPairModel.GraphMotion.firstSheet_ne_secondSheet {h : ℝ}
    {U : Set WhitneyPairModel.Space} {g : WhitneyPairModel.GraphMotionData h U}
    (a : WhitneyPairModel.GraphMotion g) (hh : 0 < h) (p q : WhitneyPairModel.Sheet) :
    a.family (1, WhitneyPairModel.firstSheet p) ≠ WhitneyPairModel.secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : WhitneyPairModel.Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : WhitneyPairModel.Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : g.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [WhitneyPairModel.verticalGraph, WhitneyPairModel.secondSheet,
      one_mul] using congrArg (fun z : WhitneyPairModel.Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ g.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (g.above q.1 habs).ne ht.symm

/-- The sheet direction of the lower sheet in the rank-three model: a line. -/
abbrev RankThreeWhitneyModel.Lower :=
  EuclideanSpace ℝ (Fin 1)

/-- The sheet direction of the upper sheet in the rank-three model: a plane. -/
abbrev RankThreeWhitneyModel.Upper :=
  EuclideanSpace ℝ (Fin 2)

/-- The ambient model of the rank-three Whitney situation: the bigon plane times the lower and upper
normal directions. -/
abbrev RankThreeWhitneyModel.Space :=
  (ℝ × ℝ) × (Lower × Upper)

/-- The parameter space of the lower sheet: a time coordinate and the lower sheet direction. -/
abbrev RankThreeWhitneyModel.LowerSheet :=
  ℝ × Lower

/-- The parameter space of the upper sheet: a time coordinate and the upper sheet direction. -/
abbrev RankThreeWhitneyModel.UpperSheet :=
  ℝ × Upper

/-- The lower sheet of the rank-three model: the sheet through the lower boundary arc, spread in the
lower direction. -/
def RankThreeWhitneyModel.firstSheet (p : LowerSheet) : Space :=
  ((p.1, 0), (p.2, 0))

/-- The upper sheet of the rank-three model: the sheet through the parabolic boundary arc, spread in
the upper direction. -/
def RankThreeWhitneyModel.secondSheet (h : ℝ) (p : UpperSheet) : Space :=
  ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

/-- The lower sheet is smooth. -/
theorem RankThreeWhitneyModel.contDiff_firstSheet : ContDiff ℝ ∞ firstSheet := by
  unfold firstSheet
  fun_prop

/-- The upper sheet is smooth. -/
theorem RankThreeWhitneyModel.contDiff_secondSheet (h : ℝ) : ContDiff ℝ ∞ (secondSheet h) :=
  by
  unfold secondSheet
  fun_prop

/-- The derivative of the lower sheet parametrisation. -/
def RankThreeWhitneyModel.firstSheetDerivative : LowerSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Lower).prod 0).prod ((ContinuousLinearMap.snd ℝ ℝ Lower).prod 0)

/-- The derivative of the upper sheet parametrisation at the time `s`, whose vertical component is
the slope `-2 h s` of the parabola. -/
def RankThreeWhitneyModel.secondSheetDerivative (h s : ℝ) : UpperSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Upper).prod
        ((-2 * h * s) • ContinuousLinearMap.fst ℝ ℝ Upper)).prod
    ((0 : UpperSheet →L[ℝ] Lower).prod (ContinuousLinearMap.snd ℝ ℝ Upper))

/-- Value of the derivative of the lower sheet parametrisation. -/
theorem RankThreeWhitneyModel.firstSheetDerivative_apply (p : LowerSheet) :
    firstSheetDerivative p = ((p.1, 0), (p.2, 0)) :=
  rfl

/-- Value of the derivative of the upper sheet parametrisation. -/
theorem RankThreeWhitneyModel.secondSheetDerivative_apply (h s : ℝ) (p : UpperSheet) :
    secondSheetDerivative h s p = ((p.1, (-2 * h * s) * p.1), (0, p.2)) :=
  rfl

/-- The lower sheet parametrisation has the stated derivative. -/
theorem RankThreeWhitneyModel.hasFDerivAt_firstSheet (p : LowerSheet) :
    HasFDerivAt firstSheet firstSheetDerivative p :=
  firstSheetDerivative.hasFDerivAt

/-- The upper sheet parametrisation has the stated derivative. -/
theorem RankThreeWhitneyModel.hasFDerivAt_secondSheet (h : ℝ) (p : UpperSheet) :
    HasFDerivAt (secondSheet h) (secondSheetDerivative h p.1) p := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ Upper).hasFDerivAt (x := p)
  have hu := (ContinuousLinearMap.snd ℝ ℝ Upper).hasFDerivAt (x := p)
  have ht := ((hasFDerivAt_const (1 : ℝ) p).sub (hs.pow 2)).const_mul h
  have hd := (hs.prodMk ht).prodMk ((hasFDerivAt_const (0 : Lower) p).prodMk hu)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [secondSheetDerivative, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', zero_apply, sub_apply, smul_apply, smul_eq_mul]
  congr 2
  norm_num [two_smul]
  ring

/-- A linear identification of the lower direction plus a line with the plane. -/
def RankThreeWhitneyModel.lowerSplit : (Lower × ℝ) ≃L[ℝ] WhitneyPairModel.Plane :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp [Lower, WhitneyPairModel.Plane, Module.finrank_prod])

/-- The inclusion of the lower direction into the plane. -/
def RankThreeWhitneyModel.lowerInclude : Lower →L[ℝ] WhitneyPairModel.Plane :=
  lowerSplit.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Lower ℝ)

/-- The projection of the plane onto the lower direction. -/
def RankThreeWhitneyModel.lowerProject : WhitneyPairModel.Plane →L[ℝ] Lower :=
  (ContinuousLinearMap.fst ℝ Lower ℝ).comp lowerSplit.symm.toContinuousLinearMap

/-- The projection is a left inverse of the inclusion of the lower direction. -/
theorem RankThreeWhitneyModel.lowerProject_include (u : Lower) :
    lowerProject (lowerInclude u) = u := by
  change (lowerSplit.symm (lowerSplit (u, 0))).1 = u
  rw [lowerSplit.symm_apply_apply]

/-- The inclusion of the pair of normal directions into the pair of planes of the planar model. -/
def RankThreeWhitneyModel.normalInclude :
    (Lower × Upper) →L[ℝ] (WhitneyPairModel.Plane × WhitneyPairModel.Plane) :=
  lowerInclude.prodMap (ContinuousLinearMap.id ℝ Upper)

/-- The projection of the pair of planes onto the pair of normal directions. -/
def RankThreeWhitneyModel.normalProject :
    (WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (Lower × Upper) :=
  lowerProject.prodMap (ContinuousLinearMap.id ℝ Upper)

/-- The normal projection is a left inverse of the normal inclusion. -/
theorem RankThreeWhitneyModel.normalProject_include :
    Function.LeftInverse normalProject normalInclude := fun z =>
  Prod.ext (lowerProject_include z.1) rfl

/-- The inclusion of the rank-three model into the planar model. -/
def RankThreeWhitneyModel.expand : Space →L[ℝ] WhitneyPairModel.Space :=
  FiberRestriction.embed normalInclude

/-- The projection of the planar model onto the rank-three model. -/
def RankThreeWhitneyModel.collapse : WhitneyPairModel.Space →L[ℝ] Space :=
  FiberRestriction.project normalProject

/-- The projection is a left inverse of the inclusion. -/
theorem RankThreeWhitneyModel.collapse_expand (z : Space) : collapse (expand z) = z :=
  FiberRestriction.project_embed normalInclude normalProject normalProject_include z

/-- The inclusion is the identity on the zero section. -/
theorem RankThreeWhitneyModel.expand_zero (p : ℝ × ℝ) : expand (p, 0) = (p, 0) :=
  Prod.ext rfl normalInclude.map_zero

/-- The projection is the identity on the zero section. -/
theorem RankThreeWhitneyModel.collapse_zero (p : ℝ × ℝ) : collapse (p, 0) = (p, 0) :=
  Prod.ext rfl normalProject.map_zero

/-- The vertical graph of the height function, read in the rank-three model. -/
def RankThreeWhitneyModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

/-- The projection carries the planar vertical graph to the rank-three one. -/
theorem RankThreeWhitneyModel.collapse_verticalGraph (B : ℝ → ℝ) (t s : ℝ) :
    collapse (WhitneyPairModel.verticalGraph B t s) = verticalGraph B t s :=
  collapse_zero _

/-- A graph motion of the rank-three model: the analogue of `WhitneyPairModel.GraphMotion` in the
model with the two normal directions. -/
structure RankThreeWhitneyModel.GraphMotion (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph height 1 s

/-- A graph motion of the rank-three model exists over any open neighbourhood of the zero section of
the bigon. -/
theorem RankThreeWhitneyModel.nonempty_graphMotion {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : ∀ p ∈ WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ U) :
    Nonempty (GraphMotion h U) := by
  let V : Set WhitneyPairModel.Space := collapse ⁻¹' U
  have hV : IsOpen V := hU.preimage collapse.continuous
  have hKV :
    Set.MapsTo WhitneyPairModel.bigonEmbedding (WhitneyPairModel.bigon h) V := by
    intro p hp
    change collapse (p, 0) ∈ U
    rw [collapse_zero]
    exact hKU p hp
  obtain ⟨g⟩ := WhitneyPairModel.nonempty_graphMotionData hh hV hKV
  obtain ⟨a⟩ := g.nonempty_graphMotion
  let A : ℝ × Space → Space := fun p => collapse (a.family (p.1, expand p.2))
  have hA : ContDiff ℝ ∞ A :=
    collapse.contDiff.comp
      (a.smooth.comp (contDiff_fst.prodMk (expand.contDiff.comp contDiff_snd)))
  refine
    ⟨{  height := g.height
        nonneg_height := g.nonneg_height
        above := g.above
        support := collapse '' a.support
        compact_support := a.compact_support.image collapse.continuous
        support_subset := ?_
        family := A
        smooth := hA
        initial := ?_
        diffeomorph := ?_
        fixed := ?_
        horizontal := ?_
        normal := ?_
        tracking := ?_ }⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact a.support_subset hz
  · intro z
    change collapse (a.family (0, expand z)) = z
    rw [a.initial, collapse_expand]
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hn : ∀ z, (d z).2 = z.2 := by
      intro z
      rw [hd]
      exact a.normal t z
    refine
      ⟨FiberRestriction.restrict normalInclude normalProject normalProject_include d hn, ?_⟩
    intro z
    change collapse (d (expand z)) = collapse (a.family (t, expand z))
    rw [hd]
  · intro t z hz
    have hz' : expand z ∉ a.support := fun hs => hz ⟨expand z, hs, collapse_expand z⟩
    change collapse (a.family (t, expand z)) = z
    rw [a.fixed t _ hz', collapse_expand]
  · intro t z
    change (a.family (t, expand z)).1.1 = z.1.1
    rw [a.horizontal]
    rfl
  · intro t z
    change normalProject (a.family (t, expand z)).2 = z.2
    rw [a.normal]
    exact normalProject_include z.2
  · intro s
    have he : expand (firstSheet (s, 0)) = WhitneyPairModel.firstSheet (s, 0) :=
      expand_zero (s, 0)
    change collapse (a.family (1, expand (firstSheet (s, 0)))) = verticalGraph g.height 1 s
    rw [he, a.tracking, collapse_verticalGraph]

/-- After the rank-three graph motion the lower sheet has been pushed off the upper sheet. -/
theorem RankThreeWhitneyModel.GraphMotion.firstSheet_ne_secondSheet {h : ℝ}
    {U : Set RankThreeWhitneyModel.Space} (a : RankThreeWhitneyModel.GraphMotion h U)
    (hh : 0 < h) (p : RankThreeWhitneyModel.LowerSheet)
    (q : RankThreeWhitneyModel.UpperSheet) :
    a.family (1, RankThreeWhitneyModel.firstSheet p) ≠
      RankThreeWhitneyModel.secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : RankThreeWhitneyModel.Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : RankThreeWhitneyModel.Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : a.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [RankThreeWhitneyModel.verticalGraph,
      RankThreeWhitneyModel.secondSheet, one_mul] using
      congrArg (fun z : RankThreeWhitneyModel.Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ a.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (a.above q.1 habs).ne ht.symm

/-- A tangent-adapted chart of a rank-three tubular bigon: a chart of the tubular neighbourhood in
the coordinates of the rank-three model whose differential along the bigon is a sheared block
matching the two sheet differentials on the two boundary arcs. -/
structure TubularBigon.RankThreeTangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map) where
  base : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        FrameField.shearedBlock (base (WhitneyPairModel.upperBoundaryArc h t))
            (normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (FrameField.shearedBlock (base p) (normal p))
        (p, 0)

/-- The Whitney condition gives a tangent-adapted chart: if the two corner intersection signs are
opposite, a rank-three tangent-adapted chart exists. -/
theorem TubularBigon.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeTangentAdaptedChart tube d e) := by
  obtain ⟨W, hW, hlo, O, hO, hKO, C, hC, hhi, hframe⟩ :=
    tube.exists_rankThree_adapted_frame_of_opposite_corner_signs d e hsign
  obtain ⟨Dlo, hDlo, hIDlo, hBlo⟩ :=
    d.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.lower_chart_center_mem_target d ht)
  obtain ⟨Dhi, hDhi, hIDhi, hBhi⟩ :=
    e.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.upper_chart_center_mem_target e ht)
  have htime (t y : ℝ) : WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    WhitneyPairModel.arcTime (WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have htimeK :
    Set.MapsTo WhitneyPairModel.arcTime (WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  let U := O ∩ WhitneyPairModel.arcTime ⁻¹' (Dlo ∩ Dhi)
  have hU : IsOpen U :=
    hO.inter ((hDlo.inter hDhi).preimage WhitneyPairModel.contDiff_arcTime.continuous)
  have hKU : WhitneyPairModel.bigon h ⊆ U := fun p hp =>
    ⟨hKO hp, hIDlo (htimeK hp), hIDhi (htimeK hp)⟩
  let A : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ)) :=
    fun p =>
    (d.sheetBaseFrame tube.chart (WhitneyPairModel.arcTime p)).coprod
      (e.sheetBaseFrame tube.chart (WhitneyPairModel.arcTime p))
  let N :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    fun p => (W p).coprod (C p)
  have hA : ContDiffOn ℝ ∞ A U :=
    FrameField.contDiffOn_coprod
      (hBlo.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.1))
      (hBhi.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
  have hN : ContDiffOn ℝ ∞ N U :=
    FrameField.contDiffOn_coprod hW.contDiffOn (hC.mono Set.inter_subset_left)
  have hiN : ∀ p ∈ U, (N p).IsInvertible := fun p hp =>
    FrameField.isInvertible_coprod_of_bijective _ _ (hframe p hp.1)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        FrameField.shearedBlock (A (2 * t - 1, 0)) (N (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u) := by
    intro t ht u
    have hWt : W (2 * t - 1, 0) = d.normalFrame tube.chart t := by
      have hg := (hlo t ht).eq_of_nhds
      dsimp only [Function.comp_apply] at hg
      rwa [htime] at hg
    rw [d.sheetDifferential_transverse_eq tube.chart ht (tube.lower_chart_center_mem_target d ht),
      FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, add_zero, zero_add, htime, hWt]
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        FrameField.shearedBlock (A (WhitneyPairModel.upperBoundaryArc h t))
            (N (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v) := by
    intro t ht v
    rw [e.sheetDifferential_transverse_eq tube.chart ht (tube.upper_chart_center_mem_target e ht),
      FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, zero_add, htq, hhi t ht]
  have hz :
    WhitneyPairModel.bigon h ×ˢ {(0 : EuclideanSpace ℝ (Fin 3))} ⊆ tube.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, Φ, hsource, hformula, htarget, -, hderiv⟩ :=
    FrameField.exists_sheared_tubular_chart tube.chart
      (WhitneyPairModel.isCompact_bigon tube.height_pos) hU hKU hz hA hN
      (fun p hp => hiN p (hKU hp))
  refine
    ⟨{  base := A
        normal := N
        domain := U
        open_domain := hU
        contains := hKU
        smooth_base := hA
        smooth_normal := hN
        normal_invertible := hiN
        lower_transverse := hlow
        upper_transverse := hupp
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        coordinates := hformula
        target_subset := htarget
        transition_derivative := hderiv }⟩
  intro p
  rw [hformula, FrameField.shearedMap_zero, tube.zero_section]

/-- The tangent-adapted chart in the planar model: the variant of `RankThreeTangentAdaptedChart`
whose two sheet directions are planes. -/
structure TubularBigon.TangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 4)
    (d :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T
        l.map) where
  base : (ℝ × ℝ) → ((WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ]
        EuclideanSpace ℝ (Fin 4))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : WhitneyPairModel.Plane,
        FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : WhitneyPairModel.Plane,
        FrameField.shearedBlock (base (WhitneyPairModel.upperBoundaryArc h t))
            (normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, WhitneyPairModel.Space) 𝓘(ℝ, E) WhitneyPairModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (FrameField.shearedBlock (base p) (normal p))
        (p, 0)

/-- The derivative of the affine retiming `s ↦ (s + 1) / 2` of the time coordinate. -/
def WhitneyPairModel.halfTimeDerivative {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : (ℝ × A) →L[ℝ] (ℝ × A) :=
  (((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ A)).prod (ContinuousLinearMap.snd ℝ ℝ A)

/-- The retiming derivative halves the time coordinate and leaves the sheet directions alone. -/
theorem WhitneyPairModel.halfTimeDerivative_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (v : (ℝ × A)) : halfTimeDerivative v = (v.1 / 2, v.2) := by
  apply Prod.ext
  · change (1 / 2 : ℝ) * v.1 = v.1 / 2
    ring
  · rfl

/-- The affine change of time coordinate `s ↦ (s + 1) / 2` carrying the boundary-arc parameter `[-1,
1]` to `[0, 1]`. -/
def WhitneyPairModel.sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : (ℝ × A) :=
  halfTimeDerivative p + ((1 / 2 : ℝ), 0)

/-- Value of the retiming of the time coordinate. -/
theorem WhitneyPairModel.sheetTimeCoordinates_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : sheetTimeCoordinates p = ((p.1 + 1) / 2, p.2) := by
  rw [sheetTimeCoordinates, halfTimeDerivative_apply]
  apply Prod.ext
  · change p.1 / 2 + 1 / 2 = (p.1 + 1) / 2
    ring
  · exact add_zero _

/-- The retiming sends the boundary-arc parameter `2 t - 1` to `t`. -/
theorem WhitneyPairModel.sheetTimeCoordinates_center {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (t : ℝ) : sheetTimeCoordinates (2 * t - 1, (0 : A)) = (t, 0) := by
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- The retiming is smooth. -/
theorem WhitneyPairModel.contDiff_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeCoordinates (A := A)) :=
  (halfTimeDerivative (A := A)).contDiff.add contDiff_const

/-- The retiming has derivative `halfTimeDerivative` everywhere. -/
theorem WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : HasFDerivAt sheetTimeCoordinates halfTimeDerivative p :=
  halfTimeDerivative.hasFDerivAt.add_const ((1 / 2 : ℝ), (0 : A))

/-- The domain of the transition from the strip chart of a sheet to a tubular chart, read along the
sheet directions. -/
def StripNormalData.sheetTransitionDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B) ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target)

/-- The domain of the sheet transition is open. -/
theorem StripNormalData.isOpen_sheetTransitionDomain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.sheetTransitionDomain Ψ) := by
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact hO.preimage (ContinuousLinearMap.inl ℝ (ℝ × A) B).continuous

/-- The sheet transition is smooth on its domain. -/
theorem StripNormalData.contDiffOn_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetTransition Ψ) (d.sheetTransitionDomain Ψ) := by
  have hfull : ContDiffOn ℝ ∞ (Ψ.symm ∘ d.chart) (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    (Ψ.contMDiffOn_invFun.comp (d.chart.contMDiffOn_toFun.mono Set.inter_subset_left)
        (fun _ hp => hp.2)).contDiffOn
  exact hfull.comp (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffOn (fun _ hp => hp)

/-- The sheet transition read in the boundary-arc time parameter. -/
def StripNormalData.retimedSheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  d.sheetTransition Ψ ∘ WhitneyPairModel.sheetTimeCoordinates

/-- The domain of the retimed sheet transition. -/
def StripNormalData.retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  WhitneyPairModel.sheetTimeCoordinates ⁻¹' d.sheetTransitionDomain Ψ

/-- The domain of the retimed sheet transition is open. -/
theorem StripNormalData.isOpen_retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.retimedDomain Ψ) :=
  (d.isOpen_sheetTransitionDomain Ψ).preimage
    WhitneyPairModel.contDiff_sheetTimeCoordinates.continuous

/-- The retimed sheet transition is smooth on its domain. -/
theorem StripNormalData.contDiffOn_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.retimedSheetTransition Ψ) (d.retimedDomain Ψ) :=
  (d.contDiffOn_sheetTransition Ψ).comp
    WhitneyPairModel.contDiff_sheetTimeCoordinates.contDiffOn (fun _ hp => hp)

/-- The centre of the strip at a parameter of `[0, 1]` lies in the domain of the retimed
transition. -/
theorem StripNormalData.retimedDomain_contains_center {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (2 * t - 1, (0 : A)) ∈ d.retimedDomain Ψ := by
  change WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0) ∈ d.sheetTransitionDomain Ψ
  rw [WhitneyPairModel.sheetTimeCoordinates_center]
  exact ⟨d.line ht, htarget⟩

/-- The derivative of the retimed sheet transition at a centre point is the sheet differential
composed with the retiming derivative. -/
theorem StripNormalData.hasFDerivAt_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    HasFDerivAt (d.retimedSheetTransition Ψ)
      ((d.sheetDifferential Ψ t).comp WhitneyPairModel.halfTimeDerivative) (2 * t - 1, 0) :=
  by
  have hd :
    HasFDerivAt (d.sheetTransition Ψ) (d.sheetDifferential Ψ t)
      (WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0)) := by
    rw [WhitneyPairModel.sheetTimeCoordinates_center]
    exact ((d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp (2 * t - 1, (0 : A)) (WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates _)

/-- Along the lower boundary arc, the sheared block of a tangent-adapted chart restricts to the
retimed sheet differential of the lower sheet. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.lower_model_tangent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))).comp
        RankThreeWhitneyModel.firstSheetDerivative =
      (d.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc : d.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, 0), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.lower_sheetDifferential_arc d ht]
    ext <;> simp [smul_eq_mul]
  change
    FrameField.shearedBlock _ _ (RankThreeWhitneyModel.firstSheetDerivative v) =
      d.sheetDifferential tube.chart t (WhitneyPairModel.halfTimeDerivative v)
  rw [WhitneyPairModel.halfTimeDerivative_apply]
  calc
    FrameField.shearedBlock _ _ (RankThreeWhitneyModel.firstSheetDerivative v) =
        FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            ((v.1, 0), 0) +
          FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            (0, (v.2, 0)) := by
      rw [← map_add]
      congr 1
      simp only [RankThreeWhitneyModel.firstSheetDerivative_apply, Prod.mk_add_mk, add_zero,
        zero_add]
    _ =
        d.sheetDifferential tube.chart t (v.1 / 2, 0) +
          d.sheetDifferential tube.chart t (0, v.2) := by
      rw [FrameField.shearedBlock_horizontal, c.lower_transverse t ht, harc]
    _ = d.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

/-- Along the upper boundary arc, the sheared block of a tangent-adapted chart restricts to the
retimed sheet differential of the upper sheet. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.upper_model_tangent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t))).comp
        (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1)) =
      (e.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc :
    e.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.upper_sheetDifferential_arc e ht]
    ext <;> simp [smul_eq_mul]
    ring
  change
    FrameField.shearedBlock _ _
        (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
      e.sheetDifferential tube.chart t (WhitneyPairModel.halfTimeDerivative v)
  rw [WhitneyPairModel.halfTimeDerivative_apply]
  calc
    FrameField.shearedBlock _ _
          (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
        FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t))
            ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) +
          FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v.2)) := by
      rw [← map_add]
      congr 1
      simp only [RankThreeWhitneyModel.secondSheetDerivative_apply, Prod.mk_add_mk,
        add_zero, zero_add]
    _ =
        e.sheetDifferential tube.chart t (v.1 / 2, 0) +
          e.sheetDifferential tube.chart t (0, v.2) := by
      rw [FrameField.shearedBlock_horizontal, c.upper_transverse t ht, harc]
    _ = e.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

/-- The projection of a sheet parameter to its centre: `(s, u) ↦ (s, 0)`. -/
def SheetCorrection.centerProjection {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    (ℝ × A) →L[ℝ] (ℝ × A) :=
  (ContinuousLinearMap.fst ℝ ℝ A).prod (0 : (ℝ × A) →L[ℝ] A)

/-- Value of the centre projection. -/
theorem SheetCorrection.centerProjection_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : ℝ × A) : centerProjection p = (p.1, 0) :=
  rfl

/-- The correction of `G` towards `R` along a sheet: the difference `R - G` with its value at the
centre subtracted, so that it vanishes on the centre line. -/
def SheetCorrection.centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (p : ℝ × A) : F :=
  (R p - G p) - (R (centerProjection p) - G (centerProjection p))

/-- The centred correction vanishes on the centre line. -/
theorem SheetCorrection.centeredCorrection_zero {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (s : ℝ) :
    centeredCorrection R G (s, 0) = 0 := by
  simp only [centeredCorrection, centerProjection_apply, sub_self]

/-- Where `R` and `G` agree at the centre, the centred correction is simply `R - G`. -/
theorem SheetCorrection.centeredCorrection_eq_sub {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] {R G : (ℝ × A) → F} {p : ℝ × A}
    (hcenter : R (p.1, 0) = G (p.1, 0)) : centeredCorrection R G p = R p - G p := by
  simp only [centeredCorrection, centerProjection_apply, hcenter, sub_self, sub_zero]

/-- The centred correction is smooth where `R` and `G` are. -/
theorem SheetCorrection.contDiffOn_centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F] {R G : (ℝ × A) → F}
    {D : Set (ℝ × A)} (hR : ContDiffOn ℝ ∞ R D) (hG : ContDiffOn ℝ ∞ G D) :
    ContDiffOn ℝ ∞ (centeredCorrection R G) (D ∩ centerProjection ⁻¹' D) :=
  ((hR.sub hG).mono Set.inter_subset_left).sub
    ((hR.sub hG).comp (centerProjection (A := A)).contDiff.contDiffOn (fun _ hp => hp.2))

/-- If `R` and `G` have the same derivative at a centre point, the centred correction has vanishing
derivative there. -/
theorem SheetCorrection.hasFDerivAt_centeredCorrection_zero {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R G : (ℝ × A) → F} {L : (ℝ × A) →L[ℝ] F} {s : ℝ} (hR : HasFDerivAt R L (s, 0))
    (hG : HasFDerivAt G L (s, 0)) :
    HasFDerivAt (centeredCorrection R G) (0 : (ℝ × A) →L[ℝ] F) (s, 0) := by
  have hdiff : HasFDerivAt (fun p => R p - G p) (0 : (ℝ × A) →L[ℝ] F) (s, (0 : A)) := by
    convert hR.sub hG using 1 <;>
      first
      | rfl
      | simp only [sub_self]
  have hcenter := hdiff.comp (s, (0 : A)) (centerProjection (A := A)).hasFDerivAt
  convert hdiff.sub hcenter using 1 <;>
    first
    | rfl
    | simp only [ContinuousLinearMap.zero_comp, sub_self]

/-- The lower sheet coordinates of a point of the rank-three model: its time coordinate and its
lower normal coordinate. -/
def RankThreeWhitneyModel.lowerSheetCoordinates : Space →L[ℝ] LowerSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.fst ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

/-- The upper sheet coordinates of a point of the rank-three model: its time coordinate and its
upper normal coordinate. -/
def RankThreeWhitneyModel.upperSheetCoordinates : Space →L[ℝ] UpperSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.snd ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

/-- The map `G` corrected along both sheets so as to agree with the prescribed parametrisations
`Rlo` and `Rhi` there, without changing it on the zero section. -/
def RankThreeWhitneyModel.correctedSheetMap {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : Space) : F :=
  G p + SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (lowerSheetCoordinates p) +
    SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (upperSheetCoordinates p)

/-- The corrected map agrees with `G` on the zero section of the model. -/
theorem RankThreeWhitneyModel.correctedSheetMap_zero {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : ℝ × ℝ) :
    correctedSheetMap G Rlo Rhi h (p, 0) = G (p, 0) := by
  change
    G (p, 0) + SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (p.1, 0) +
        SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (p.1, 0) =
      G (p, 0)
  rw [SheetCorrection.centeredCorrection_zero,
    SheetCorrection.centeredCorrection_zero, add_zero, add_zero]

/-- On the lower sheet the corrected map is the prescribed lower parametrisation. -/
theorem RankThreeWhitneyModel.correctedSheetMap_lower {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : LowerSheet)
    (hcenter : Rlo (q.1, 0) = G (firstSheet (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (firstSheet q) = Rlo q := by
  have hlo : lowerSheetCoordinates (firstSheet q) = q := rfl
  have hhi : upperSheetCoordinates (firstSheet q) = (q.1, 0) := rfl
  rw [correctedSheetMap, hlo, hhi, SheetCorrection.centeredCorrection_zero, add_zero,
    SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

/-- On the upper sheet the corrected map is the prescribed upper parametrisation. -/
theorem RankThreeWhitneyModel.correctedSheetMap_upper {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : UpperSheet)
    (hcenter : Rhi (q.1, 0) = G (secondSheet h (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (secondSheet h q) = Rhi q := by
  have hlo : lowerSheetCoordinates (secondSheet h q) = (q.1, 0) := rfl
  have hhi : upperSheetCoordinates (secondSheet h q) = q := rfl
  rw [correctedSheetMap, hlo, hhi, SheetCorrection.centeredCorrection_zero, add_zero,
    SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

/-- The domain of the correction: the points whose sheet coordinates and their centres lie in the
two sheet domains. -/
def RankThreeWhitneyModel.correctionDomain (U : Set Space) (Dlo : Set LowerSheet)
    (Dhi : Set UpperSheet) : Set Space :=
  U ∩
    (lowerSheetCoordinates ⁻¹' (Dlo ∩ SheetCorrection.centerProjection ⁻¹' Dlo) ∩
      upperSheetCoordinates ⁻¹' (Dhi ∩ SheetCorrection.centerProjection ⁻¹' Dhi))

/-- The correction domain is open. -/
theorem RankThreeWhitneyModel.isOpen_correctionDomain {U : Set Space} {Dlo : Set LowerSheet}
    {Dhi : Set UpperSheet} (hU : IsOpen U) (hDlo : IsOpen Dlo) (hDhi : IsOpen Dhi) :
    IsOpen (correctionDomain U Dlo Dhi) :=
  hU.inter
    (((hDlo.inter (hDlo.preimage SheetCorrection.centerProjection.continuous)).preimage
          lowerSheetCoordinates.continuous).inter
      ((hDhi.inter (hDhi.preimage SheetCorrection.centerProjection.continuous)).preimage
        upperSheetCoordinates.continuous))

/-- The corrected map is smooth on the correction domain. -/
theorem RankThreeWhitneyModel.contDiffOn_correctedSheetMap {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {U : Set Space} {Dlo : Set LowerSheet} {Dhi : Set UpperSheet}
    (hG : ContDiffOn ℝ ∞ G U) (hRlo : ContDiffOn ℝ ∞ Rlo Dlo)
    (hGlo : ContDiffOn ℝ ∞ (G ∘ firstSheet) Dlo) (hRhi : ContDiffOn ℝ ∞ Rhi Dhi)
    (hGhi : ContDiffOn ℝ ∞ (G ∘ secondSheet h) Dhi) :
    ContDiffOn ℝ ∞ (correctedSheetMap G Rlo Rhi h) (correctionDomain U Dlo Dhi) :=
  ((hG.mono Set.inter_subset_left).add
        ((SheetCorrection.contDiffOn_centeredCorrection hRlo hGlo).comp
          lowerSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.1))).add
    ((SheetCorrection.contDiffOn_centeredCorrection hRhi hGhi).comp
      upperSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.2))

/-- At a point of the zero section the corrected map has the same derivative as the uncorrected one,
the two corrections having vanishing derivative there. -/
theorem RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {p : ℝ × ℝ} {L : Space →L[ℝ] F} {Llo : LowerSheet →L[ℝ] F}
    {Lhi : UpperSheet →L[ℝ] F} (hG : HasFDerivAt G L (p, 0)) (hRlo : HasFDerivAt Rlo Llo (p.1, 0))
    (hGlo : HasFDerivAt (G ∘ firstSheet) Llo (p.1, 0)) (hRhi : HasFDerivAt Rhi Lhi (p.1, 0))
    (hGhi : HasFDerivAt (G ∘ secondSheet h) Lhi (p.1, 0)) :
    HasFDerivAt (correctedSheetMap G Rlo Rhi h) L (p, 0) := by
  have hlo :
    HasFDerivAt
      (SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) ∘ lowerSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (SheetCorrection.hasFDerivAt_centeredCorrection_zero hRlo hGlo).comp
        (p, (0 : Lower × Upper)) lowerSheetCoordinates.hasFDerivAt
  have hhi :
    HasFDerivAt
      (SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) ∘ upperSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (SheetCorrection.hasFDerivAt_centeredCorrection_zero hRhi hGhi).comp
        (p, (0 : Lower × Upper)) upperSheetCoordinates.hasFDerivAt
  convert (hG.add hlo).add hhi using 1 <;>
    first
    | rfl
    | simp only [add_zero]

/-- The sheared coordinates of a tangent-adapted chart: the model map of its base and normal
blocks. -/
def TubularBigon.RankThreeTangentAdaptedChart.shearedCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  FrameField.shearedMap c.base c.normal

/-- The corrected coordinates: the sheared coordinates corrected along the two sheets to agree with
the two retimed sheet transitions. -/
def TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  RankThreeWhitneyModel.correctedSheetMap c.shearedCoordinates
    (d.retimedSheetTransition tube.chart) (e.retimedSheetTransition tube.chart) h

/-- The corrected coordinates are the identity on the zero section. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) (p : ℝ × ℝ) :
    c.correctedCoordinates (p, 0) = (p, 0) := by
  rw [correctedCoordinates, RankThreeWhitneyModel.correctedSheetMap_zero]
  exact FrameField.shearedMap_zero c.base c.normal p

/-- At a point of the bigon, the sheared coordinates have the sheared block as derivative. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_shearedCoordinates_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    HasFDerivAt c.shearedCoordinates (FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) :=
  FrameField.hasFDerivAt_shearedMap_zero
    ((c.smooth_base.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))
    ((c.smooth_normal.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))

/-- The restriction of the sheared coordinates to the lower sheet has the retimed lower sheet
differential as derivative. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_lower {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ RankThreeWhitneyModel.firstSheet)
      ((d.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.lowerBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : RankThreeWhitneyModel.Lower))
      (RankThreeWhitneyModel.hasFDerivAt_firstSheet (2 * t - 1, 0))
  rwa [WhitneyPairModel.lowerBoundaryArc, c.lower_model_tangent ht] at hd

/-- The restriction of the sheared coordinates to the upper sheet has the retimed upper sheet
differential as derivative. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ RankThreeWhitneyModel.secondSheet h)
      ((e.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.upperBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : RankThreeWhitneyModel.Upper))
      (RankThreeWhitneyModel.hasFDerivAt_secondSheet h (2 * t - 1, 0))
  rwa [c.upper_model_tangent ht] at hd

/-- The corrected coordinates have the same derivative as the sheared ones at every point of the
bigon. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_correctedCoordinates_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    HasFDerivAt c.correctedCoordinates (FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) := by
  have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have hRlo :=
    d.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.lower_chart_center_mem_target d ht)
  have hRhi :=
    e.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.upper_chart_center_mem_target e ht)
  have hGlo := c.hasFDerivAt_sheared_lower ht
  have hGhi := c.hasFDerivAt_sheared_upper ht
  rw [htime] at hRlo hRhi hGlo hGhi
  exact
    RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero
      (c.hasFDerivAt_shearedCoordinates_zero hp) hRlo hGlo hRhi hGhi

/-- Along the lower boundary arc, the retimed lower sheet transition and the sheared coordinates of
the lower sheet have the same germ. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.retimed_lower_center_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.lower_sheetTransition_center_germ d ht).comp_tendsto htime] with s hs
  change
    d.sheetTransition tube.chart (WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      FrameField.shearedMap c.base c.normal ((s, 0), 0)
  rw [WhitneyPairModel.sheetTimeCoordinates_apply, FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [WhitneyPairModel.lowerBoundaryArc, hlin]

/-- Along the upper boundary arc, the retimed upper sheet transition and the sheared coordinates of
the upper sheet have the same germ. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.retimed_upper_center_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => e.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.upper_sheetTransition_center_germ e ht).comp_tendsto htime] with s hs
  change
    e.sheetTransition tube.chart (WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      FrameField.shearedMap c.base c.normal ((s, h * (1 - s ^ 2)), 0)
  rw [WhitneyPairModel.sheetTimeCoordinates_apply, FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [WhitneyPairModel.upperBoundaryArc, hlin]

/-- The domain of the sheared coordinates: the points whose base coordinate lies in the domain of
the chart blocks. -/
def TubularBigon.RankThreeTangentAdaptedChart.shearedDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.Space :=
  Prod.fst ⁻¹' c.domain

/-- The domain of the correction along the lower sheet. -/
def TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.LowerSheet :=
  d.retimedDomain tube.chart ∩ RankThreeWhitneyModel.firstSheet ⁻¹' c.shearedDomain

/-- The domain of the correction along the upper sheet. -/
def TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.UpperSheet :=
  e.retimedDomain tube.chart ∩ RankThreeWhitneyModel.secondSheet h ⁻¹' c.shearedDomain

/-- The interior of the set of times at which both sheet transitions agree with the sheared
coordinates on the centre lines. -/
def TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : Set ℝ :=
  interior
    {s |
      d.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
        e.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}

/-- The domain on which the corrected coordinates are defined and smooth: the correction domain
intersected with the matching times. -/
def TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.Space :=
  RankThreeWhitneyModel.correctionDomain c.shearedDomain c.lowerCorrectionDomain
      c.upperCorrectionDomain ∩
    (fun p : RankThreeWhitneyModel.Space => p.1.1) ⁻¹' c.centerMatchingTimes

/-- The domain of the sheared coordinates is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_shearedDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.shearedDomain :=
  c.open_domain.preimage continuous_fst

/-- The lower correction domain is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_lowerCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.lowerCorrectionDomain :=
  (d.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage RankThreeWhitneyModel.contDiff_firstSheet.continuous)

/-- The upper correction domain is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_upperCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.upperCorrectionDomain :=
  (e.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage
      (RankThreeWhitneyModel.contDiff_secondSheet h).continuous)

/-- The domain of the corrected coordinates is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_nonlinearDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.nonlinearDomain :=
  (RankThreeWhitneyModel.isOpen_correctionDomain c.isOpen_shearedDomain
        c.isOpen_lowerCorrectionDomain c.isOpen_upperCorrectionDomain).inter
    (isOpen_interior.preimage (by fun_prop))

/-- The corrected coordinates are smooth on their domain. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.contDiffOn_correctedCoordinates
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    ContDiffOn ℝ ∞ c.correctedCoordinates c.nonlinearDomain := by
  have hG : ContDiffOn ℝ ∞ c.shearedCoordinates c.shearedDomain :=
    FrameField.contDiffOn_shearedMap c.smooth_base c.smooth_normal
  exact
    (RankThreeWhitneyModel.contDiffOn_correctedSheetMap hG
          ((d.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp RankThreeWhitneyModel.contDiff_firstSheet.contDiffOn (fun _ hp => hp.2))
          ((e.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp (RankThreeWhitneyModel.contDiff_secondSheet h).contDiffOn
            (fun _ hp => hp.2))).mono
      Set.inter_subset_left

/-- Every parameter of `[0, 1]`, read as a boundary-arc time, is a matching time. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes_contains {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 2 * t - 1 ∈ c.centerMatchingTimes :=
  mem_interior_iff_mem_nhds.mpr
    ((c.retimed_lower_center_germ ht).and (c.retimed_upper_center_germ ht))

/-- The centre of the lower sheet at a parameter of `[0, 1]` lies in the lower correction domain. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain_contains_center
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : RankThreeWhitneyModel.Lower)) ∈ c.lowerCorrectionDomain := by
  refine
    ⟨d.retimedDomain_contains_center tube.chart ht (tube.lower_chart_center_mem_target d ht), ?_⟩
  exact c.contains (tube.lowerBoundaryArc_mem_bigon ht)

/-- The centre of the upper sheet at a parameter of `[0, 1]` lies in the upper correction domain. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain_contains_center
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : RankThreeWhitneyModel.Upper)) ∈ c.upperCorrectionDomain := by
  refine
    ⟨e.retimedDomain_contains_center tube.chart ht (tube.upper_chart_center_mem_target e ht), ?_⟩
  exact c.contains (tube.upperBoundaryArc_mem_bigon ht)

/-- The zero section over the bigon lies in the domain of the corrected coordinates. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain_contains_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    (p, (0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)) ∈
      c.nonlinearDomain := by
  have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have hlo := c.lowerCorrectionDomain_contains_center ht
  have hhi := c.upperCorrectionDomain_contains_center ht
  have hmatch := c.centerMatchingTimes_contains ht
  rw [htime] at hlo hhi hmatch
  exact ⟨⟨c.contains hp, ⟨hlo, hlo⟩, ⟨hhi, hhi⟩⟩, hmatch⟩

/-- A point of the lower sheet in the domain has its retimed parameter in the source of the lower
strip chart, with image in the target of the tubular chart. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.lower_native_parameters {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
        d.chart.source ∧
      d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.1.1.1

/-- A point of the upper sheet in the domain has its retimed parameter in the source of the upper
strip chart, with image in the target of the tubular chart. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.upper_native_parameters {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
        e.chart.source ∧
      e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.2.1.1

/-- On the lower sheet the corrected coordinates are the retimed lower sheet transition: the chart
is sheet-parametrised there. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_lower_of_mem_domain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (RankThreeWhitneyModel.firstSheet q) =
      d.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact RankThreeWhitneyModel.correctedSheetMap_lower q hm.1

/-- On the upper sheet the corrected coordinates are the retimed upper sheet transition: the chart
is sheet-parametrised there. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_upper_of_mem_domain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (RankThreeWhitneyModel.secondSheet h q) =
      e.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact RankThreeWhitneyModel.correctedSheetMap_upper q hm.2

/-- A sheet-parametrised chart of a rank-three tubular bigon: a chart in the coordinates of the
rank-three model which on the two model sheets is the strip chart of the corresponding sheet,
read in the retimed parameter. -/
structure TubularBigon.RankThreeSheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : RankThreeWhitneyModel.LowerSheet,
      RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : RankThreeWhitneyModel.UpperSheet,
      RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
          e.chart.source
  lower :
    ∀ q : RankThreeWhitneyModel.LowerSheet,
      RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        chart (RankThreeWhitneyModel.firstSheet q) =
          d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : RankThreeWhitneyModel.UpperSheet,
      RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        chart (RankThreeWhitneyModel.secondSheet h q) =
          e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)

/-- The corrected coordinates of a tangent-adapted chart give a sheet-parametrised chart. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.nonempty_rankThreeSheetParametrizedChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Nonempty (TubularBigon.RankThreeSheetParametrizedChart tube d e) := by
  have hinj :
    Set.InjOn c.correctedCoordinates
      (WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)}) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩ ⟨q, w⟩ ⟨hq, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [c.correctedCoordinates_zero, c.correctedCoordinates_zero] at heq
    exact Prod.ext (congrArg (fun v : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3) => v.1) heq) rfl
  have hlocal :
    ∀
      p ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      IsLocalDiffeomorphAt 𝓘(ℝ, RankThreeWhitneyModel.Space)
        𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) ∞ c.correctedCoordinates p := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      isLocalDiffeomorphAt_of_contMDiffOn (D := RankThreeWhitneyModel.Space) (E :=
        (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) (M := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3))
        c.isOpen_nonlinearDomain (c.nonlinearDomain_contains_zero hp)
        c.contDiffOn_correctedCoordinates.contMDiffOn
    rw [mfderiv_eq_fderiv, (c.hasFDerivAt_correctedCoordinates_zero hp).fderiv]
    exact
      FrameField.isInvertible_shearedBlock (c.base p) (c.normal p)
        (c.normal_invertible p (c.contains hp))
  have hzeroDomain :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      c.nonlinearDomain := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.nonlinearDomain_contains_zero hp
  obtain ⟨χ, hzeroχ, hχD, hχ⟩ :=
    exists_partialDiffeomorph_near_compact
      ((WhitneyPairModel.isCompact_bigon tube.height_pos).prod isCompact_singleton) hinj
      hlocal c.isOpen_nonlinearDomain hzeroDomain
  let Φ := χ.trans tube.chart
  have hzeroΦ :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      Φ.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hp, rfl⟩, ?_⟩
    change χ (p, 0) ∈ tube.chart.source
    rw [hχ, c.correctedCoordinates_zero]
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset
      (WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzeroΦ
  have hformula (p : RankThreeWhitneyModel.Space) :
    Φ p = tube.chart (c.correctedCoordinates p) := by
    change tube.chart (χ p) = tube.chart (c.correctedCoordinates p)
    rw [hχ]
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        target_subset := fun _ hy => hy.1
        lower_source := fun q hq => (c.lower_native_parameters (hχD hq.1)).1
        upper_source := fun q hq => (c.upper_native_parameters (hχD hq.1)).1
        lower := ?_
        upper := ?_ }⟩
  · intro p
    rw [hformula, c.correctedCoordinates_zero, tube.zero_section]
  · intro q hq
    rw [hformula, c.correctedCoordinates_lower_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.lower_native_parameters (hχD hq.1)).2
  · intro q hq
    rw [hformula, c.correctedCoordinates_upper_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.upper_native_parameters (hχD hq.1)).2

/-- The Whitney condition gives a sheet-parametrised chart: if the two corner intersection signs are
opposite, a rank-three sheet-parametrised chart exists. -/
theorem TubularBigon.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeSheetParametrizedChart tube d e) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeSheetParametrizedChart

/-- In a sheet-parametrised chart, the model lower sheet lands in the first sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.lower_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    c.chart (RankThreeWhitneyModel.firstSheet q) ∈ S := by
  rw [c.lower q hq]
  exact (d.sheet _ (c.lower_source q hq)).mpr rfl

/-- In a sheet-parametrised chart, the model upper sheet lands in the second sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.upper_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    c.chart (RankThreeWhitneyModel.secondSheet h q) ∈ T := by
  rw [c.upper q hq]
  exact (e.sheet _ (c.upper_source q hq)).mpr rfl

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

/-- The inverse `s ↦ 2 s - 1` of the retiming of the time coordinate. -/
def WhitneyPairModel.sheetTimeInverse {A : Type*} (q : (ℝ × A)) : (ℝ × A) :=
  (2 * q.1 - 1, q.2)

/-- The inverse retiming is smooth. -/
theorem WhitneyPairModel.contDiff_sheetTimeInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeInverse (A := A)) := by
  unfold sheetTimeInverse
  fun_prop

/-- The inverse retiming is a left inverse of the retiming. -/
theorem WhitneyPairModel.sheetTimeInverse_leftInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.LeftInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change 2 * ((q.1 + 1) / 2) - 1 = q.1
    ring
  · rfl

/-- The inverse retiming is a right inverse of the retiming. -/
theorem WhitneyPairModel.sheetTimeInverse_rightInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.RightInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change (2 * q.1 - 1 + 1) / 2 = q.1
    ring
  · rfl

/-- Near a point of the model lower sheet, a sheet-parametrised chart meets the first sheet exactly
in the model lower sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.eventually_lower_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (RankThreeWhitneyModel.firstSheet q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart d.chart d.sheet
    RankThreeWhitneyModel.contDiff_firstSheet.continuous
    WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    WhitneyPairModel.sheetTimeInverse_leftInverse
    WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.lower_source q hq, c.lower q hq⟩) hq

/-- Near a point of the model upper sheet, a sheet-parametrised chart meets the second sheet exactly
in the model upper sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.eventually_upper_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (RankThreeWhitneyModel.secondSheet h q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h)) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart e.chart e.sheet
    (RankThreeWhitneyModel.contDiff_secondSheet h).continuous
    WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    WhitneyPairModel.sheetTimeInverse_leftInverse
    WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.upper_source q hq, c.upper q hq⟩) hq

/-- The sheet-parametrised chart in the planar model: the variant of
`RankThreeSheetParametrizedChart` whose two sheet directions are planes. -/
structure TubularBigon.SheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 4)
    (d :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T
        l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, WhitneyPairModel.Space) 𝓘(ℝ, E) WhitneyPairModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.firstSheet q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.secondSheet h q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          e.chart.source
  lower :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.firstSheet q ∈ chart.source →
        chart (WhitneyPairModel.firstSheet q) =
          d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.secondSheet h q ∈ chart.source →
        chart (WhitneyPairModel.secondSheet h q) =
          e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)

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

/-- On the zero section, the rank-three model lower sheet is the lower boundary arc `{y = 0}`. -/
theorem RankThreeWhitneyModel.zero_mem_firstSheet_iff (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range firstSheet ↔ p.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun z : Space => z.1.2) hq).symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

/-- On the zero section, the rank-three model upper sheet is the parabolic boundary arc. -/
theorem RankThreeWhitneyModel.zero_mem_secondSheet_iff (h : ℝ) (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range (secondSheet h) ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · rintro ⟨q, hq⟩
    have hs : q.1 = p.1 := congrArg (fun z : Space => z.1.1) hq
    have ht : h * (1 - q.1 ^ 2) = p.2 := congrArg (fun z : Space => z.1.2) hq
    rw [hs] at ht
    exact ht.symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

/-- A sheet-parametrised chart has an open neighbourhood of the zero section of the bigon on which
it meets the two sheets exactly in the two model sheets. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.exists_open_full_sheet_neighborhood
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) :
    ∃ U : Set RankThreeWhitneyModel.Space,
      IsOpen U ∧
        WhitneyPairModel.bigon h ×ˢ
              {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
            U ∧
          U ⊆ c.chart.source ∧
            (∀ z ∈ U, c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet) ∧
              ∀ z ∈ U,
                c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
  have hzero :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      c.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩
  have hfirst :
    ∀
      z ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_first_iff hp).trans
        (RankThreeWhitneyModel.zero_mem_firstSheet_iff p).symm
  have hsecond :
    ∀
      z ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_second_iff hp).trans
        (RankThreeWhitneyModel.zero_mem_secondSheet_iff h p).symm
  obtain ⟨U, hU, hKU, hUsource, hUS⟩ :=
    SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range RankThreeWhitneyModel.firstSheet) hS hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.lower_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_lower_mem_iff hz)
      hfirst
  obtain ⟨V, hV, hKV, -, hVT⟩ :=
    SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range (RankThreeWhitneyModel.secondSheet h)) hT hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.upper_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_upper_mem_iff hz)
      hsecond
  exact
    ⟨U ∩ V, hU.inter hV, fun z hz => ⟨hKU hz, hKV hz⟩, fun _ hz => hUsource hz.1, fun z hz =>
      hUS z hz.1, fun z hz => hVT z hz.2⟩

/-- The image in the manifold of the model lower sheet under a chart. -/
def RankThreeWhitneyModel.nativeFirstSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) : Set M :=
  Φ '' (Set.range firstSheet ∩ Φ.source)

/-- The image in the manifold of the model upper sheet under a chart. -/
def RankThreeWhitneyModel.nativeSecondSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) (h : ℝ) : Set M :=
  Φ '' (Set.range (secondSheet h) ∩ Φ.source)

/-- A compatible chart of a rank-three tubular bigon: a chart in the rank-three model coordinates
which meets the two sheets exactly in the two model sheets. -/
structure TubularBigon.RankThreeCompatibleChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  first_sheet :
    ∀ z ∈ chart.source, chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet
  second_sheet :
    ∀ z ∈ chart.source, chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h)

/-- Restricting a sheet-parametrised chart to the recognition neighbourhood gives a compatible
chart. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.nonempty_rankThreeCompatibleChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) : Nonempty (TubularBigon.RankThreeCompatibleChart tube) := by
  obtain ⟨U, hU, hKU, hUsource, hfirst, hsecond⟩ := c.exists_open_full_sheet_neighborhood hS hT
  have hlocal :
    IsLocalDiffeomorphOn 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E) ∞ c.chart U := fun z =>
    ⟨c.chart, hUsource z.property, fun _ _ => rfl⟩
  let Φ :=
    partialDiffeomorphOfInjectiveLocal hU (c.chart.toPartialEquiv.injOn.mono hUsource)
      hlocal
  have hzero :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      Φ.source :=
    hKU
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset
      (WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzero
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := c.zero_section
        target_subset := ?_
        first_sheet := hfirst
        second_sheet := hsecond }⟩
  intro y hy
  change y ∈ c.chart '' U at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact c.target_subset (c.chart.map_source' (hUsource hz))

/-- The Whitney condition gives a compatible chart: if the two corner intersection signs are
opposite, a rank-three compatible chart exists. -/
theorem TubularBigon.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeCompatibleChart tube) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeCompatibleChart hS hT

/-- In a compatible chart, the image of the model lower sheet is the part of the first sheet in the
target. -/
theorem TubularBigon.RankThreeCompatibleChart.nativeFirstSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    RankThreeWhitneyModel.nativeFirstSheet c.chart = S ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.first_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.first_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ S
    rw [hzy]
    exact hy.1

/-- In a compatible chart, the image of the model upper sheet is the part of the second sheet in the
target. -/
theorem TubularBigon.RankThreeCompatibleChart.nativeSecondSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    RankThreeWhitneyModel.nativeSecondSheet c.chart h = T ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.second_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.second_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ T
    rw [hzy]
    exact hy.1

/-- The graph motion of the rank-three model, transported through a chart: a compactly supported
ambient isotopy of the manifold, supported in the target of the chart, whose time-one map pushes
the image of the model lower sheet off the image of the model upper sheet. -/
theorem RankThreeWhitneyModel.GraphMotion.exists_native_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) J
        RankThreeWhitneyModel.Space M ∞)
    {h : ℝ} (a : RankThreeWhitneyModel.GraphMotion h Φ.source) (hh : 0 < h) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint
                      ((fun y => A (1, y)) '' RankThreeWhitneyModel.nativeFirstSheet Φ)
                      (RankThreeWhitneyModel.nativeSecondSheet Φ h) := by
  have hsource : ∀ t, Set.MapsTo (fun z => a.family (t, z)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    intro z hz
    change a.family (t, z) ∈ Φ.source
    rw [← hd z]
    exact SupportedDiffeomorph.mapsTo_source Φ d.toEquiv a.support_subset hdfix hz
  let A : ℝ × M → M := fun p =>
    SupportedDiffeomorph.extendMap Φ (fun z => a.family (p.1, z)) p.2
  have hcompact : IsCompact (Φ '' a.support) :=
    a.compact_support.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono a.support_subset)
  have htarget : Φ '' a.support ⊆ Φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Φ.map_source' (a.support_subset hz)
  have hfamily :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RankThreeWhitneyModel.Space))
      𝓘(ℝ, RankThreeWhitneyModel.Space) ∞ a.family := by
    exact a.smooth.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  refine
    ⟨Φ '' a.support, hcompact, htarget, A,
      SupportedDiffeomorph.contMDiff_extendFamily Φ hfamily a.compact_support
        a.support_subset a.fixed hsource,
      ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun z => a.family (0, z)) = id := funext a.initial
    change SupportedDiffeomorph.extendMap Φ (fun z => a.family (0, z)) y = y
    rw [hzero]
    exact SupportedDiffeomorph.extendMap_id Φ y
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    refine ⟨SupportedDiffeomorph.extension Φ d a.compact_support a.support_subset hdfix, ?_⟩
    intro y
    change
      SupportedDiffeomorph.extendMap Φ (fun z => a.family (t, z)) y =
        SupportedDiffeomorph.extendMap Φ d y
    exact
      congrArg
        (fun f : RankThreeWhitneyModel.Space → RankThreeWhitneyModel.Space =>
          SupportedDiffeomorph.extendMap Φ f y)
        (funext (fun z => (hd z).symm))
  · intro t y hy
    exact SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (a.fixed t) hy
  · rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨x, hx, hxy⟩ := hy₁
    obtain ⟨z, ⟨⟨p, hp⟩, hz⟩, hzx⟩ := hx
    obtain ⟨w, ⟨⟨q, hq⟩, hw⟩, hwy⟩ := hy₂
    have hleft : A (1, Φ z) = y := by rw [hzx]; exact hxy
    have hcomm : A (1, Φ z) = Φ (a.family (1, z)) :=
      SupportedDiffeomorph.extendMap_chart Φ (fun v => a.family (1, v)) hz
    have heq : a.family (1, z) = w :=
      Φ.toPartialEquiv.injOn (hsource 1 hz) hw (hcomm.symm.trans (hleft.trans hwy.symm))
    apply a.firstSheet_ne_secondSheet hh p q
    rw [hp, hq]
    exact heq

/-- The same cancellation with an explicit compact support inside the target of the chart. -/
theorem RankThreeWhitneyModel.exists_supported_native_bigon_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) {h : ℝ} (hh : 0 < h)
    (hsource : ∀ p ∈ WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ Φ.source) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint ((fun y => A (1, y)) '' nativeFirstSheet Φ)
                      (nativeSecondSheet Φ h) := by
  obtain ⟨a⟩ := nonempty_graphMotion hh Φ.open_source hsource
  exact a.exists_native_cancellation Φ hh

/-- If a bijection is the identity off `U` and carries `S ∩ U` off `T ∩ U`, then the image of `S`
meets `T` exactly in `(S ∩ T) \ U`: the intersections inside `U` have been removed and no
others. -/
theorem SupportedDiffeomorph.image_inter_eq_diff {X : Type*} (d : X ≃ X) {S T U : Set X}
    (hfix : ∀ x ∉ U, d x = x) (hdisjoint : Disjoint (d '' (S ∩ U)) (T ∩ U)) :
    (d '' S) ∩ T = (S ∩ T) \ U := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyT⟩
    have hyU : y ∉ U := by
      intro hy
      have hxU : x ∈ U := by
        by_contra hnot
        have he : x = y := (hfix x hnot).symm.trans hxy
        exact hnot (he.symm ▸ hy)
      exact Set.disjoint_left.mp hdisjoint ⟨x, ⟨hx, hxU⟩, hxy⟩ ⟨hyT, hy⟩
    have he : x = y := d.injective (hxy.trans (hfix y hyU).symm)
    exact ⟨⟨he ▸ hx, hyT⟩, hyU⟩
  · rintro ⟨⟨hyS, hyT⟩, hyU⟩
    exact ⟨⟨y, hyS, hfix y hyU⟩, hyT⟩

/-- Under the same removal, the preimage of the second sheet along a composed parametrisation loses
exactly the preimage of the removed set. -/
theorem SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal {X Y : Type*}
    (d : X ≃ X) (F : Y → X) {T R : Set X} (hfix : ∀ y ∈ (Set.range F ∩ T) \ R, d y = y)
    (himage : (d '' Set.range F) ∩ T = (Set.range F ∩ T) \ R) :
    (d ∘ F) ⁻¹' T = (F ⁻¹' T) \ (F ⁻¹' R) := by
  ext x
  constructor
  · intro hx
    have hy : d (F x) ∈ (d '' Set.range F) ∩ T := ⟨⟨F x, ⟨x, rfl⟩, rfl⟩, hx⟩
    rw [himage] at hy
    have heq : F x = d (F x) := d.injective (hfix _ hy).symm
    change F x ∈ T ∧ F x ∉ R
    rw [heq]
    exact ⟨hy.1.2, hy.2⟩
  · intro hx
    have hy : F x ∈ (Set.range F ∩ T) \ R := ⟨⟨⟨x, rfl⟩, hx.1⟩, hx.2⟩
    change d (F x) ∈ T
    rw [hfix _ hy]
    exact hx.1

/-- A map that is the identity off a closed set does not change the germ of a parametrisation at a
point mapped outside that set. -/
theorem SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {d : X → X} {F : Y → X} {K : Set X}
    (hK : IsClosed K) (hfix : ∀ y ∉ K, d y = y) (hF : Continuous F) {x : Y} (hx : F x ∉ K) :
    (d ∘ F) =ᶠ[𝓝 x] F := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hx)] with y hy
  exact hfix _ hy

/-- In the rank-three model the two sheets meet exactly at the two corners of the bigon, at the
parameters `±1`. -/
theorem RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff {h : ℝ} (hh : 0 < h)
    (p : LowerSheet) (q : UpperSheet) :
    firstSheet p = secondSheet h q ↔ p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  rcases p with ⟨s, u⟩
  rcases q with ⟨t, v⟩
  constructor
  · intro heq
    have hst : s = t := congrArg (fun z : Space => z.1.1) heq
    have ht : 0 = h * (1 - t ^ 2) := congrArg (fun z : Space => z.1.2) heq
    have hu : u = 0 := congrArg (fun z : Space => z.2.1) heq
    have hv : v = 0 := (congrArg (fun z : Space => z.2.2) heq).symm
    have hsq : t ^ 2 = 1 := by
      have hz := (mul_eq_zero.mp ht.symm).resolve_left hh.ne'
      linarith
    have hprod : (t + 1) * (t - 1) = 0 := by nlinarith
    refine ⟨hst, hu, hv, ?_⟩
    rcases mul_eq_zero.mp hprod with hm | hp
    · left
      linarith
    · right
      linarith
  · rintro ⟨hst, hu, hv, ht⟩
    change s = t at hst
    change u = 0 at hu
    change v = 0 at hv
    subst s
    subst u
    subst v
    rcases ht with ht | ht
    · change t = -1 at ht
      subst t
      simp [firstSheet, secondSheet]
    · change t = 1 at ht
      subst t
      simp [firstSheet, secondSheet]

/-- In the target of a compatible chart the two sheets meet exactly at the two corners `a 0` and `a
1` of the bigon. -/
theorem TubularBigon.RankThreeCompatibleChart.intersection_in_target_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    (S ∩ T) ∩ c.chart.target = {a 0, a 1} := by
  have hc0 : c.chart (RankThreeWhitneyModel.firstSheet (-1, 0)) = a 0 := by
    calc
      c.chart (RankThreeWhitneyModel.firstSheet (-1, 0)) = tube.map (-1, 0) :=
        c.zero_section (-1, 0)
      _ = a 0 := by simpa using tube.lower 0 (by simp)
  have hc1 : c.chart (RankThreeWhitneyModel.firstSheet (1, 0)) = a 1 := by
    calc
      c.chart (RankThreeWhitneyModel.firstSheet (1, 0)) = tube.map (1, 0) :=
        c.zero_section (1, 0)
      _ = a 1 := by
        have he := tube.lower 1 (by simp)
        norm_num at he
        exact he
  have hcorner :
    ∀ s : ℝ,
      s = -1 ∨ s = 1 →
        c.chart (RankThreeWhitneyModel.firstSheet (s, 0)) ∈ (S ∩ T) ∩ c.chart.target := by
    intro s hs
    have hb : (s, (0 : ℝ)) ∈ WhitneyPairModel.bigon h := by
      rcases hs with rfl | rfl <;> simp [WhitneyPairModel.bigon]
    have hsource : RankThreeWhitneyModel.firstSheet (s, 0) ∈ c.chart.source :=
      c.source_contains ⟨hb, Metric.mem_closedBall_self c.radius_pos.le⟩
    refine
      ⟨⟨(c.first_sheet _ hsource).mpr ⟨(s, 0), rfl⟩, (c.second_sheet _ hsource).mpr ?_⟩,
        c.chart.map_source' hsource⟩
    refine ⟨(s, 0), ?_⟩
    rcases hs with rfl | rfl <;>
      simp [RankThreeWhitneyModel.firstSheet, RankThreeWhitneyModel.secondSheet]
  ext y
  change y ∈ (S ∩ T) ∩ c.chart.target ↔ y = a 0 ∨ y = a 1
  constructor
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    have hlo : c.chart.symm y ∈ Set.range RankThreeWhitneyModel.firstSheet := by
      apply (c.first_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ S
      rw [hzy]
      exact hy.1.1
    have hhi : c.chart.symm y ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
      apply (c.second_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ T
      rw [hzy]
      exact hy.1.2
    obtain ⟨p, hp⟩ := hlo
    obtain ⟨q, hq⟩ := hhi
    obtain ⟨hst, hu, _, hends⟩ :=
      (RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff tube.height_pos p q).mp
        (hp.trans hq.symm)
    have hpq : p = (q.1, 0) := Prod.ext hst hu
    rw [hpq] at hp
    have hycorner : y = c.chart (RankThreeWhitneyModel.firstSheet (q.1, 0)) :=
      hzy.symm.trans (congrArg c.chart hp.symm)
    rcases hends with hm | hp
    · left
      rw [hm] at hycorner
      exact hycorner.trans hc0
    · right
      rw [hp] at hycorner
      exact hycorner.trans hc1
  · rintro (rfl | rfl)
    · rw [← hc0]
      exact hcorner (-1) (Or.inl rfl)
    · rw [← hc1]
      exact hcorner 1 (Or.inr rfl)

/-- The Whitney cancellation in a compatible chart: a compactly supported ambient isotopy whose
time-one map removes exactly the two intersection points `a 0`, `a 1` from the intersection of
the two sheets. -/
theorem TubularBigon.RankThreeCompatibleChart.exists_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) [T2Space M] :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, hdisjoint⟩ :=
    RankThreeWhitneyModel.exists_supported_native_bigon_cancellation c.chart tube.height_pos
      (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)
  rw [c.nativeFirstSheet_eq, c.nativeSecondSheet_eq] at hdisjoint
  obtain ⟨d, hd⟩ := hdiff 1
  have hdfix : ∀ y ∉ c.chart.target, d y = y := by
    intro y hy
    exact (hd y).symm.trans (hfix 1 y (fun h => hy (hKsource h)))
  have hdeq : (fun y => A (1, y)) = d := funext hd
  have hdisjoint' : Disjoint (d '' (S ∩ c.chart.target)) (T ∩ c.chart.target) := by
    rw [← hdeq]
    exact hdisjoint
  have hinter : (d '' S) ∩ T = (S ∩ T) \ c.chart.target :=
    SupportedDiffeomorph.image_inter_eq_diff d.toEquiv hdfix hdisjoint'
  refine ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, ?_⟩
  rw [hdeq, hinter, ← c.intersection_in_target_eq]
  ext y
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

/-- The cancellation of the previous statement with support disjoint from the remaining intersection
points, so that it can be performed relative to them. -/
theorem TubularBigon.RankThreeCompatibleChart.exists_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKt, A, hA⟩ := c.exists_cancellation
  refine ⟨K, hK, hKt, ?_, A, hA⟩
  apply Set.disjoint_left.mpr
  intro y hyK hy
  have hc : y ∈ (S ∩ T) ∩ c.chart.target := ⟨hy.1, hKt hyK⟩
  rw [c.intersection_in_target_eq] at hc
  exact hy.2 hc

/-- The rank-three Whitney lemma: a tubular bigon whose two corner intersection signs are opposite
gives an ambient isotopy, supported away from the other intersection points, whose time-one map
removes exactly those two points from the intersection of the two sheets. -/
theorem TubularBigon.exists_rankThree_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ tube.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKt, hd, A, hA⟩ := c.exists_relative_cancellation
  exact ⟨K, hK, hKt.trans c.target_subset, hd, A, hA⟩

end
