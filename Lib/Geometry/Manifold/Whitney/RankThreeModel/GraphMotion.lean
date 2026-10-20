/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.FiberRestriction
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SmallPerturbation
import Lib.Geometry.Manifold.Whitney.FrameField.RankThreeFrame
import Lib.Geometry.Manifold.Whitney.FrameField.SheetNormal

/-!
# Graph motions of the Whitney pair model

In the model `WhitneyPairModel.Space` of a pair of sheets meeting along the boundary of the
planar bigon `{(x, y) | 0 ≤ y, h x² + y ≤ h}`, the lower sheet is pushed across the bigon by a
vertical graph motion. Given an open neighbourhood `U` of the bigon, a smooth compactly supported
height function `B` lying strictly above the parabolic arc `y = h (1 - x²)` on `[-1, 1]` and whose
vertical trace stays in `U` is built from a bump function on a slightly enlarged bigon
(`exists_supported_graph_height`), together with a cut-off tracking it
(`exists_graph_motion_cutoff`). Composing finitely many small translations by the cut-off weight
(`graphStep`) gives a compactly supported smooth ambient isotopy preserving the horizontal and
normal coordinates which carries the lower sheet onto the graph of `B`
(`GraphMotionData.nonempty_graphMotion`); after it the two sheets are disjoint
(`GraphMotion.firstSheet_ne_secondSheet`).

This is the model isotopy of the Whitney trick: Milnor, *Lectures on the h-cobordism theorem*,
§6 (the push across the Whitney disc in the standard model).

## Tags

Whitney trick, isotopy, bump function
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


end
