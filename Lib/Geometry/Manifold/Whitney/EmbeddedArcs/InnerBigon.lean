/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.AnnularExtension

/-!
# Contractions of the standard bigon

`WhitneyPairModel.innerBigonMap h r` contracts the plane towards the interior point `(0, h / 2)` of
the bigon of height `h` by the factor `r`; for `r ≠ 0` it is a diffeomorphism
(`WhitneyPairModel.innerBigonDiffeomorph`) with explicit inverse, and for `0 < r < 1` it carries the
bigon into its interior. The collar `WhitneyPairModel.innerBigonCollar` is the part of the bigon not
covered by the contracted bigon; it is compact, a point of the bigon is carried into it exactly when
the point lies on the boundary, and every open neighbourhood of the boundary contains the collar of
some contraction (`WhitneyPairModel.exists_inner_bigon_collar_in_open`).

These collars are used to glue a filling of the bigon to its boundary map.

## Tags

bigon, collar, contraction
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- The contraction of the plane towards the interior point `(0, h / 2)` of the bigon by the factor
`r`. -/
def WhitneyPairModel.innerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - r) • (0, h / 2) + r • p

/-- The contraction with factor one is the identity. -/
theorem WhitneyPairModel.innerBigonMap_one (h : ℝ) (p : ℝ × ℝ) : innerBigonMap h 1 p = p := by
  simp only [innerBigonMap, sub_self, zero_smul, one_smul, zero_add]

/-- The contraction depends smoothly on the factor and the point. -/
theorem WhitneyPairModel.contDiff_innerBigonMap (h : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => innerBigonMap h z.1 z.2) := by
  unfold innerBigonMap
  fun_prop

/-- For `r ≠ 0`, the contraction is a diffeomorphism of the plane. -/
def WhitneyPairModel.innerBigonDiffeomorph (h r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞
    where
  toEquiv :=
    { toFun := innerBigonMap h r
      invFun := fun p => r⁻¹ • (p - (1 - r) • (0, h / 2))
      left_inv := by
        intro p
        simp only [innerBigonMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
      right_inv := by
        intro p
        simp only [innerBigonMap, smul_smul, mul_inv_cancel₀ hr, one_smul]
        abel }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r)
    apply ContDiff.contMDiff
    unfold innerBigonMap
    fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun p : ℝ × ℝ => r⁻¹ • (p - (1 - r) • (0, h / 2)))
    apply ContDiff.contMDiff
    fun_prop

/-- The differential of the contraction is bijective at every point, for `r ≠ 0`. -/
theorem WhitneyPairModel.bijective_mfderiv_innerBigonMap (h r : ℝ) (hr : r ≠ 0)
    (p : ℝ × ℝ) : Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (innerBigonMap h r) p) :=
  PartialChart.bijective_mfderiv (innerBigonDiffeomorph h r hr).toPartialDiffeomorph
    (Set.mem_univ p)

/-- For `0 < r < 1`, the contraction carries the whole bigon into its interior. -/
theorem WhitneyPairModel.innerBigonMap_mem_interior {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ interior (bigon h) :=
  (convex_bigon hh.le).combo_interior_self_mem_interior (bigon_center_mem_interior hh) hp
    (sub_pos.mpr hr.2) hr.1.le (by ring)

/-- The collar of the bigon cut off by the contraction: the part of the bigon not covered by the
contracted interior. -/
def WhitneyPairModel.innerBigonCollar (h r : ℝ) : Set (ℝ × ℝ) :=
  bigon h \ innerBigonMap h r '' interior (bigon h)

/-- The inverse of the contraction `innerBigonMap h r`. -/
def WhitneyPairModel.inverseInnerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  r⁻¹ • (p - (1 - r) • (0, h / 2))

/-- The inverse contraction with factor one is the identity. -/
theorem WhitneyPairModel.inverseInnerBigonMap_one (h : ℝ) (p : ℝ × ℝ) :
    inverseInnerBigonMap h 1 p = p := by
  simp only [inverseInnerBigonMap, inv_one, sub_self, zero_smul, sub_zero, one_smul]

/-- The inverse contraction is a right inverse of the contraction, for `r ≠ 0`. -/
theorem WhitneyPairModel.inner_inverseInnerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    innerBigonMap h r (inverseInnerBigonMap h r p) = p :=
  (innerBigonDiffeomorph h r hr).apply_symm_apply p

/-- The inverse contraction is continuous in the factor and the point at factor one. -/
theorem WhitneyPairModel.continuousAt_inverseInnerBigonMap (h : ℝ) (p : ℝ × ℝ) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => inverseInnerBigonMap h z.1 z.2) (1, p) := by
  unfold inverseInnerBigonMap
  fun_prop (disch := norm_num)

/-- For `0 < h` and `r ≠ 0`, the collar cut off by the contraction is compact. -/
theorem WhitneyPairModel.isCompact_innerBigonCollar {h r : ℝ} (hh : 0 < h) (hr : r ≠ 0) :
    IsCompact (innerBigonCollar h r) := by
  have ho : IsOpen (innerBigonMap h r '' interior (bigon h)) :=
    (innerBigonDiffeomorph h r hr).toHomeomorph.isOpenMap _ isOpen_interior
  exact (isCompact_bigon hh).inter_right ho.isClosed_compl

/-- For `0 < r < 1`, a point of the bigon is carried into the collar exactly when it lies on the
boundary of the bigon. -/
theorem WhitneyPairModel.innerBigonMap_mem_collar_iff {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ innerBigonCollar h r ↔ p ∈ frontier (bigon h) := by
  rw [frontier, (isClosed_bigon h).closure_eq]
  constructor
  · intro hx
    exact ⟨hp, fun hi => hx.2 (Set.mem_image_of_mem _ hi)⟩
  · intro hx
    refine ⟨interior_subset (innerBigonMap_mem_interior hh hr hp), ?_⟩
    rintro ⟨q, hq, heq⟩
    have hqp : q = p := (innerBigonDiffeomorph h r hr.1.ne').injective heq
    exact hx.2 (hqp ▸ hq)

/-- Any open neighbourhood of the boundary of the bigon contains the collar of some contraction,
which moreover pushes the boundary into the neighbourhood and into the interior of the bigon. -/
theorem WhitneyPairModel.exists_inner_bigon_collar_in_open {h : ℝ} (hh : 0 < h)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hfrontU : frontier (bigon h) ⊆ U) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        innerBigonCollar h r ⊆ U ∧
          Set.MapsTo (innerBigonMap h r) (frontier (bigon h)) (U ∩ interior (bigon h)) := by
  let bad : Set (ℝ × ℝ) := bigon h \ U
  have hbad : IsCompact bad := (isCompact_bigon hh).inter_right hU.isClosed_compl
  have hbadInterior : bad ⊆ interior (bigon h) := by
    intro p hp
    by_contra hi
    apply hp.2
    apply hfrontU
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hi⟩
  have hnearInv : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bad, inverseInnerBigonMap h r p ∈ interior (bigon h) :=
    by
    apply hbad.eventually_forall_of_forall_eventually
    intro p hp
    apply (continuousAt_inverseInnerBigonMap h p).preimage_mem_nhds
    apply isOpen_interior.mem_nhds
    simpa only [inverseInnerBigonMap_one] using hbadInterior hp
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  have hnearFront : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ frontier (bigon h), innerBigonMap h r p ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((contDiff_innerBigonMap h).continuous.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [innerBigonMap_one] using hfrontU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hnearInv.and hnearFront)
  let δ : ℝ := Min.min ε 1 / 2
  have hδpos : 0 < δ := half_pos (lt_min hε zero_lt_one)
  have hδε : δ < ε := by
    dsimp [δ]
    have hm := min_le_left ε 1
    linarith
  have hδ1 : δ < 1 := by
    dsimp [δ]
    have hm := min_le_right ε 1
    linarith
  have hr : 1 - δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hrball : 1 - δ ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : 1 - δ - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδpos]
    exact hδε
  have hretained := hball hrball
  refine ⟨1 - δ, hr, ?_, fun p hp => ⟨hretained.2 p hp, ?_⟩⟩
  · intro p hp
    by_contra hpU
    exact
      hp.2
        ⟨inverseInnerBigonMap h (1 - δ) p, hretained.1 p ⟨hp.1, hpU⟩,
          inner_inverseInnerBigonMap h (1 - δ) hr.1.ne' p⟩
  · exact innerBigonMap_mem_interior hh hr ((mem_frontier_bigon_iff h p).mp hp).1

end
