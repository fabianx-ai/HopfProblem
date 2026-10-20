/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.LocalReplacement
import Lib.Geometry.Manifold.Morse.Rearrangement.HeightCoordinates
import Lib.Geometry.Manifold.Morse.Connection.CylinderHolonomy
import Lib.Geometry.Manifold.Morse.Connection.PhaseCylinder
import Lib.Geometry.Manifold.Morse.Connection.Suspension
import Lib.Geometry.Manifold.Morse.Connection.TimeChange
import Lib.Geometry.Manifold.Morse.Connection.TransverseBlocks
import Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts

/-!
# Phase clocks and the phase-corrected cylinder

A *phase* `v : E → ℝ` (smooth, `v 0 = 0`) is realised by a time change of the flow supported in
a flow cylinder:

* `exists_small_supported_scalar_germ`, `exists_bounded_step_profile`,
  `exists_supported_phase_clock`: a diffeomorphism `D (s, x) = (s + τ s * g x, x)` of `ℝ × E`
  with `g =ᶠ[𝓝 0] v` compactly supported and `τ` a smooth step from `0` to `1` on `[1/3, 2/3]`;
* `phaseConjugatingDiffeomorph`, `phaseClockFlow_base`, `phaseClockField_base_zero`,
  `phaseClockField_time_derivative`, `phaseClockField_time_positive`,
  `phaseClockField_eq_vertical_of_translation_germ`, `exists_compact_phase_field_support`,
  `PhaseFlowCoordinates`, `exists_compact_phase_flow`: the suspended flow of `D` on `E × ℝ` is
  vertical outside a compact set and satisfies `F t (z, 0) = (z, t + g z)` for `t ≥ 2/3`;
* `partialChartField_vertical_factor`, `exists_native_positive_cylinder_rescaling`,
  `exists_native_cylinder_conjugacy`, `exists_native_phase_realization`: a positive rescaling of
  `V` whose flow `G` satisfies `G t (Φ (z, 0)) = Φ (z, t + g z)` for `t ≥ 2/3`, with a new
  vertical chart `Ω` agreeing with `Φ` below and with `Φ ∘ (id, · + g)` above;
* `exists_native_matched_phase_cylinder`, `exists_unique_phase_corrected_cylinder`: combining
  block holonomy and phase realisation, the corrected chart `Ξ` satisfies
  `Ξ (u, t) = Φ (Q u, t + v₀ u)` for `t ≤ -1` and
  `Ξ (u, t) = Φ (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))` for `t ≥ 2`, and the connecting
  orbit stays unique.

cf. Milnor, *Lectures on the h-cobordism theorem*, §5 (the field is altered near the trajectory
so that the coordinate systems at its two ends match along it).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Phase clocks -/

/-- A small supported scalar germ exists. -/
theorem FlowTimeChange.exists_small_supported_scalar_germ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ}
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0) {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (K : Set E) (g : E → ℝ),
      IsCompact K ∧
        K ⊆ U ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ K ∧ g =ᶠ[𝓝 0] v ∧ g 0 = 0 ∧ ∀ x, |g x| < ε := by
  have hnear : ∀ᶠ x in 𝓝 (0 : E), x ∈ U ∧ |v x| < ε := by
    have hp : |v 0| < ε := by simpa only [hv0, abs_zero] using hε
    have hmem : ∀ᶠ x in 𝓝 (0 : E), x ∈ U := hU.mem_nhds h0U
    exact hmem.and (hv.continuous.abs.continuousAt (eventually_lt_nhds hp))
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff.mp hnear
  let β : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let K := Metric.closedBall (0 : E) β.rOut
  let g (x : E) := β x * v x
  have hKsmall {x : E} (hx : x ∈ K) : Dist.dist x 0 < r := by
    have hh : Dist.dist x 0 ≤ r / 2 := hx
    linarith
  have hKU : K ⊆ U := fun _ hx => (hrsub (hKsmall hx)).1
  have hsupp : tsupport g ⊆ K := by
    have hh := tsupport_mul_subset_left (f := fun x : E => β x) (g := v)
    rw [β.tsupport_eq] at hh
    exact hh
  have hgerm : g =ᶠ[𝓝 0] v := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) β.rIn_pos] with x hx
    change β x * v x = v x
    rw [β.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_mul]
  refine
    ⟨K, g, ProperSpace.isCompact_closedBall _ _, hKU, β.contDiff.mul hv, hsupp, hgerm,
      hgerm.eq_of_nhds.trans hv0, ?_⟩
  intro x
  by_cases hx : β x = 0
  · simpa only [g, hx, MulZeroClass.zero_mul, abs_zero] using hε
  · have hxin : x ∈ K := by
      change x ∈ Metric.closedBall (0 : E) β.rOut
      rw [← β.tsupport_eq]
      exact subset_tsupport β hx
    have hvx : |v x| < ε := (hrsub (hKsmall hxin)).2
    change |β x * v x| < ε
    rw [abs_mul, abs_of_nonneg β.nonneg]
    exact (mul_le_of_le_one_left (abs_nonneg (v x)) β.le_one).trans_lt hvx

/-- A bounded step profile exists. -/
theorem FlowTimeChange.exists_bounded_step_profile :
    ∃ (τ : ℝ → ℝ) (L : ℝ),
      ContDiff ℝ ∞ τ ∧
        0 < L ∧
          (∀ t, τ t ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ t, t ≤ 1 / 3 → τ t = 0) ∧
              (∀ t, 2 / 3 ≤ t → τ t = 1) ∧
                (∀ t, t ∉ Set.Icc (1 / 3 : ℝ) (2 / 3) → deriv τ t = 0) ∧ ∀ t, |deriv τ t| ≤ L := by
  let τ : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hτ : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hzero (t : ℝ) (ht : t ≤ 1 / 3) : τ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hone (t : ℝ) (ht : 2 / 3 ≤ t) : τ t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hout (t : ℝ) (ht : t ∉ Set.Icc (1 / 3 : ℝ) (2 / 3)) : deriv τ t = 0 := by
    by_cases hlo : t < 1 / 3
    · have hg : τ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventually_lt_nhds hlo] with s hs
        exact hzero s hs.le
      rw [hg.deriv_eq]
      exact deriv_const _ _
    · have hhi : 2 / 3 < t := by
        by_contra hn
        exact ht ⟨le_of_not_gt hlo, le_of_not_gt hn⟩
      have hg : τ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
        filter_upwards [eventually_gt_nhds hhi] with s hs
        exact hone s hs.le
      rw [hg.deriv_eq]
      exact deriv_const _ _
  have hcomp : HasCompactSupport (deriv τ) :=
    HasCompactSupport.intro
      (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (1 / 3 : ℝ) (2 / 3))) hout
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous (hτ.continuous_deriv (by simp))
  let L : ℝ := Max.max C 0 + 1
  refine ⟨τ, L, hτ, by dsimp [L]; positivity, ?_, hzero, hone, hout, ?_⟩
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro t
    have hh : |deriv τ t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t
    exact hh.trans (by dsimp [L]; linarith [le_max_left C 0])

/-- A supported phase clock exists. -/
theorem FlowTimeChange.exists_supported_phase_clock {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ (K : Set E) (g : E → ℝ) (τ : ℝ → ℝ) (D :
      Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞),
      IsCompact K ∧
        K ⊆ U ∧
          ContDiff ℝ ∞ g ∧
            tsupport g ⊆ K ∧
              g =ᶠ[𝓝 0] v ∧
                g 0 = 0 ∧
                  (∀ x, |g x| < 1 / 12) ∧
                    ContDiff ℝ ∞ τ ∧
                      (∀ t, τ t ∈ Set.Icc (0 : ℝ) 1) ∧
                        (∀ p, D p = (p.1 + τ p.1 * g p.2, p.2)) ∧
                          (∀ s, D (s, 0) = (s, 0)) ∧
                            (∀ p, p.1 ≤ 1 / 3 → D p = p) ∧
                              (∀ p, 2 / 3 ≤ p.1 → D p = (p.1 + g p.2, p.2)) ∧
                                ∀ p, 1 / 2 < fderiv ℝ (fun q => (D q).1) p (1, 0) := by
  obtain ⟨τ, L, hτ, hL, hrange, hleft, hright, -, hder⟩ := exists_bounded_step_profile
  let ε : ℝ := Min.min (1 / 12) (1 / (2 * L))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨K, g, hK, hKU, hg, hsupp, hgerm, hg0, hsmall⟩ :=
    exists_small_supported_scalar_germ hv hv0 hU h0U hε
  let u (p : ℝ × E) := τ p.1 * g p.2
  have hu : ContDiff ℝ ∞ u := (hτ.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hbound (p : ℝ × E) : |u p| ≤ ε := by
    change |τ p.1 * g p.2| ≤ ε
    rw [abs_mul, abs_of_nonneg (hrange p.1).1]
    exact (mul_le_of_le_one_left (abs_nonneg (g p.2)) (hrange p.1).2).trans (hsmall p.2).le
  have hrate (p : ℝ × E) :
    fderiv ℝ (RegularHeightCoordinates.displacedHeight u) p (1, 0) =
      1 + deriv τ p.1 * g p.2 := by
    have ha :=
      (RegularHeightCoordinates.scalar_derivative
          (RegularHeightCoordinates.contDiff_displacedHeight hu) p.1 p.2).deriv
    have hb :=
      ((hasDerivAt_id p.1).add
          ((hτ.differentiable (by simp) p.1).hasDerivAt.mul_const (g p.2))).deriv
    exact ha.symm.trans hb
  have hsmall' (p : ℝ × E) : |deriv τ p.1 * g p.2| < 1 / 2 := by
    rw [abs_mul]
    calc
      |deriv τ p.1| * |g p.2| ≤ L * |g p.2| := mul_le_mul_of_nonneg_right (hder _) (abs_nonneg _)
      _ < L * ε := (mul_lt_mul_of_pos_left (hsmall _) hL)
      _ ≤ L * (1 / (2 * L)) := (mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le)
      _ = 1 / 2 := by field_simp
  have hpositive (p : ℝ × E) :
    1 / 2 < fderiv ℝ (RegularHeightCoordinates.displacedHeight u) p (1, 0) := by
    rw [hrate]
    linarith [(abs_lt.mp (hsmall' p)).1]
  have hpos (p : ℝ × E) :
    0 < fderiv ℝ (RegularHeightCoordinates.displacedHeight u) p (1, 0) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans (hpositive p)
  have hF := RegularHeightCoordinates.contDiff_displacedHeight hu
  have hlocal :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞
      (RegularHeightCoordinates.heightMap
        (RegularHeightCoordinates.displacedHeight u)) :=
    fun p => RegularHeightCoordinates.heightMap_localDiffeomorph hF (hpos p).ne'
  let D :=
    hlocal.diffeomorphOfBijective
      ⟨RegularHeightCoordinates.heightMap_injective_of_positive hF hpos,
        RegularHeightCoordinates.heightMap_surjective_of_bounded hu.continuous ε hε.le
          hbound⟩
  have hD (p : ℝ × E) : D p = (p.1 + τ p.1 * g p.2, p.2) := rfl
  refine
    ⟨K, g, τ, D, hK, hKU, hg, hsupp, hgerm, hg0, fun x => (hsmall x).trans_le (min_le_left _ _),
      hτ, hrange, hD, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hD, hg0, MulZeroClass.mul_zero, add_zero]
  · intro p hp
    rw [hD, hleft p.1 hp, MulZeroClass.zero_mul, add_zero]
  · intro p hp
    rw [hD, hright p.1 hp, one_mul]
  · exact hpositive

/-- The phase-conjugating diffeomorphism. -/
def FlowTimeChange.phaseConjugatingDiffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) :
    Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
  ((ContinuousLinearEquiv.prodComm ℝ E ℝ).toDiffeomorph.trans D).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ E).toDiffeomorph

/-- The phase clock flow's base. -/
theorem FlowTimeChange.phaseClockFlow_base {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hbase : ∀ p, (D p).2 = p.2) (p : E × ℝ) (t : ℝ) :
    (FlowSuspension.suspensionFlow (phaseConjugatingDiffeomorph D) t p).1 = p.1 := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have hh := congrArg (fun w : E × ℝ => w.1) (Q.apply_symm_apply p)
  change (D (z.2, z.1)).2 = p.1 at hh
  rw [hbase] at hh
  change (D (z.2 + t, z.1)).2 = p.1
  rw [hbase]
  exact hh

/-- The phase clock field's base at zero. -/
theorem FlowTimeChange.phaseClockField_base_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hbase : ∀ p, (D p).2 = p.2) (p : E × ℝ) :
    (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).1 = 0 := by
  have hd :
    HasDerivAt
      (fun t => (FlowSuspension.suspensionFlow (phaseConjugatingDiffeomorph D) t p).1)
      (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).1 0 :=
    (FlowSuspension.hasDerivAt_suspensionFlow_zero (phaseConjugatingDiffeomorph D) p).fst
  have heq :
    (fun t => (FlowSuspension.suspensionFlow (phaseConjugatingDiffeomorph D) t p).1) =
      (fun _ => p.1) :=
    funext (phaseClockFlow_base D hbase p)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 p.1)

/-- The phase clock field's time derivative. -/
theorem FlowTimeChange.phaseClockField_time_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) (p : E × ℝ) :
    (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).2 =
      fderiv ℝ (fun q => (D q).1) ((phaseConjugatingDiffeomorph D).symm p).swap (1, 0) := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have hd :
    HasDerivAt (fun t => (FlowSuspension.suspensionFlow Q t p).2)
      (FlowSuspension.suspensionField Q p).2 0 :=
    (FlowSuspension.hasDerivAt_suspensionFlow_zero Q p).snd
  have hD : ContDiff ℝ ∞ (fun q : ℝ × E => (D q).1) := D.contMDiff.contDiff.fst
  have hc : HasDerivAt (fun t : ℝ => (z.2 + t, z.1)) ((1 : ℝ), (0 : E)) 0 :=
    ((hasDerivAt_id 0).const_add z.2).prodMk (hasDerivAt_const 0 z.1)
  have hi := (hD.differentiable (by simp) (z.2 + 0, z.1)).hasFDerivAt.comp_hasDerivAt 0 hc
  simp only [add_zero] at hi
  change
    HasDerivAt (fun t => (D (z.2 + t, z.1)).1) (FlowSuspension.suspensionField Q p).2
      0 at hd
  exact hd.unique hi

/-- The phase clock field's time component is positive. -/
theorem FlowTimeChange.phaseClockField_time_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hpos : ∀ q, 1 / 2 < fderiv ℝ (fun p => (D p).1) q (1, 0)) (p : E × ℝ) :
    1 / 2 < (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).2 := by
  rw [phaseClockField_time_derivative]
  exact hpos _

/-- The phase clock field is vertical for a translation germ. -/
theorem FlowTimeChange.phaseClockField_eq_vertical_of_translation_germ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) (p : E × ℝ) {h : ℝ}
    (hgerm :
      ∀ᶠ s in 𝓝 ((phaseConjugatingDiffeomorph D).symm p).2,
        D (s, ((phaseConjugatingDiffeomorph D).symm p).1) =
          (s + h, ((phaseConjugatingDiffeomorph D).symm p).1)) :
    FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p = (0, 1) := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have ht : Filter.Tendsto (fun t : ℝ => z.2 + t) (𝓝 0) (𝓝 z.2) := by
    have hc : Continuous (fun t : ℝ => z.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq :
    (fun t => FlowSuspension.suspensionFlow Q t p) =ᶠ[𝓝 0] (fun t => (z.1, z.2 + t + h)) :=
    by
    filter_upwards [ht.eventually hgerm] with t hts
    change ((D (z.2 + t, z.1)).2, (D (z.2 + t, z.1)).1) = _
    rw [hts]
  have hd :=
    (FlowSuspension.hasDerivAt_suspensionFlow_zero Q p).congr_of_eventuallyEq heq.symm
  exact
    hd.unique
      ((hasDerivAt_const 0 z.1).prodMk (((hasDerivAt_id (0 : ℝ)).const_add z.2).add_const h))

/-- A compact phase field support exists. -/
theorem FlowTimeChange.exists_compact_phase_field_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) {g : E → ℝ} {τ : ℝ → ℝ}
    {K : Set E} (hK : IsCompact K) (hsupp : tsupport g ⊆ K) (hsmall : ∀ x, |g x| < 1 / 12)
    (hrange : ∀ t, τ t ∈ Set.Icc (0 : ℝ) 1) (hD : ∀ p, D p = (p.1 + τ p.1 * g p.2, p.2))
    (hleft : ∀ p, p.1 ≤ 1 / 3 → D p = p) (hright : ∀ p, 2 / 3 ≤ p.1 → D p = (p.1 + g p.2, p.2)) :
    ∃ C : Set (E × ℝ),
      IsCompact C ∧
        C ⊆ K ×ˢ Set.Ioo (0 : ℝ) 1 ∧
          ∀ p ∉ C,
            FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p = (0, 1) := by
  let Q := phaseConjugatingDiffeomorph D
  let C := Q '' (K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3))
  have hC : IsCompact C := (hK.prod CompactIccSpace.isCompact_Icc).image Q.continuous
  have hsub : C ⊆ K ×ˢ Set.Ioo (0 : ℝ) 1 := by
    rintro p ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    change ((D (t, z)).2, (D (t, z)).1) ∈ K ×ˢ Set.Ioo (0 : ℝ) 1
    rw [hD]
    have hamp : |τ t * g z| < 1 / 12 := by
      rw [abs_mul, abs_of_nonneg (hrange t).1]
      exact (mul_le_of_le_one_left (abs_nonneg (g z)) (hrange t).2).trans_lt (hsmall z)
    refine ⟨hz, ?_, ?_⟩ <;> linarith [(abs_lt.mp hamp).1, (abs_lt.mp hamp).2, ht.1, ht.2]
  refine ⟨C, hC, hsub, ?_⟩
  intro p hp
  let z := Q.symm p
  have hz : z ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) := fun hh => hp ⟨z, hh, Q.apply_symm_apply p⟩
  by_cases hbase : z.1 ∈ K
  · have htime : z.2 ∉ Set.Icc (1 / 3 : ℝ) (2 / 3) := fun ht => hz ⟨hbase, ht⟩
    by_cases hlo : z.2 < 1 / 3
    · apply phaseClockField_eq_vertical_of_translation_germ D p (h := 0)
      filter_upwards [eventually_lt_nhds hlo] with s hs
      simpa only [add_zero] using hleft (s, z.1) hs.le
    · have hhi : 2 / 3 < z.2 := by
        by_contra hn
        exact htime ⟨le_of_not_gt hlo, le_of_not_gt hn⟩
      apply phaseClockField_eq_vertical_of_translation_germ D p (h := g z.1)
      filter_upwards [eventually_gt_nhds hhi] with s hs
      exact hright (s, z.1) hs.le
  · have hg : g z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hbase (hsupp h))
    apply phaseClockField_eq_vertical_of_translation_germ D p (h := 0)
    apply Filter.Eventually.of_forall
    intro s
    rw [hD, hg, MulZeroClass.mul_zero]

/-! ### Phase flow coordinates -/

/-- Coordinates for the phase flow. -/
structure FlowTimeChange.PhaseFlowCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : E → ℝ) (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = FlowSuspension.suspensionField chart
  flow_eq : F = FlowSuspension.suspensionFlow chart
  base : ∀ p, (chart p).1 = p.1
  lower : ∀ p, p.2 ≤ 1 / 3 → chart p = p
  upper : ∀ p, 2 / 3 ≤ p.2 → chart p = (p.1, p.2 + g p.1)
  axis : ∀ t : ℝ, chart (0, t) = (0, t)

/-- A compact phase flow exists. -/
theorem FlowTimeChange.exists_compact_phase_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ (K : Set E) (C : Set (E × ℝ)) (g : E → ℝ) (W : E × ℝ → E × ℝ) (F : Flow ℝ (E × ℝ)),
      IsCompact K ∧
        K ⊆ U ∧
          IsCompact C ∧
            C ⊆ K ×ˢ Set.Ioo (0 : ℝ) 1 ∧
              ContDiff ℝ ∞ g ∧
                tsupport g ⊆ K ∧
                  g =ᶠ[𝓝 0] v ∧
                    g 0 = 0 ∧
                      ContDiff ℝ ∞ W ∧
                        (∀ p, (W p).1 = 0) ∧
                          (∀ p, 1 / 2 < (W p).2) ∧
                            (∀ p ∉ C, W p = (0, 1)) ∧
                              (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
                                (∀ p t, (F t p).1 = p.1) ∧
                                  (∀ z t, t ≤ 1 / 3 → F t (z, 0) = (z, t)) ∧
                                    (∀ z t, 2 / 3 ≤ t → F t (z, 0) = (z, t + g z)) ∧
                                      (∀ s t : ℝ, F t (0, s) = (0, s + t)) ∧
                                        Nonempty (PhaseFlowCoordinates g W F) := by
  obtain
    ⟨K, g, τ, D, hK, hKU, hg, hsupp, hgerm, hg0, hsmall, hτ, hrange, hD, haxis, hleft, hright,
      hpos⟩ :=
    exists_supported_phase_clock hv hv0 hU h0U
  let Q := phaseConjugatingDiffeomorph D
  let W := FlowSuspension.suspensionField Q
  let F := FlowSuspension.suspensionFlow Q
  have hbase (p : ℝ × E) : (D p).2 = p.2 := by rw [hD]
  obtain ⟨C, hC, hCsub, hoff⟩ :=
    exists_compact_phase_field_support D hK hsupp hsmall hrange hD hleft hright
  have hinitial (z : E) : Q (z, 0) = (z, 0) := by
    change ((D (0, z)).2, (D (0, z)).1) = (z, 0)
    rw [hleft (0, z) (by norm_num)]
  have hinverse (z : E) : Q.symm (z, 0) = (z, 0) := by
    have hh := Q.symm_apply_apply (z, 0)
    rw [hinitial] at hh
    exact hh
  have hfromzero (z : E) (t : ℝ) : F t (z, 0) = ((D (t, z)).2, (D (t, z)).1) := by
    change Q ((Q.symm (z, 0)).1, (Q.symm (z, 0)).2 + t) = _
    rw [hinverse, zero_add]
    rfl
  have hcoords : PhaseFlowCoordinates g W F := by
    refine ⟨Q, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro p
      change (D (p.2, p.1)).2 = p.1
      rw [hD]
    · intro p hp
      change ((D (p.2, p.1)).2, (D (p.2, p.1)).1) = p
      rw [hleft (p.2, p.1) hp]
    · intro p hp
      change ((D (p.2, p.1)).2, (D (p.2, p.1)).1) = (p.1, p.2 + g p.1)
      rw [hright (p.2, p.1) hp]
    · intro t
      change ((D (t, 0)).2, (D (t, 0)).1) = (0, t)
      rw [haxis]
  refine
    ⟨K, C, g, W, F, hK, hKU, hC, hCsub, hg, hsupp, hgerm, hg0,
      FlowSuspension.contDiff_suspensionField Q, phaseClockField_base_zero D hbase,
      phaseClockField_time_positive D hpos, hoff,
      FlowSuspension.hasDerivAt_suspensionFlow Q, phaseClockFlow_base D hbase, ?_, ?_, ?_,
      ⟨hcoords⟩⟩
  · intro z t ht
    rw [hfromzero, hleft (t, z) ht]
  · intro z t ht
    rw [hfromzero, hright (t, z) ht]
  · intro s t
    have hQaxis (r : ℝ) : Q (0, r) = (0, r) := by
      change ((D (r, 0)).2, (D (r, 0)).1) = (0, r)
      rw [haxis]
    have hiaxis : Q.symm (0, s) = (0, s) := by
      have hh := Q.symm_apply_apply (0, s)
      rw [hQaxis] at hh
      exact hh
    change Q ((Q.symm (0, s)).1, (Q.symm (0, s)).2 + t) = _
    rw [hiaxis, hQaxis]

/-- The partial chart field's vertical factor. -/
theorem FlowTimeChange.partialChartField_vertical_factor {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) (W : (E × ℝ) → E × ℝ)
    (hbase : ∀ p, (W p).1 = 0) (x : M) :
    FlowConstruction.partialChartField Φ.symm W x =
      (W (Φ.symm x)).2 •
        FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x := by
  have hw (p : E × ℝ) : W p = (W p).2 • ((0 : E), (1 : ℝ)) := by
    apply Prod.ext
    · simpa only [Prod.smul_fst, smul_zero] using hbase p
    · simp only [Prod.smul_snd, smul_eq_mul, mul_one]
  unfold FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, VectorField.mpullback_apply]
  conv_lhs => rw [hw]
  rw [map_smul, map_smul]

/-- A native positive cylinder rescaling exists. -/
theorem FlowTimeChange.exists_native_positive_cylinder_rescaling {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace M] [ChartedSpace B M] [T2Space M] [IsManifold 𝓘(ℝ, B) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (W : (E × ℝ) → E × ℝ) (hW : ContDiff ℝ ∞ W) (hbase : ∀ p, (W p).1 = 0)
    (hpos : ∀ p, 0 < (W p).2) {C : Set (E × ℝ)} (hC : IsCompact C) (hCsource : C ⊆ Φ.source)
    (hfix : ∀ p ∉ C, W p = (0, 1)) :
    ∃ ρ : M → ℝ,
      ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ x, 0 < ρ x) ∧
          ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
              (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
            (∀ x ∈ Φ.target, ρ x • V x = FlowConstruction.partialChartField Φ.symm W x) ∧
              (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
                (∀ (f : M → ℝ) x,
                    mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (ρ x • V x) < 0) ∧
                  ∀ x ∉ Φ '' C, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let w (p : E × ℝ) := (W p).2
  let ρ := LocalFunctionReplacement.replace Φ (fun _ : M => 1) w
  have hw : ContDiff ℝ ∞ w := hW.snd
  have hwfix (p : E × ℝ) (hp : p ∉ C) : w p = 1 := by
    change (W p).2 = 1
    rw [hfix p hp]
  have hρ : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ ρ :=
    LocalFunctionReplacement.contMDiff_replace Φ contMDiff_const hw hC hCsource
      (fun _ _ => rfl) hwfix
  have hρpos (x : M) : 0 < ρ x := by
    change 0 < LocalFunctionReplacement.replace Φ (fun _ : M => 1) w x
    by_cases hx : x ∈ Φ.target
    · rw [LocalFunctionReplacement.replace_of_mem Φ (fun _ => 1) w hx]
      exact hpos _
    · rw [LocalFunctionReplacement.replace_of_notMem Φ (fun _ => 1) w hx]
      exact zero_lt_one
  refine ⟨ρ, hρ, hρpos, hρ.smul_section hV, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change LocalFunctionReplacement.replace Φ (fun _ : M => 1) w x • V x = _
    rw [LocalFunctionReplacement.replace_of_mem Φ (fun _ => 1) w hx, hmodel x hx,
      partialChartField_vertical_factor Φ W hbase x]
  · intro x
    exact smul_eq_zero.trans (or_iff_right (hρpos x).ne')
  · intro f x hx
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hρpos x) hx
  · intro x hx
    exact
      LocalFunctionReplacement.replace_germ_off_support Φ hC hCsource (fun _ _ => rfl)
        hwfix hx

/-- A native cylinder conjugacy exists. -/
theorem FlowSuspension.exists_native_cylinder_conjugacy {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ)
    (D : Diffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, Z × ℝ) (Z × ℝ) (Z × ℝ) ∞)
    (hbase : ∀ p, (D p).1 ∈ U ↔ p.1 ∈ U) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel :
      ∀ y ∈ Φ.target,
        V y = FlowConstruction.partialChartField Φ.symm (suspensionField D) y) :
    ∃ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞,
      Ω.source = U ×ˢ Set.univ ∧
        Ω.target = Φ.target ∧
          (∀ p, Ω p = Φ (D p)) ∧
            ∀ y ∈ Ω.target,
              V y = FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y :=
  by
  let Ω := D.toPartialDiffeomorph.trans Φ
  have hΩsource : Ω.source = U ×ˢ Set.univ := by
    ext p
    change (p ∈ (Set.univ : Set (Z × ℝ)) ∧ D p ∈ Φ.source) ↔ p ∈ U ×ˢ Set.univ
    rw [hsource]
    simp only [Set.mem_univ, true_and, Set.mem_prod, and_true, hbase]
  have hΩtarget : Ω.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (Set.univ : Set (Z × ℝ))) ↔ y ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hpush (p : Z × ℝ) (_ : p ∈ D.toPartialDiffeomorph.source) :
    fderiv ℝ D.toPartialDiffeomorph p (0, 1) = suspensionField D (D p) := by
    simp only [suspensionField, D.symm_apply_apply]
    rfl
  refine ⟨Ω, hΩsource, hΩtarget, fun _ => rfl, ?_⟩
  intro y hy
  rw [hmodel y (hΩtarget ▸ hy)]
  exact
    (MorseCancellation.partialChartField_of_model_conjugacy D.toPartialDiffeomorph Φ
        (fun _ : Z × ℝ => (0, 1)) (suspensionField D) hpush hy).symm

/-- A native phase realization exists. -/
theorem FlowTimeChange.exists_native_phase_realization {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    [IsManifold 𝓘(ℝ, B) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {U : Set E} (hU : IsOpen U)
    (h0U : (0 : E) ∈ U) (hsource : Φ.source = U ×ˢ Set.univ)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V) {v : E → ℝ}
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0) :
    ∃ (N : Set M) (g : E → ℝ) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧
        N ⊆ Φ.target ∩ Φ '' (U ×ˢ Set.Ioo (0 : ℝ) 1) ∧
          ContDiff ℝ ∞ g ∧
            g =ᶠ[𝓝 0] v ∧
              g 0 = 0 ∧
                ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
                    (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
                  (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
                    (∀ x, V' x = 0 ↔ V x = 0) ∧
                      (∀ (f : M → ℝ) x,
                          mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
                        (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                          (∀ x,
                              Set.range (fun t => G t x) = Set.range (fun t => H t x) ∧
                                (∀ p,
                                    Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) ↔
                                      Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p)) ∧
                                  ∀ p,
                                    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
                                      Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p)) ∧
                            (∀ z ∈ U, ∀ t : ℝ, t ≤ 1 / 3 → G t (Φ (z, 0)) = Φ (z, t)) ∧
                              (∀ z ∈ U, ∀ t : ℝ, 2 / 3 ≤ t → G t (Φ (z, 0)) = Φ (z, t + g z)) ∧
                                (∀ s t : ℝ, G t (Φ (0, s)) = Φ (0, s + t)) ∧
                                  ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
                                    Ω.source = U ×ˢ Set.univ ∧
                                      Ω.target = Φ.target ∧
                                        (∀ y ∈ Ω.target,
                                            V' y =
                                              FlowConstruction.partialChartField Ω.symm
                                                (fun _ : E × ℝ => (0, 1)) y) ∧
                                          (∀ p, p.2 ≤ 1 / 3 → Ω p = Φ p) ∧
                                            (∀ p, 2 / 3 ≤ p.2 → Ω p = Φ (p.1, p.2 + g p.1)) ∧
                                              (∀ t : ℝ, Ω (0, t) = Φ (0, t)) ∧
                                                ∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0)) := by
  obtain
    ⟨K, C, g, W, F, -, hKU, hC, hCsub, hg, -, hgerm, hg0, hW, hWbase, hWpos, hWfix, hF, hFbase,
      hleft, hright, haxis, ⟨Cdata⟩⟩ :=
    exists_compact_phase_flow hv hv0 hU h0U
  have hCsource : C ⊆ Φ.source := by
    rw [hsource]
    exact fun p hp => ⟨hKU (hCsub hp).1, Set.mem_univ _⟩
  obtain ⟨ρ, hρ, hρpos, hV', hnew, hzeros, hneg, hρgerm⟩ :=
    exists_native_positive_cylinder_rescaling Φ V hV hmodel W hW hWbase
      (fun p => (by norm_num : (0 : ℝ) < 1 / 2).trans (hWpos p)) hC hCsource hWfix
  let V' : (x : M) → TangentSpace 𝓘(ℝ, B) x := fun x => ρ x • V x
  let N := Φ '' C
  have hN : IsCompact N :=
    hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hNsub : N ⊆ Φ.target ∩ Φ '' (U ×ˢ Set.Ioo (0 : ℝ) 1) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨Φ.map_source' (hCsource hp), ⟨p, ⟨hKU (hCsub hp).1, (hCsub hp).2⟩, rfl⟩⟩
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : F t p ∈ Φ.source := by
    rw [hsource] at hp ⊢
    exact ⟨(hFbase p t) ▸ hp.1, Set.mem_univ _⟩
  have hfull (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : G t (Φ p) = Φ (F t p) :=
    FlowSuspension.native_chart_flow_all_time Φ hV'₁ G hG F W hF hnew (hstay p hp) t
  have hnew' (y : M) (hy : y ∈ Φ.target) :
    V' y =
      FlowConstruction.partialChartField Φ.symm
        (FlowSuspension.suspensionField Cdata.chart) y := by
    exact
      (hnew y hy).trans
        (congrArg (fun w => FlowConstruction.partialChartField Φ.symm w y) Cdata.field_eq)
  obtain ⟨Ω, hΩsource, hΩtarget, hΩmap, hΩfield⟩ :=
    FlowSuspension.exists_native_cylinder_conjugacy Φ hsource Cdata.chart
      (fun p => by rw [Cdata.base]) V' hnew'
  have hΩlower (p : E × ℝ) (hp : p.2 ≤ 1 / 3) : Ω p = Φ p := by rw [hΩmap, Cdata.lower p hp]
  have hΩupper (p : E × ℝ) (hp : 2 / 3 ≤ p.2) : Ω p = Φ (p.1, p.2 + g p.1) := by
    rw [hΩmap, Cdata.upper p hp]
  have hΩaxis (t : ℝ) : Ω (0, t) = Φ (0, t) := by rw [hΩmap, Cdata.axis]
  have hΩflow (z : E) (hz : z ∈ U) (t : ℝ) : Ω (z, t) = G t (Φ (z, 0)) := by
    have h0 : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    have hC0 : Cdata.chart (z, (0 : ℝ)) = (z, 0) := Cdata.lower _ (by norm_num)
    have hFt : F t (z, 0) = Cdata.chart (z, t) := by
      calc
        F t (z, 0) = FlowSuspension.suspensionFlow Cdata.chart t (z, 0) :=
          congrArg (fun A : Flow ℝ (E × ℝ) => A t (z, 0)) Cdata.flow_eq
        _ = FlowSuspension.suspensionFlow Cdata.chart t (Cdata.chart (z, 0)) :=
          (congrArg (FlowSuspension.suspensionFlow Cdata.chart t) hC0.symm)
        _ = Cdata.chart (z, 0 + t) :=
          (FlowSuspension.suspensionFlow_chart Cdata.chart t (z, 0))
        _ = Cdata.chart (z, t) := by rw [zero_add]
    rw [hΩmap]
    exact ((hfull (z, 0) h0 t).trans (congrArg Φ hFt)).symm
  refine
    ⟨N, g, V', G, hN, hNsub, hg, hgerm, hg0, hV', hG, hzeros, hneg, ?_,
      native_flow_time_change_orbits hρ.continuous hρpos hV'₁ H G hH hG, ?_, ?_, ?_, Ω, hΩsource,
      hΩtarget, hΩfield, hΩlower, hΩupper, hΩaxis, hΩflow⟩
  · intro x hx
    filter_upwards [hρgerm x hx] with y hy
    simp only [V', hy, one_smul]
  · intro z hz t ht
    have hp : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    rw [hfull _ hp, hleft z t ht]
  · intro z hz t ht
    have hp : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    rw [hfull _ hp, hright z t ht]
  · intro s t
    have hp : ((0 : E), s) ∈ Φ.source := by rw [hsource]; exact ⟨h0U, Set.mem_univ _⟩
    rw [hfull _ hp, haxis]

/-- A native matched phase cylinder exists. -/
theorem FlowTimeChange.exists_native_matched_phase_cylinder {E Z B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
    [T2Space M] [CompactSpace M] (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Ω.source = U ×ˢ Set.univ)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (hQtarget : Q.target = U)
    (hQ0 : (0 : E) ∈ Q.source) (hQzero : Q 0 = 0) (P : E → Z) {v₀ v₁ : E → ℝ}
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ y ∈ Ω.target,
        V y = FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hleft : ∀ p, p.2 ≤ 0 → Ω p = Φ p)
    (hright : ∀ᶠ z in 𝓝 (0 : E), ∀ t : ℝ, 1 ≤ t → Ω (Q z, t) = Φ (P z, t)) :
    ∃ (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M) (Ξ :
      PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞),
      IsCompact N ∧
        N ⊆ Ω.target ∧
          ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ (f : M → ℝ) x,
                    mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (W x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                    (∀ x,
                        Set.range (fun t => G t x) = Set.range (fun t => F t x) ∧
                          (∀ p,
                              Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) ∧
                            ∀ p,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) ∧
                      Ξ.source = Q.source ×ˢ Set.univ ∧
                        Ξ.target = Ω.target ∧
                          (∀ y ∈ Ξ.target,
                              W y =
                                FlowConstruction.partialChartField Ξ.symm
                                  (fun _ : E × ℝ => (0, 1)) y) ∧
                            (∀ t : ℝ, Ξ (0, t) = Ω (0, t)) ∧
                              ∀ᶠ z in 𝓝 (0 : E),
                                (∀ t : ℝ, t ≤ -1 → Ξ (z, t) = Φ (Q z, t + v₀ z)) ∧
                                  (∀ t : ℝ, 2 ≤ t → Ξ (z, t) = Φ (P z, t + v₁ z)) := by
  obtain ⟨Ψ, hΨsource, hΨtarget, hΨmap, hΨmodel⟩ :=
    FlowSuspension.exists_native_phase_cylinder Ω hsource Q hQtarget v₀ hv₀ V hmodel
  let v : E → ℝ := fun z => v₁ z - v₀ z
  have hv : ContDiff ℝ ∞ v := hv₁.sub hv₀
  have hvzero : v 0 = 0 := by simp only [v, hv₁zero, hv₀zero, sub_self]
  obtain
    ⟨N, g, W, G, hN, hNsub, _, hgerm, _, hW, hG, hzero, hdesc, hfield, hgeometry, _, _, _, Ξ,
      hΞsource, hΞtarget, hΞmodel, hΞleft, hΞright, hΞaxis, _⟩ :=
    exists_native_phase_realization Ψ Q.open_source hQ0 hΨsource V hV hΨmodel F hF hv hvzero
  have hsmall₀ : ∀ᶠ z in 𝓝 (0 : E), v₀ z ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    hv₀.continuous.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by rw [hv₀zero]; constructor <;> norm_num))
  have hsmall₁ : ∀ᶠ z in 𝓝 (0 : E), v₁ z ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    hv₁.continuous.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by rw [hv₁zero]; constructor <;> norm_num))
  refine
    ⟨N, W, G, Ξ, hN, fun x hx => hΨtarget ▸ (hNsub hx).1, hW, hG, hzero, hdesc, hfield, hgeometry,
      hΞsource, hΞtarget.trans hΨtarget, hΞmodel, ?_, ?_⟩
  · intro t
    rw [hΞaxis, hΨmap, hQzero, hv₀zero, add_zero]
  · filter_upwards [hgerm, hright, hsmall₀, hsmall₁] with z hg hr h₀ h₁
    constructor
    · intro t ht
      rw [hΞleft (z, t) (by dsimp; linarith), hΨmap]
      exact hleft (Q z, t + v₀ z) (by dsimp; linarith [h₀.2])
    · intro t ht
      have hclock : t + g z + v₀ z = t + v₁ z := by
        change g z = v₁ z - v₀ z at hg
        rw [hg]
        ring
      rw [hΞright (z, t) (by dsimp; linarith), hΨmap, hclock]
      exact hr (t + v₁ z) (by linarith [h₁.1])

/-- A unique phase-corrected cylinder exists. -/
theorem FlowSuspension.exists_unique_phase_corrected_cylinder {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source) (hQtarget : Q.target = U)
    (hPtarget : P.target = U) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
        (fun y : B => (0, y)) 0 0)
    {p q : M}
    (hleftBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 0))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ H.source ∧ Q (x, 0) = z)
    (hrightBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 1))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ H.target, y.1 = 0 ∧ P y = z)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x)
    {v₀ v₁ : (A × B) → ℝ} (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0)
    (hv₁zero : v₁ 0 = 0) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G :
      Flow ℝ M) (Ξ : PartialDiffeomorph 𝓘(ℝ, (A × B) × ℝ) 𝓘(ℝ, E) ((A × B) × ℝ) M ∞),
      IsCompact N ∧
        N ⊆ Φ.target ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                    Ξ.source = Q.source ×ˢ Set.univ ∧
                      Ξ.target = Φ.target ∧
                        (∀ y ∈ Ξ.target,
                            W y =
                              FlowConstruction.partialChartField Ξ.symm
                                (fun _ : (A × B) × ℝ => (0, 1)) y) ∧
                          (∀ t : ℝ, Ξ (0, t) = Φ (0, t)) ∧
                            (∀ x,
                                Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q) →
                                  Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) →
                                    ∃ t, G t (Φ (0, 0)) = x) ∧
                              ∀ᶠ u in 𝓝 (0 : A × B),
                                (∀ t : ℝ, t ≤ -1 → Ξ (u, t) = Φ (Q u, t + v₀ u)) ∧
                                  (∀ t : ℝ,
                                    2 ≤ t →
                                      Ξ (u, t) =
                                        Φ (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) := by
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have h0U : (0 : Z) ∈ U := by
    have hh := hQU (Q.map_source' (hHs h0))
    rwa [hQ0] at hh
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : Φ (z, t) = F t (Φ (z, 0)) := by
    simpa only [zero_add] using
      (native_vertical_cylinder_flow Φ hsource (hV.of_le (by simp)) hmodel F hF z hz 0 t).symm
  have hrelative :=
    relative_intersection_of_native_unique_connection Φ hsource h0U F hflow Q P H h0 hH0 hQ0 hHs
      hQU hdiagram hleftBasin hrightBasin hold
  obtain
    ⟨L₁, L₂, N₁, V₁, G₁, Ω, hN₁, hN₁sub, hV₁, hG₁, hzero₁, hdesc₁, hgerm₁, hout₁, hΩsource,
      hΩtarget, hΩfield, hΩflow, hΩleft, haxis₁, hΩsection, hleftTail, hrightTail, hsection,
      hΩright⟩ :=
    exists_native_block_holonomy Φ hsource hf hheight V hV hmodel F hF Q P H h0 hH0 hQ0 hP0 hHs
      hHt hQU hPU hdiagram htrans hrelative
  have hunique₁ :=
    corrected_cylinder_unique_connection Φ Ω h0U hsource hΩsource hΩtarget F G₁ hflow hΩflow
      hΩsection hleftTail hrightTail hout₁ Q P hQ0 H.source H.target hleftBasin hrightBasin
      hsection hold
  let L := L₁.prodCongr L₂
  have hv₁L : ContDiff ℝ ∞ (fun u : A × B => v₁ (L u)) := hv₁.comp L.contDiff
  have hv₁L0 : v₁ (L (0 : A × B)) = 0 := by rw [map_zero, hv₁zero]
  obtain
    ⟨N₂, W, G, Ξ, hN₂, hN₂sub, hW, hG, hzero₂, hdesc₂, hgerm₂, hgeometry, hΞsource, hΞtarget,
      hΞfield, hΞaxis, hΞmatch⟩ :=
    FlowTimeChange.exists_native_matched_phase_cylinder Φ Ω hΩsource Q hQtarget (hHs h0)
      hQ0 (fun u => P (L u)) hv₀ hv₁L hv₀zero hv₁L0 V₁ hV₁ hΩfield G₁ hG₁ hΩleft hΩright
  let N := N₁ ∪ N₂
  have hN : IsCompact N := hN₁.union hN₂
  have hNsub : N ⊆ Φ.target := by
    intro x hx
    rcases hx with hx | hx
    · exact (hN₁sub hx).1
    · exact hΩtarget ▸ hN₂sub hx
  have hkeep (x : M) (hx : x ∉ N) : ∀ᶠ y in 𝓝 x, W y = V y := by
    filter_upwards [hgerm₂ x (fun h => hx (Or.inr h)), hgerm₁ x (fun h => hx (Or.inl h))] with y
      h₂ h₁
    exact h₂.trans h₁
  have haxis (t : ℝ) : Ξ (0, t) = Φ (0, t) := by rw [hΞaxis, hΩflow 0 h0U t, haxis₁ 0 t, zero_add]
  have hunique :
    ∀ x,
      Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x := by
    intro x hbot htop
    obtain ⟨t, ht⟩ := hunique₁ x ((hgeometry x).2.2 q |>.mp hbot) ((hgeometry x).2.1 p |>.mp htop)
    have hmem : x ∈ Set.range (fun t => G₁ t (Φ (0, 0))) := ⟨t, ht⟩
    rw [← (hgeometry (Φ (0, 0))).1] at hmem
    exact hmem
  exact
    ⟨L₁, L₂, N, W, G, Ξ, hN, hNsub, hW, hG, fun x => (hzero₂ x).trans (hzero₁ x), fun x hx =>
      hdesc₂ f x (hdesc₁ x hx), hkeep, hΞsource, hΞtarget.trans hΩtarget, hΞfield, haxis, hunique,
      hΞmatch⟩

end
