/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Diffeomorph
/-!
# Linearisation of germs by compactly supported isotopies

A smooth map fixing the origin whose derivative there is the identity agrees near the origin with
the time-one map of a compactly supported isotopy of diffeomorphisms; the construction is a cut-off
`x + β x • u x` of the nonlinear part `u`, kept a diffeomorphism by a small Lipschitz constant.
Relative versions preserve a linear functional and fix a subspace, and a map with bijective
derivative factors near the origin as its derivative composed with such a time-one map.

## Main results

* `SmallPerturbation.exists_supported_tangent_identity_isotopy`
* `SmallPerturbation.exists_relative_germ_linearization_isotopy`

## References

* cf. [M. Hirsch, *Differential Topology*][hirsch76], Ch. 8 §3 (proof of the disc theorem).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- A cut-off of a bounded Lipschitz map is Lipschitz, with constant `a + b R` in terms of the
Lipschitz constants and the bound.
-/
theorem SmallPerturbation.lipschitzWith_cutoff_smul {P E : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : P → E} {β : P → ℝ} {S : Set P} {a b R : ℝ≥0}
    (hu : LipschitzOnWith a u S) (hbound : ∀ x ∈ S, ‖u x‖ ≤ R) (hβ : LipschitzWith b β)
    (hβbound : ∀ x, |β x| ≤ 1) (hzero : ∀ x ∉ S, β x = 0) :
    LipschitzWith (a + b * R) (fun x => β x • u x) := by
  have hcross (x y : P) (hx : x ∈ S) (hy : y ∉ S) :
    Dist.dist (β x • u x) (β y • u y) ≤ ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
    have hβx : |β x| ≤ (b : ℝ) * Dist.dist x y := by
      have h := hβ.dist_le_mul x y
      simpa only [hzero y hy, Real.dist_eq, sub_zero] using h
    rw [hzero y hy, zero_smul, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc
      |β x| * ‖u x‖ ≤ ((b : ℝ) * Dist.dist x y) * R :=
        mul_le_mul hβx (hbound x hx) (norm_nonneg _) (by positivity)
      _ ≤ ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
        simp only [NNReal.coe_add, NNReal.coe_mul]
        nlinarith [mul_nonneg a.coe_nonneg (dist_nonneg (x := x) (y := y))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · have hu' : ‖u x - u y‖ ≤ (a : ℝ) * Dist.dist x y := by
        simpa only [dist_eq_norm] using hu.dist_le_mul x hx y hy
      have hβ' : |β x - β y| ≤ (b : ℝ) * Dist.dist x y := by
        simpa only [Real.dist_eq] using hβ.dist_le_mul x y
      have hsplit : β x • u x - β y • u y = β x • (u x - u y) + (β x - β y) • u y := by
        rw [smul_sub, sub_smul]
        abel
      rw [dist_eq_norm, hsplit]
      calc
        ‖β x • (u x - u y) + (β x - β y) • u y‖ ≤ ‖β x • (u x - u y)‖ + ‖(β x - β y) • u y‖ :=
          norm_add_le _ _
        _ = |β x| * ‖u x - u y‖ + |β x - β y| * ‖u y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ((a : ℝ) * Dist.dist x y) + ((b : ℝ) * Dist.dist x y) * R := by
          exact
            add_le_add (mul_le_mul (hβbound x) hu' (norm_nonneg _) (by norm_num))
              (mul_le_mul hβ' (hbound y hy) (norm_nonneg _) (by positivity))
        _ = ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          ring
    · exact hcross x y hx hy
  · by_cases hy : y ∈ S
    · simpa only [dist_comm] using hcross y x hy hx
    · rw [hzero x hx, hzero y hy, zero_smul, zero_smul, dist_self]
      positivity

/-- A smooth map whose derivative vanishes at the origin is Lipschitz with arbitrarily small
constant on some closed ball around the origin.
-/
theorem SmallPerturbation.exists_closedBall_small_lipschitz_of_fderiv_zero {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] {u : P → E}
    {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hu : ContDiffOn ℝ ∞ u U)
    (hdu : fderiv ℝ u 0 = 0) {a : ℝ≥0} (ha : 0 < a) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        Metric.closedBall (0 : P) ρ ⊆ U ∧ LipschitzOnWith a u (Metric.closedBall (0 : P) ρ) := by
  have hd : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hzero)
  have hsmall : ∀ᶠ x in 𝓝 (0 : P), ‖fderiv ℝ u x‖ < (a : ℝ) := by
    have h : ∀ᶠ x in 𝓝 (0 : P), fderiv ℝ u x ∈ Metric.ball (fderiv ℝ u 0) (a : ℝ) :=
      hd.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ u 0) (show (0 : ℝ) < a from ha))
    simpa only [hdu, mem_ball_zero_iff] using h
  have hnear : ∀ᶠ x in 𝓝 (0 : P), x ∈ U := hU.mem_nhds hzero
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hnear.and hsmall)
  refine ⟨ρ, hρ, fun x hx => (hball hx).1, ?_⟩
  apply (convex_closedBall (0 : P) ρ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hball hx).1)).differentiableAt (by simp)
  · intro x hx
    exact (hball hx).2.le

/-- A smooth map vanishing to first order at the origin agrees near the origin with a compactly
supported map that is globally Lipschitz with arbitrarily small constant and is pointwise a
scalar multiple of it between `0` and `1`.
-/
theorem SmallPerturbation.exists_lipschitz_supported_germ {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : P → E} {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (hu : ContDiffOn ℝ ∞ u U) (hu₀ : u 0 = 0) (hdu : fderiv ℝ u 0 = 0) {κ : ℝ≥0} (hκ : 0 < κ) :
    ∃ w : P → E,
      ContDiff ℝ ∞ w ∧
        HasCompactSupport w ∧
          tsupport w ⊆ U ∧
            LipschitzWith κ w ∧ w =ᶠ[𝓝 (0 : P)] u ∧ ∀ x, ∃ c ∈ Set.Icc (0 : ℝ) 1, w x = c • u x :=
  by
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : P)}) (U := Metric.ball (0 : P) 1)
      isCompact_singleton Metric.isOpen_ball (by simp)
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hβcompact hβ (by simp)
  let a : ℝ≥0 := κ / (1 + k)
  have hden : (0 : ℝ≥0) < 1 + k := by positivity
  have ha : 0 < a := div_pos hκ hden
  obtain ⟨ρ, hρ, hρU, hlocal⟩ :=
    exists_closedBall_small_lipschitz_of_fderiv_zero hU hzero hu hdu ha
  let r : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : 0 < r := hρ
  let βρ : P → ℝ := fun x => β (ρ⁻¹ • x)
  have hβρ : ContDiff ℝ ∞ βρ := hβ.comp (ρ⁻¹ • ContinuousLinearMap.id ℝ P).contDiff
  have hβρlip : LipschitzWith (k * ‖ρ⁻¹‖₊) βρ := hk.comp (lipschitzWith_smul ρ⁻¹)
  have hβρbound (x : P) : |βρ x| ≤ 1 := by
    change |β (ρ⁻¹ • x)| ≤ 1
    rw [abs_of_nonneg (hβrange _).1]
    exact (hβrange _).2
  have hβρzero (x : P) (hx : x ∉ Metric.closedBall (0 : P) ρ) : βρ x = 0 := by
    by_contra hne
    have hm : ρ⁻¹ • x ∈ Metric.ball (0 : P) 1 := hβsupport (subset_tsupport β hne)
    have hn : ‖ρ⁻¹ • x‖ < 1 := mem_ball_zero_iff.mp hm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_lt_one₀ hρ] at hn
    exact hx (mem_closedBall_zero_iff.mpr hn.le)
  have hbound : ∀ x ∈ Metric.closedBall (0 : P) ρ, ‖u x‖ ≤ (a * r : ℝ≥0) := by
    intro x hx
    have h0 : (0 : P) ∈ Metric.closedBall (0 : P) ρ := by simpa using hρ.le
    have hn := hlocal.dist_le_mul x hx 0 h0
    rw [hu₀, dist_zero_right, dist_zero_right] at hn
    change ‖u x‖ ≤ (a : ℝ) * ρ
    exact hn.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) a.coe_nonneg)
  let w : P → E := fun x => βρ x • u x
  have hwzero (x : P) (hx : x ∉ Metric.closedBall (0 : P) ρ) : w x = 0 := by
    change βρ x • u x = 0
    rw [hβρzero x hx, zero_smul]
  have hsmooth : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβρ.contDiffAt.smul (hu.contDiffAt (hU.mem_nhds hx))
    · have hnot : x ∉ Metric.closedBall (0 : P) ρ := fun h => hx (hρU h)
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) x := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hnot] with y hy
      exact hwzero y hy
  have hcompact : HasCompactSupport w :=
    HasCompactSupport.intro (ProperSpace.isCompact_closedBall (0 : P) ρ) hwzero
  have hsupport : tsupport w ⊆ Metric.closedBall (0 : P) ρ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (hwzero x hnot)
  have hwlip : LipschitzWith (a + (k * ‖ρ⁻¹‖₊) * (a * r)) w :=
    lipschitzWith_cutoff_smul hlocal hbound hβρlip hβρbound hβρzero
  have hnn : ‖ρ‖₊ = r := Real.nnnorm_of_nonneg hρ.le
  have hcoeff : a + (k * ‖ρ⁻¹‖₊) * (a * r) = κ := by
    rw [nnnorm_inv, hnn]
    calc
      a + (k * r⁻¹) * (a * r) = a + (k * a) * (r⁻¹ * r) := by ring
      _ = a + k * a := by rw [inv_mul_cancel₀ hr.ne', mul_one]
      _ = (1 + k) * a := by ring
      _ = κ := by
        dsimp [a]
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm (1 + k) κ, mul_assoc, mul_inv_cancel₀ hden.ne',
          mul_one]
  rw [hcoeff] at hwlip
  have hβ₀ : ∀ᶠ x in 𝓝 (0 : P), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : P)))
  have hscale : Filter.Tendsto (fun x : P => ρ⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have hs : Continuous (fun x : P => ρ⁻¹ • x) := (ρ⁻¹ • ContinuousLinearMap.id ℝ P).continuous
    simpa only [smul_zero] using (hs.continuousAt (x := (0 : P))).tendsto
  have hgerm : w =ᶠ[𝓝 (0 : P)] u := by
    have hscaled : ∀ᶠ x in 𝓝 (0 : P), β (ρ⁻¹ • x) = 1 := hscale hβ₀
    filter_upwards [hscaled] with x hx
    change β (ρ⁻¹ • x) • u x = u x
    rw [hx, one_smul]
  refine ⟨w, hsmooth, hcompact, hsupport.trans hρU, hwlip, hgerm, ?_⟩
  intro x
  exact ⟨βρ x, hβrange _, rfl⟩

/-- A smooth map fixing the origin whose derivative there is the identity agrees near the origin
with the time-one map of a compactly supported isotopy of diffeomorphisms.
-/
theorem SmallPerturbation.exists_supported_tangent_identity_isotopy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0)
    (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
            (∀ x, A (0, x) = x) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                (∀ t x, x ∉ K → A (t, x) = x) ∧
                  (∀ t x, ∃ c ∈ Set.Icc (0 : ℝ) 1, A (t, x) = x + c • (f x - x)) ∧
                    (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  let u : E → E := fun x => f x - x
  have hu : ContDiffOn ℝ ∞ u U := hf.sub contDiffOn_id
  have hu₀ : u 0 = 0 := by simp [u, hf₀]
  have hdu : fderiv ℝ u 0 = 0 := by
    have hdiff : DifferentiableAt ℝ f 0 :=
      (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
    change fderiv ℝ (f - id) 0 = 0
    rw [fderiv_sub hdiff differentiableAt_id, hdf, fderiv_id, sub_self]
  obtain ⟨w, hw, hwcompact, hwsupport, hwlip, hweq, hwscalar⟩ :=
    exists_lipschitz_supported_germ hU hzero hu hu₀ hdu (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let A : ℝ × E → E := fun p => p.2 + Real.smoothTransition p.1 • w p.2
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hθ.comp contMDiff_fst).smul (hw.contMDiff.comp contMDiff_snd))
  refine ⟨A, tsupport w, hwcompact.isCompact, hwsupport, hA, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [A, Real.smoothTransition.zero]
  · intro t
    have hs : ContDiff ℝ ∞ (fun x => Real.smoothTransition t • w x) := contDiff_const.smul hw
    have hlip :
      LipschitzWith (‖Real.smoothTransition t‖₊ * (1 / 2))
        (fun x => Real.smoothTransition t • w x) :=
      (lipschitzWith_smul (Real.smoothTransition t)).comp hwlip
    have hθnorm : ‖Real.smoothTransition t‖₊ ≤ 1 := by
      change ‖Real.smoothTransition t‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact Real.smoothTransition.le_one t
    have hsmall : ‖Real.smoothTransition t‖₊ * (1 / 2 : ℝ≥0) < 1 := by
      calc
        _ ≤ 1 * (1 / 2 : ℝ≥0) := mul_le_mul_of_nonneg_right hθnorm (by positivity)
        _ < 1 := by norm_num
    have hloc :
      IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun x => x + Real.smoothTransition t • w x) := by
      intro x
      apply
        isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
          ((contDiff_id.add hs).contMDiff.contMDiffOn)
      rw [mfderiv_eq_fderiv]
      exact isInvertible_fderiv_id_add hs hlip hsmall x
    exact
      ⟨IsLocalDiffeomorph.diffeomorph' hloc (bijective_id_add hlip hsmall), fun _ => rfl⟩
  · intro t x hx
    have hz : w x = 0 := by
      by_contra hne
      exact hx (subset_tsupport w hne)
    simp only [A, hz, smul_zero, add_zero]
  · intro t x
    obtain ⟨c, hc, hwc⟩ := hwscalar x
    refine
      ⟨Real.smoothTransition t * c,
        ⟨mul_nonneg (Real.smoothTransition.nonneg t) hc.1,
          (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) hc.1).trans
            (by simpa only [one_mul] using hc.2)⟩,
        ?_⟩
    change x + Real.smoothTransition t • w x = x + _
    rw [hwc, smul_smul]
  · filter_upwards [hweq] with x hx
    change x + Real.smoothTransition 1 • w x = f x
    rw [Real.smoothTransition.one, one_smul, hx]
    change x + (f x - x) = f x
    abel

/-- The relative form of the previous statement: the isotopy can be taken to preserve a linear
functional `Q` that the map preserves and to fix a set `S` that the map fixes.
-/
theorem SmallPerturbation.exists_relative_tangent_identity_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E} {U S : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0) (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E)
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) (hS : ∀ x ∈ U ∩ S, f x = x) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
            (∀ x, A (0, x) = x) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                (∀ t x, x ∉ K → A (t, x) = x) ∧
                  (∀ t x, Q (A (t, x)) = Q x) ∧
                    (∀ t x, x ∈ S → A (t, x) = x) ∧ (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hscalar, hgerm⟩ :=
    exists_supported_tangent_identity_isotopy hU hzero hf hf₀ hdf
  refine ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, ?_, ?_, hgerm⟩
  · intro t x
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, map_add, map_smul, map_sub, hQ x hx, sub_self, smul_zero, add_zero]
    · rw [hfix t x (fun h => hx (hKU h))]
  · intro t x hxS
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, hS x ⟨hx, hxS⟩, sub_self, smul_zero, add_zero]
    · exact hfix t x (fun h => hx (hKU h))

/-- A map preserving a linear projection `Q` near the origin has derivative preserving `Q`. -/
theorem SmallPerturbation.fderiv_preserves_projection {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableAt ℝ f 0) (Q : E →L[ℝ] F)
    (hQ : ∀ x ∈ U, Q (f x) = Q x) : Q.comp (fderiv ℝ f 0) = Q := by
  have heq : Q ∘ f =ᶠ[𝓝 (0 : E)] Q := by
    filter_upwards [hU.mem_nhds hzero] with x hx
    exact hQ x hx
  have hc : fderiv ℝ (Q ∘ f) 0 = Q.comp (fderiv ℝ f 0) :=
    (Q.hasFDerivAt.comp 0 hf.hasFDerivAt).fderiv
  exact hc.symm.trans (heq.fderiv_eq.trans Q.fderiv)

/-- A map fixing a subspace near the origin has derivative fixing that subspace. -/
theorem SmallPerturbation.fderiv_fixes_subspace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : DifferentiableAt ℝ f 0) (S : Submodule ℝ E) (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∀ x ∈ S, fderiv ℝ f 0 x = x := by
  have heq : f ∘ (S.subtypeL : S → E) =ᶠ[𝓝 (0 : S)] (S.subtypeL : S → E) := by
    have hn : ∀ᶠ x : S in 𝓝 (0 : S), (x : E) ∈ U :=
      S.subtypeL.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hzero)
    filter_upwards [hn] with x hx
    exact hS x ⟨hx, x.property⟩
  have hc : fderiv ℝ (f ∘ (S.subtypeL : S → E)) (0 : S) = (fderiv ℝ f 0).comp S.subtypeL :=
    (hf.hasFDerivAt.comp (0 : S) S.subtypeL.hasFDerivAt).fderiv
  have hlinear : (fderiv ℝ f 0).comp S.subtypeL = S.subtypeL :=
    hc.symm.trans (heq.fderiv_eq.trans S.subtypeL.fderiv)
  intro x hx
  exact congrArg (fun A : S →L[ℝ] E => A ⟨x, hx⟩) hlinear

/-- Germ linearisation: a smooth map fixing the origin with bijective derivative there factors near
the origin as its derivative composed with the time-one map of a compactly supported isotopy;
the linear part and the isotopy inherit the map's preservation of a functional `Q` and of a
subspace `S`.
-/
theorem SmallPerturbation.exists_relative_germ_linearization_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0) (hdf : Function.Bijective (fderiv ℝ f 0))
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) (S : Submodule ℝ E)
    (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∃ (C : E ≃L[ℝ] E) (A : ℝ × E → E) (K : Set E),
      C.toContinuousLinearMap = fderiv ℝ f 0 ∧
        (∀ x, Q (C x) = Q x) ∧
          (∀ x ∈ S, C x = x) ∧
            IsCompact K ∧
              K ⊆ U ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                  (∀ x, A (0, x) = x) ∧
                    (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                      (∀ t x, x ∉ K → A (t, x) = x) ∧
                        (∀ t x, Q (A (t, x)) = Q x) ∧
                          (∀ t x, x ∈ S → A (t, x) = x) ∧
                            f =ᶠ[𝓝 (0 : E)] (fun x => C (A (1, x))) := by
  have hfd : DifferentiableAt ℝ f 0 :=
    (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
  let C := (LinearEquiv.ofBijective (fderiv ℝ f 0).toLinearMap hdf).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ f 0 := rfl
  have hQC : ∀ x, Q (C x) = Q x := by
    intro x
    exact congrArg (fun A : E →L[ℝ] F => A x) (fderiv_preserves_projection hU hzero hfd Q hQ)
  have hCS : ∀ x ∈ S, C x = x := fderiv_fixes_subspace hU hzero hfd S hS
  have hQCinv (y : E) : Q (C.symm y) = Q y := by
    have h := (hQC (C.symm y)).symm
    simpa only [C.apply_symm_apply] using h
  have hCSinv (x : E) (hx : x ∈ S) : C.symm x = x := by
    have h := C.symm_apply_apply x
    rwa [hCS x hx] at h
  let G : E → E := C.symm ∘ f
  have hG : ContDiffOn ℝ ∞ G U := C.symm.contDiff.comp_contDiffOn hf
  have hG₀ : G 0 = 0 := by simp [G, hf₀]
  have hGder : fderiv ℝ G 0 = C.symm.toContinuousLinearMap.comp (fderiv ℝ f 0) :=
    (C.symm.toContinuousLinearMap.hasFDerivAt.comp 0 hfd.hasFDerivAt).fderiv
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ E := by
    rw [hGder, ← hC]
    ext x
    exact C.symm_apply_apply x
  have hQG : ∀ x ∈ U, Q (G x) = Q x := by
    intro x hx
    change Q (C.symm (f x)) = Q x
    rw [hQCinv, hQ x hx]
  have hSG : ∀ x ∈ U ∩ (S : Set E), G x = x := by
    intro x hx
    change C.symm (f x) = x
    rw [hS x hx, hCSinv x hx.2]
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, hgerm⟩ :=
    exists_relative_tangent_identity_isotopy hU hzero hG hG₀ hdG Q hQG hSG
  refine ⟨C, A, K, hC, hQC, hCS, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, ?_⟩
  filter_upwards [hgerm] with x hx
  change A (1, x) = C.symm (f x) at hx
  rw [hx, C.apply_symm_apply]
