/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection

/-!
# The cubic model of a cancelling pair

The local model of a pair of critical points of adjacent index joined by one
trajectory is the cubic `MorseCancellation.cubic σ t` on `Model m = ℝ × (Fin m → ℝ)`
(imported from `Morse.Connection`): for `t = -(a ^ 2) < 0` the descent field
`cubicDescent σ t` has exactly the two zeros `(±a, 0)`, joined by the axis
`Icc (-a) a × {0}`. This file holds the model-space part of the cancellation:

* the cancelled descent field `cancelledDescent σ a φ`, which agrees with
  `cubicDescent σ (-(a ^ 2))` off the support of a cutoff `φ`, is nowhere zero,
  and points downward along the axis (`exists_cubic_field_cancellation`);
* the Lyapunov function `fieldLyapunov σ k = p.1 + k * ∑ σ i * p.2 i ^ 2`, whose
  derivative along the cancelled field is negative on any compact set for `k`
  large (`exists_compact_fieldLyapunov`), via the transverse energy
  `transverseEnergy σ`;
* the Hessian `hessian σ p` of the cubic and the fact that the cubic is a Morse
  function for `t ≠ 0` (`cubic_isMorse`);
* a smooth cutoff equal to `1` near the origin with support in a given open set
  (`NativeCubicCancellation.exists_cutoff`).

This is the model computation behind Milnor, *Lectures on the h-cobordism
theorem*, §5 (First Cancellation Theorem): the pair `(a, 0)`, `(-a, 0)` of the
cubic is removed by a compactly supported change of the gradient-like field.

## Tags

morse-theory, cancellation, cubic-model
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### The cancelled descent field -/

/-- The cancelled descent field. -/
def MorseCancellation.cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (φ : Model m → ℝ) (p : Model m) :
    Model m :=
  (a ^ 2 - p.1 ^ 2 - 2 * a ^ 2 * φ p, fun i => -σ i * p.2 i)

/-- The cancelled descent field is smooth. -/
theorem MorseCancellation.contDiff_cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (cancelledDescent σ a φ) := by
  unfold cancelledDescent
  fun_prop

/-- The cancelled descent points negatively on the axis. -/
theorem MorseCancellation.cancelledDescent_axis_negative {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) (s : ℝ) :
    (cancelledDescent σ a φ (s, 0)).1 < 0 := by
  change a ^ 2 - s ^ 2 - 2 * a ^ 2 * φ (s, 0) < 0
  by_cases hs : s ∈ Set.Icc (-a) a
  · rw [hone s hs]
    nlinarith [sq_pos_of_pos ha, sq_nonneg s]
  · have hsq : a ^ 2 < s ^ 2 := by
      by_cases hl : -a ≤ s
      · have hr : a < s := lt_of_not_ge (fun h => hs ⟨hl, h⟩)
        nlinarith
      · have hh : s < -a := lt_of_not_ge hl
        nlinarith
    have hnonneg : 0 ≤ 2 * a ^ 2 * φ (s, 0) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) (hφ (s, 0))
    linarith

/-- The cancelled descent is nonvanishing. -/
theorem MorseCancellation.cancelledDescent_ne_zero {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {a : ℝ}
    (ha : 0 < a) {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1)
    (p : Model m) : cancelledDescent σ a φ p ≠ 0 := by
  intro hp
  have hz : p.2 = 0 := by
    funext i
    have hi := congrArg (fun q : Model m => q.2 i) hp
    change -σ i * p.2 i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr (hσ i))
  have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
  have hx := congrArg Prod.fst hp
  rw [he] at hx
  exact (cancelledDescent_axis_negative σ ha hφ hone p.1).ne hx

/-- The cancelled descent's germ off the support. -/
theorem MorseCancellation.cancelledDescent_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    {φ : Model m → ℝ} {p : Model m} (hp : p ∉ tsupport φ) :
    cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
  apply Prod.ext
  · simp only [cancelledDescent, cubicDescent, hq, Pi.zero_apply, MulZeroClass.mul_zero, sub_zero]
    ring
  · rfl

/-- A cubic field cancellation exists. -/
theorem MorseCancellation.exists_cubic_field_cancellation {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {U : Set (Model m)} (hU : IsOpen U)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ U) :
    ∃ φ : Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ U ∧
            (∀ p, φ p ∈ Set.Icc (0 : ℝ) 1) ∧
              (∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) ∧
                ContDiff ℝ ∞ (cancelledDescent σ a φ) ∧
                  (∀ p, cancelledDescent σ a φ p ≠ 0) ∧
                    ∀ p ∉ tsupport φ, cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  obtain ⟨φ, hφ, hc, hsupp, hone, hrange⟩ :=
    exists_compact_smooth_cutoff (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hU
      haxis
  have hone' (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : φ (s, (0 : Fin m → ℝ)) = 1 := by
    have hn : ∀ᶠ p in 𝓝 (s, (0 : Fin m → ℝ)), φ p = 1 :=
      (nhds_le_nhdsSet (show (s, (0 : Fin m → ℝ)) ∈ Set.Icc (-a) a ×ˢ {0} from ⟨hs, rfl⟩)) hone
    exact hn.self_of_nhds
  exact
    ⟨φ, hφ, hc, hsupp, hrange, hone', contDiff_cancelledDescent σ a hφ,
      cancelledDescent_ne_zero σ hσ ha (fun p => (hrange p).1) hone', fun p hp =>
      cancelledDescent_germ_off_support σ a hp⟩

/-- The cubic descent vanishes exactly at the critical point. -/
theorem MorseCancellation.cubicDescent_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) (a : ℝ)
    (p : Model m) : cubicDescent σ (-(a ^ 2)) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [← negative_parameter_critical_iff σ hσ a p]
  constructor
  · intro hp
    by_contra hn
    have hh := cubicDescent_strict σ hn
    rw [hp, map_zero] at hh
    exact lt_irrefl _ hh
  · exact cubicDescent_zero_of_critical σ

/-! ### The transverse energy Lyapunov function -/

/-- The transverse energy Lyapunov function. -/
def MorseCancellation.transverseEnergy {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : ℝ :=
  ∑ i, (σ i * p.2 i) ^ 2

/-- The transverse energy is nonnegative. -/
theorem MorseCancellation.transverseEnergy_nonneg {m : ℕ} (σ : Fin m → ℝ) (p : Model m) :
    0 ≤ transverseEnergy σ p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The transverse energy vanishes exactly on the axis. -/
theorem MorseCancellation.transverseEnergy_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : transverseEnergy σ p = 0 ↔ p.2 = 0 := by
  constructor
  · intro h
    funext i
    have hh :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp h i
        (Finset.mem_univ i)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hh)).resolve_left (hσ i)
  · intro h
    simp [transverseEnergy, h]

/-- The field Lyapunov function. -/
def MorseCancellation.fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) : ℝ :=
  p.1 + k * ∑ i, σ i * p.2 i ^ 2

/-- The field Lyapunov function is smooth. -/
theorem MorseCancellation.contDiff_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) :
    ContDiff ℝ ∞ (fieldLyapunov σ k) := by
  unfold fieldLyapunov
  fun_prop

/-- The field Lyapunov function is differentiable. -/
theorem MorseCancellation.hasFDerivAt_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) :
    HasFDerivAt (fieldLyapunov σ k)
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
        k •
          ∑ i,
            (2 * σ i * p.2 i) •
              ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))
      p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! hx.add (hq.const_mul k) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [mul_assoc, mul_comm]

/-- The Lyapunov decay speed of the field. -/
theorem MorseCancellation.fieldLyapunov_speed {m : ℕ} (σ : Fin m → ℝ) (k a : ℝ) (φ : Model m → ℝ)
    (p : Model m) :
    fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) =
      (cancelledDescent σ a φ p).1 - 2 * k * transverseEnergy σ p := by
  rw [(hasFDerivAt_fieldLyapunov σ k p).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change
    (cancelledDescent σ a φ p).1 + k * (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = _
  have hsum :
    (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = -2 * transverseEnergy σ p := by
    rw [transverseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change 2 * σ i * p.2 i * (-σ i * p.2 i) = _
    ring
  rw [hsum]
  ring

/-- A compact field Lyapunov bound exists. -/
theorem MorseCancellation.exists_compact_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) {C : Set (Model m)} (hC : IsCompact C) :
    ∃ k : ℝ,
      0 ≤ k ∧
        ContDiff ℝ ∞ (fieldLyapunov σ k) ∧
          ∀ p ∈ C, fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) < 0 := by
  let O : ℕ → Set (Model m) := fun n =>
    {p | (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0}
  have henergy : Continuous (transverseEnergy σ) := by
    unfold transverseEnergy
    fun_prop
  have hO (n : ℕ) : IsOpen (O n) :=
    isOpen_lt
      ((contDiff_cancelledDescent σ a hφ).continuous.fst.sub (continuous_const.mul henergy))
      continuous_const
  have hcover : C ⊆ ⋃ n, O n := by
    intro p hp
    by_cases hz : p.2 = 0
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
      have hh := cancelledDescent_axis_negative σ ha hφnonneg hone p.1
      have hneg : (cancelledDescent σ a φ p).1 < 0 :=
        (congrArg (fun q : Model m => (cancelledDescent σ a φ q).1) he).trans_lt hh
      simpa only [O, Set.mem_ofPred_eq, Nat.cast_zero, MulZeroClass.mul_zero,
        MulZeroClass.zero_mul, sub_zero] using hneg
    · have hpos : 0 < transverseEnergy σ p :=
        lt_of_le_of_ne (transverseEnergy_nonneg σ p)
          (Ne.symm (fun he => hz ((transverseEnergy_zero_iff σ hσ p).mp he)))
      obtain ⟨n, hn⟩ := exists_nat_gt ((cancelledDescent σ a φ p).1 / (2 * transverseEnergy σ p))
      have hh := (div_lt_iff₀ (mul_pos (by norm_num) hpos)).mp hn
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0
      nlinarith
  have hmono : Monotone O := by
    intro i j hij p hp
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have he := transverseEnergy_nonneg σ p
    change (cancelledDescent σ a φ p).1 - 2 * (i : ℝ) * transverseEnergy σ p < 0 at hp
    change (cancelledDescent σ a φ p).1 - 2 * (j : ℝ) * transverseEnergy σ p < 0
    nlinarith
  obtain ⟨n, hn⟩ :=
    hC.elim_directed_cover O hO hcover
      (fun i j => ⟨Max.max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
  refine ⟨n, by positivity, contDiff_fieldLyapunov σ n, ?_⟩
  intro p hp
  rw [fieldLyapunov_speed]
  exact hn hp

/-! ### The cubic Hessian -/

/-- The Hessian of the cubic model. -/
def MorseCancellation.hessian {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : Model m →L[ℝ] Model m →L[ℝ] ℝ :=
  (2 * p.1) •
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).smulRight
        (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) +
    ∑ i,
      (2 * σ i) •
        (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).smulRight
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))

/-- The Hessian computes the second derivative. -/
theorem MorseCancellation.hessian_apply {m : ℕ} (σ : Fin m → ℝ) (p v w : Model m) :
    hessian σ p v w = 2 * p.1 * v.1 * w.1 + ∑ i, 2 * σ i * v.2 i * w.2 i := by
  simp [hessian, mul_assoc]

/-- The differential is differentiable. -/
theorem MorseCancellation.hasFDerivAt_differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (differential σ t) (hessian σ p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  let L (i : Fin m) : Model m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))
  have hq :=
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (((L i).hasFDerivAt (x := p)).const_mul (2 * σ i)).smul_const (L i))
  convert
      (((hx.pow 2).add_const t).smul_const (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ))).add hq using
      1 <;>
    first
    | rfl
    | ( apply ContinuousLinearMap.ext; intro v
        apply ContinuousLinearMap.ext; intro w
        simp [hessian, L, mul_assoc])

/-- The cubic's Hessian derivative. -/
theorem MorseCancellation.fderiv_cubic_hessian {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (fderiv ℝ (cubic σ t)) p = hessian σ p := by
  rw [show fderiv ℝ (cubic σ t) = differential σ t from funext (fderiv_cubic σ t)]
  exact (hasFDerivAt_differential σ t p).fderiv

/-- The cubic Hessian is bijective at the critical point. -/
theorem MorseCancellation.hessian_bijective {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {p : Model m}
    (hp : p.1 ≠ 0) : Function.Bijective (hessian σ p) := by
  have hi : Function.Injective (hessian σ p) := by
    apply (injective_iff_map_eq_zero (hessian σ p)).mpr
    intro v hv
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hv
    have hx' : 2 * p.1 * v.1 = 0 := by simpa [hessian_apply] using hx
    have hvx : v.1 = 0 := (mul_eq_zero.mp hx').resolve_left (mul_ne_zero (by norm_num) hp)
    apply Prod.ext hvx
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hv
    have hy' : 2 * σ i * v.2 i = 0 := by simpa [hessian_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  have hd : Module.finrank ℝ (Model m) = Module.finrank ℝ (Model m →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (Model m →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = _ :=
        (LinearMap.toContinuousLinearMap : (Model m →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Model m →L[ℝ] ℝ)).finrank_eq
  exact
    ⟨hi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (hessian σ p).toLinearMap)
            hd).mp
        hi⟩

/-- The cubic critical point is Morse. -/
theorem MorseCancellation.cubic_isMorse {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) : MorsePerturbation.IsMorse (cubic σ t) := by
  intro p hcrit
  rw [fderiv_cubic_hessian]
  apply hessian_bijective σ hσ
  intro hp
  have h := ((critical_iff σ hσ t p).mp hcrit).1
  exact ht (by simpa [hp] using h)

/-! ### Native cubic cancellation -/

/-- A cutoff for the native cubic cancellation exists. -/
theorem NativeCubicCancellation.exists_cutoff {m : ℕ} {V : Set (MorseCancellation.Model m)}
    (hV : IsOpen V) (h0 : (0 : MorseCancellation.Model m) ∈ V) :
    ∃ φ : MorseCancellation.Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ V ∧
            ∃ U : Set (MorseCancellation.Model m),
              IsOpen U ∧ (0 : MorseCancellation.Model m) ∈ U ∧ Set.EqOn φ (fun _ => 1) U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let φ : ContDiffBump (0 : MorseCancellation.Model m) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine
    ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, Metric.ball 0 (r / 4), Metric.isOpen_ball,
      Metric.mem_ball_self (by positivity), ?_⟩
  · rw [φ.tsupport_eq]
    intro p hp
    apply hball
    exact lt_of_le_of_lt hp (by change r / 2 < r; linarith)
  · intro p hp
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hp)

end
