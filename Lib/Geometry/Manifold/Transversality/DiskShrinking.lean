/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Transversality.Diffeomorph
/-!
# Radial diffeomorphisms and the disc-shrinking isotopy

The radial map `x ↦ φ(‖x‖²) • x` of an inner product space is a diffeomorphism when `φ` is smooth,
positive, monotone and equal to `1` beyond some radius. With a suitable profile this gives an
isotopy, compactly supported in a ball of radius `R > 1`, that contracts the unit disc by a factor
`a ∈ (0, 1]` and fixes the origin.

## Main definitions and results

* `SmoothRadial.radialMap`, `SmoothRadial.diffeomorph`
* `DiskShrinking.family`, `DiskShrinking.family_slices`, `DiskShrinking.family_one_inner`

## References

* cf. [M. Hirsch, *Differential Topology*][hirsch76], Ch. 8 §3 (proof of the disc theorem).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- The radial map `x ↦ φ(‖x‖²) • x` determined by a real function `φ`. -/
def SmoothRadial.radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (φ : ℝ → ℝ)
    (x : N) : N :=
  φ (‖x‖ ^ 2) • x

/-- For a positive `φ` the radial map multiplies norms by `φ(‖x‖²)`. -/
theorem SmoothRadial.norm_radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (x : N) : ‖radialMap φ x‖ = φ (‖x‖ ^ 2) * ‖x‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos _)]

/-- For a positive monotone `φ` the radius function `r ↦ φ(r²) r` is strictly increasing on
`[0, ∞)`.
-/
theorem SmoothRadial.radius_strictMono {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) : StrictMonoOn (fun r => φ (r ^ 2) * r) (Set.Ici 0) := by
  intro r hr s hs hrs
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs.le
  exact (mul_lt_mul_of_pos_left hrs (hpos _)).trans_le (mul_le_mul_of_nonneg_right (hmono hsq) hs)

/-- For a positive monotone `φ` the radial map is injective. -/
theorem SmoothRadial.radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) :
    Function.Injective (radialMap (N := N) φ) := by
  intro x y hxy
  have hn : ‖x‖ = ‖y‖ := by
    apply (radius_strictMono hpos hmono).injOn (norm_nonneg x) (norm_nonneg y)
    simpa only [norm_radialMap hpos] using congrArg Norm.norm hxy
  change φ (‖x‖ ^ 2) • x = φ (‖y‖ ^ 2) • y at hxy
  rw [hn] at hxy
  exact smul_right_injective N (hpos _).ne' hxy

/-- A continuous `φ` equal to `1` beyond radius `R` gives a surjective radial map. -/
theorem SmoothRadial.radialMap_surjective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hR : 0 < R)
    (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) : Function.Surjective (radialMap (N := N) φ) := by
  intro y
  by_cases hy : R ≤ ‖y‖
  · refine ⟨y, ?_⟩
    rw [radialMap, hout _ ((sq_le_sq₀ hR.le (norm_nonneg y)).mpr hy), one_smul]
  by_cases hyzero : y = 0
  · subst y
    exact ⟨0, by simp only [radialMap, smul_zero]⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hyzero
  have htarget : ‖y‖ ∈ Set.Icc (φ (0 ^ 2) * 0) (φ (R ^ 2) * R) := by
    simpa only [MulZeroClass.mul_zero, hout _ le_rfl, one_mul, Set.mem_Icc] using
      And.intro hypos.le (le_of_not_ge hy)
  have hcont : Continuous (fun r : ℝ => φ (r ^ 2) * r) :=
    (hc.comp (continuous_id.pow 2)).mul continuous_id
  obtain ⟨r, hr, hradius⟩ := intermediate_value_Icc hR.le hcont.continuousOn htarget
  change φ (r ^ 2) * r = ‖y‖ at hradius
  let x : N := (r / ‖y‖) • y
  have hnorm : ‖x‖ = r := by
    change ‖(r / ‖y‖) • y‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hypos.le),
      div_mul_cancel₀ _ hypos.ne']
  refine ⟨x, ?_⟩
  change φ (‖x‖ ^ 2) • ((r / ‖y‖) • y) = y
  rw [hnorm, smul_smul, ← mul_div_assoc, hradius, div_self hypos.ne', one_smul]

/-- The radial map of a smooth `φ` is smooth on an inner product space. -/
theorem SmoothRadial.contDiff_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (radialMap (N := N) φ) :=
  (hφ.comp (contDiff_id.norm_sq ℝ)).smul contDiff_id

/-- The derivative of the radial map: `v ↦ φ(‖x‖²) • v + 2 φ'(‖x‖²) ⟪x, v⟫ • x`. -/
theorem SmoothRadial.fderiv_radialMap_apply {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : N) :
    fderiv ℝ (radialMap φ) x v =
      φ (‖x‖ ^ 2) • v + (2 * deriv φ (‖x‖ ^ 2) * Inner.inner ℝ x v) • x := by
  have hscale :=
    ((hφ.differentiable (by simp) (‖x‖ ^ 2)).hasDerivAt).comp_hasFDerivAt x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := hscale.smul (hasFDerivAt_id x)
  rw [show fderiv ℝ (radialMap φ) x = _ from hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply,
    id_eq]
  congr 1
  ring_nf

/-- For a positive monotone smooth `φ` the radial map has injective derivative everywhere. -/
theorem SmoothRadial.fderiv_radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) (x : N) : Function.Injective (fderiv ℝ (radialMap φ) x) := by
  have hzero : ∀ v : N, fderiv ℝ (radialMap φ) x v = 0 → v = 0 := by
    intro v hv
    have heq := congrArg (fun w : N => Inner.inner ℝ v w) hv
    rw [fderiv_radialMap_apply hφ, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm v x, inner_zero_right] at heq
    have hd : 0 ≤ deriv φ (‖x‖ ^ 2) := hmono.deriv_nonneg
    have hnonneg : 0 ≤ 2 * deriv φ (‖x‖ ^ 2) * (Inner.inner ℝ v x) ^ 2 := by positivity
    have hterm : φ (‖x‖ ^ 2) * ‖v‖ ^ 2 ≤ 0 := by nlinarith
    have hsq : ‖v‖ ^ 2 ≤ 0 := by
      by_contra hn
      exact (not_lt_of_ge hterm) (mul_pos (hpos _) (lt_of_not_ge hn))
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  intro v w hvw
  have hsub : fderiv ℝ (radialMap φ) x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hzero (v - w) hsub)

/-- In finite dimension the derivative of such a radial map is invertible everywhere. -/
theorem SmoothRadial.isInvertible_fderiv_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) (x : N) :
    (fderiv ℝ (radialMap (N := N) φ) x).IsInvertible := by
  let L :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialMap φ) x).toLinearMap
        (fderiv_radialMap_injective hφ hpos hmono x)).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- A positive monotone smooth `φ` equal to `1` beyond radius `R` makes the radial map a
diffeomorphism of the whole space, the identity outside the ball of radius `R`.
-/
def SmoothRadial.diffeomorph {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ (radialMap (N := N) φ) := by
    intro x
    apply
      isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_radialMap hφ).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_radialMap hφ hpos hmono x
  exact
    IsLocalDiffeomorph.diffeomorph' hlocal
      ⟨radialMap_injective hpos hmono, radialMap_surjective hφ.continuous hR hout⟩

/-- The time profile `t ↦ 1 + (a - 1) smoothTransition t` of the disc shrinking, running smoothly
from `1` at time `0` to `a` at time `1`.
-/
def SmoothRadial.shrinkTimeFactor (a t : ℝ) : ℝ :=
  1 + (a - 1) * Real.smoothTransition t

/-- For `a ≤ 1` the time profile stays between `a` and `1`. -/
theorem SmoothRadial.shrinkTimeFactor_bounds {a : ℝ} (ha₁ : a ≤ 1) (t : ℝ) :
    a ≤ shrinkTimeFactor a t ∧ shrinkTimeFactor a t ≤ 1 := by
  have ht₀ := Real.smoothTransition.nonneg t
  have ht₁ := Real.smoothTransition.le_one t
  unfold shrinkTimeFactor
  constructor <;> nlinarith

/-- The time profile is `1` at time zero. -/
theorem SmoothRadial.shrinkTimeFactor_zero (a : ℝ) : shrinkTimeFactor a 0 = 1 := by
  simp only [shrinkTimeFactor, Real.smoothTransition.zero, MulZeroClass.mul_zero, add_zero]

/-- The time profile is `a` at time one. -/
theorem SmoothRadial.shrinkTimeFactor_one (a : ℝ) : shrinkTimeFactor a 1 = a := by
  simp only [shrinkTimeFactor, Real.smoothTransition.one, mul_one]
  ring

/-- The time profile is smooth. -/
theorem SmoothRadial.contDiff_shrinkTimeFactor (a : ℝ) :
    ContDiff ℝ ∞ (shrinkTimeFactor a) :=
  contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff (n := ⊤)))

/-- The radial profile of the disc shrinking: equal to `a` on the unit ball and to `1` beyond radius
`R`, interpolating smoothly in between.
-/
def DiskShrinking.scale (R a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((s - 1) / (R ^ 2 - 1))

/-- The radial profile is smooth. -/
theorem DiskShrinking.contDiff_scale (R a : ℝ) : ContDiff ℝ ∞ (scale R a) :=
  contDiff_const.add
    (contDiff_const.mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp
        ((contDiff_id.sub contDiff_const).div_const _)))

/-- The radial profile is positive. -/
theorem DiskShrinking.scale_pos {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (R s : ℝ) :
    0 < scale R a s :=
  add_pos_of_pos_of_nonneg ha (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

/-- For `1 < R` and `a ≤ 1` the radial profile is monotone. -/
theorem DiskShrinking.scale_monotone {R a : ℝ} (hR : 1 < R) (ha₁ : a ≤ 1) :
    Monotone (scale R a) := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  intro s t hst
  exact
    add_le_add_right
      (mul_le_mul_of_nonneg_left
        (Real.smoothTransition.monotone
          (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hden.le))
        (sub_nonneg.mpr ha₁))
      a

/-- On the unit ball the radial profile equals `a`. -/
theorem DiskShrinking.scale_inner {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : s ≤ 1) :
    scale R a s = a := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale,
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hden.le)]
  simp only [MulZeroClass.mul_zero, add_zero]

/-- Beyond radius `R` the radial profile equals `1`. -/
theorem DiskShrinking.scale_outer {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : R ^ 2 ≤ s) :
    scale R a s = 1 := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hden).mpr (by linarith))]
  ring

/-- The radial profile for `a = 1` is constant `1`. -/
theorem DiskShrinking.scale_one (R s : ℝ) : scale R 1 s = 1 := by
  simp only [scale, sub_self, MulZeroClass.zero_mul, add_zero]

/-- The disc-shrinking isotopy: the radial map with profile `scale R (shrinkTimeFactor a t)`, which
at time one contracts the unit ball by the factor `a` and is the identity outside the ball of
radius `R`.
-/
def DiskShrinking.family {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (R a : ℝ) (p : ℝ × N) : N :=
  SmoothRadial.radialMap (scale R (SmoothRadial.shrinkTimeFactor a p.1)) p.2

/-- The disc-shrinking isotopy is smooth in time and space. -/
theorem DiskShrinking.contMDiff_family {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ (family (N := N) R a) := by
  have ht :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => SmoothRadial.shrinkTimeFactor a p.1) :=
    (SmoothRadial.contDiff_shrinkTimeFactor a).contMDiff.comp contMDiff_fst
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × N => ‖p.2‖ ^ 2) :=
    (show ContDiff ℝ ∞ (fun x : N => ‖x‖ ^ 2) from contDiff_id.norm_sq ℝ).contMDiff.comp
      contMDiff_snd
  have hz :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × N => (‖p.2‖ ^ 2 - 1) / (R ^ 2 - 1)) :=
    by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using
      (hn.sub contMDiff_const).mul (contMDiff_const (c := (R ^ 2 - 1)⁻¹))
  exact
    (ht.add
          ((contMDiff_const.sub ht).mul
            ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp hz))).smul
      contMDiff_snd

/-- The disc-shrinking isotopy is the identity at time zero. -/
theorem DiskShrinking.family_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a : ℝ) (x : N) : family R a (0, x) = x := by
  simp only [family, SmoothRadial.shrinkTimeFactor_zero, SmoothRadial.radialMap,
    scale_one, one_smul]

/-- Each time slice of the disc-shrinking isotopy is a diffeomorphism. -/
theorem DiskShrinking.family_slices {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R a : ℝ} (hR : 1 < R) (ha : 0 < a)
    (ha₁ : a ≤ 1) (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞, ∀ x, D x = family R a (t, x) := by
  have ht := SmoothRadial.shrinkTimeFactor_bounds ha₁ t
  exact
    ⟨SmoothRadial.diffeomorph (contDiff_scale R _) (scale_pos (ha.trans_le ht.1) ht.2 R)
        (scale_monotone hR ht.2) (zero_lt_one.trans hR) (fun _ hs => scale_outer hR _ hs),
      fun _ => rfl⟩

/-- The disc-shrinking isotopy is the identity outside the ball of radius `R`, hence compactly
supported.
-/
theorem DiskShrinking.family_outer {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R : ℝ} (hR : 1 < R) (a t : ℝ) {x : N}
    (hx : R ≤ ‖x‖) : family R a (t, x) = x := by
  rw [family, SmoothRadial.radialMap,
    scale_outer hR _ ((sq_le_sq₀ (zero_lt_one.trans hR).le (norm_nonneg x)).mpr hx), one_smul]

/-- At time one the disc-shrinking isotopy is the scaling by `a` on the unit ball. -/
theorem DiskShrinking.family_one_inner {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R : ℝ} (hR : 1 < R) (a : ℝ) {x : N}
    (hx : ‖x‖ ≤ 1) : family R a (1, x) = a • x := by
  rw [family, SmoothRadial.radialMap, SmoothRadial.shrinkTimeFactor_one,
    scale_inner hR a (by nlinarith [norm_nonneg x])]

/-- The disc-shrinking isotopy fixes the origin. -/
theorem DiskShrinking.family_origin {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a t : ℝ) : family R a (t, (0 : N)) = 0 := by
  simp only [family, SmoothRadial.radialMap, smul_zero]
