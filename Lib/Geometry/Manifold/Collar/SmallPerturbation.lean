/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Small perturbations of the identity are diffeomorphisms

If `u : E → E` is Lipschitz with constant `k < 1` on a complete normed group, then `x ↦ x + u x`
is a bijection (Banach fixed point theorem); if moreover `E` is a finite-dimensional real normed
space and `u` is smooth, it is a diffeomorphism (`SmallPerturbation.diffeomorphIdAdd`). The
special case `u x = β x • a` with `β` a compactly supported smooth function and `a` a small
vector is the bump translation `SmallPerturbation.bumpTranslation`: a diffeomorphism equal to the
translation by `a` where `β = 1` and to the identity off the support of `β`
(`SmallPerturbation.exists_radius_bumpTranslation`). Cf. Hirsch, *Differential Topology*,
Ch. 2, §1 (diffeomorphisms form an open set).

## Tags

diffeomorphism, Lipschitz perturbation, bump function
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

/-! ### Small perturbations of the identity -/

/-- The identity plus a small map is injective. -/
theorem SmallPerturbation.injective_id_add {E : Type*} [NormedAddCommGroup E] {u : E → E}
    {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) : Function.Injective (fun x => x + u x) :=
  (AntilipschitzWith.id.add_lipschitzWith hu (by simpa only [inv_one] using hk)).injective

/-- The identity plus a small map is surjective. -/
theorem SmallPerturbation.surjective_id_add {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Function.Surjective (fun x => x + u x) := by
  intro y
  have hlip : LipschitzWith k (fun x => y - u x) := by
    simpa only [zero_add] using (LipschitzWith.const y).sub hu
  have hc : ContractingWith k (fun x => y - u x) := ⟨hk, hlip⟩
  let x := ContractingWith.fixedPoint (fun x => y - u x) hc
  refine ⟨x, ?_⟩
  have hx : y - u x = x := hc.fixedPoint_isFixedPt.eq
  exact eq_sub_iff_add_eq.mp hx.symm

/-- The identity plus a small map is bijective. -/
theorem SmallPerturbation.bijective_id_add {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Function.Bijective (fun x => x + u x) :=
  ⟨injective_id_add hu hk, surjective_id_add hu hk⟩

/-- The identity plus a small map has invertible derivative. -/
theorem SmallPerturbation.isInvertible_fderiv_id_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → E} {k : ℝ≥0} (hs : ContDiff ℝ ∞ u)
    (hu : LipschitzWith k u) (hk : k < 1) (x : E) :
    (fderiv ℝ (fun y => y + u y) x).IsInvertible := by
  have hn : ‖fderiv ℝ u x‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ hu).trans_lt (show (k : ℝ) < 1 from hk)
  have hnn : ‖fderiv ℝ u x‖₊ < 1 := hn
  have hi : Function.Injective (ContinuousLinearMap.id ℝ E + fderiv ℝ u x) :=
    injective_id_add (fderiv ℝ u x).lipschitz hnn
  have hd : fderiv ℝ (fun y => y + u y) x = ContinuousLinearMap.id ℝ E + fderiv ℝ u x :=
    ((hasFDerivAt_id x).add (hs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hd]
  let L :=
    (LinearEquiv.ofInjectiveEndo (ContinuousLinearMap.id ℝ E + fderiv ℝ u x).toLinearMap
        hi).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- The identity plus a small map is a diffeomorphism. -/
def SmallPerturbation.diffeomorphIdAdd {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → E} {k : ℝ≥0} (hs : ContDiff ℝ ∞ u)
    (hu : LipschitzWith k u) (hk : k < 1) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := by
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x => x + u x) := by
    intro x
    apply
      isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_id.add hs).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_id_add hs hu hk x
  exact hloc.diffeomorphOfBijective' (bijective_id_add hu hk)

/-- A scaled constant is Lipschitz. -/
theorem SmallPerturbation.lipschitzWith_smul_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {β : E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (a : E) :
    LipschitzWith (k * ‖a‖₊) (fun x => β x • a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β x • a) (β y • a) = ‖β x - β y‖ * ‖a‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul]
    _ ≤ ((k : ℝ) * Dist.dist x y) * ‖a‖ :=
      (mul_le_mul_of_nonneg_right (hβ.dist_le_mul x y) (norm_nonneg a))
    _ = (k * ‖a‖₊ : ℝ≥0) * Dist.dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

/-- The bump translation diffeomorphism. -/
def SmallPerturbation.bumpTranslation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β) (hβ : LipschitzWith k β)
    (a : E) (ha : k * ‖a‖₊ < 1) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphIdAdd (hs.smul contDiff_const) (lipschitzWith_smul_const hβ a) ha

/-- The bump translation computes the shifted point. -/
theorem SmallPerturbation.bumpTranslation_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) (x : E) :
    bumpTranslation hs hβ a ha x = x + β x • a := by
  have h : bumpTranslation hs hβ a ha x = x + β x • a := rfl
  exact h

/-- The bump translation is the identity where the bump vanishes. -/
theorem SmallPerturbation.bumpTranslation_eq_of_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) {x : E} (hx : β x = 0) :
    bumpTranslation hs hβ a ha x = x := by rw [bumpTranslation_apply, hx, zero_smul, add_zero]

/-- A radius for which the bump translation exists. -/
theorem SmallPerturbation.exists_radius_bumpTranslation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} (hs : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
              (∀ x, d x = x + β x • a) ∧ ∀ x ∉ tsupport β, d x = x := by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hreal : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hreal
  refine ⟨bumpTranslation hs hk a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport β hne)
