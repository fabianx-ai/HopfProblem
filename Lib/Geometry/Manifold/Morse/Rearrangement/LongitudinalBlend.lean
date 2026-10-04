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
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative
public import Lib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Morse.Rearrangement.HeightCoordinates
public import Lib.Geometry.Manifold.Morse.Rearrangement.IntervalTranslation
/-!
# Longitudinal blending in a tube

Given a profile `D : ℝ → ℝ`, a transverse cutoff `β : V → ℝ` and a time cutoff `η : ℝ → ℝ`,
`MorseCancellation.longitudinalBlend D β η (t, (s, z)) = (s + η t * β z * (D s - s), z)`
moves the longitudinal coordinate `s` towards `D s`, weighted by `η t * β z`. It is smooth
(`longitudinalBlend_smooth`), the identity at time `0` when `η 0 = 0` (`longitudinalBlend_zero`)
and outside `Icc l u ×ˢ tsupport β` when `D` is fixed outside `Ioo l u`
(`longitudinalBlend_fixed_outside`). When `0 < deriv D` and `η`, `β` take values in `[0, 1]`
the longitudinal derivative `1 + η t * β z * (deriv D s - 1)` stays positive
(`longitudinalBlend_derivative_positive`), so by `RegularHeightCoordinates.longitudinalDiffeomorph`
every time slice is a diffeomorphism of `ℝ × V` (`longitudinalBlend_slices`).

This is the model isotopy that pushes a point along the axis of a tube while fixing everything
outside a compact box (Milnor, *Lectures on the h-cobordism theorem*, §4 and §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Longitudinal blending -/

/-- The longitudinal displacement of a blended height. -/
def MorseCancellation.longitudinalBlendDisplacement {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (t : ℝ) (p : ℝ × V) : ℝ :=
  η t * β p.2 * (D p.1 - p.1)

/-- The longitudinal blend diffeomorphism of the tube. -/
def MorseCancellation.longitudinalBlend {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (p : ℝ × (ℝ × V)) : ℝ × V :=
  (p.2.1 + longitudinalBlendDisplacement D β η p.1 p.2, p.2.2)

/-- The blend displacement is smooth. -/
theorem MorseCancellation.longitudinalBlendDisplacement_smooth {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (t : ℝ) : ContDiff ℝ ∞ (longitudinalBlendDisplacement D β η t) :=
  (contDiff_const.mul (hβ.comp contDiff_snd)).mul ((hD.comp contDiff_fst).sub contDiff_fst)

/-- The longitudinal blend is smooth. -/
theorem MorseCancellation.longitudinalBlend_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β)
    (hη : ContDiff ℝ ∞ η) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ × V) ∞ (longitudinalBlend D β η) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ) ∞ Prod.fst := contDiff_fst.contMDiff
  have hz : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, V) ∞ Prod.snd := contDiff_snd.contMDiff
  have hs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × (ℝ × V) => p.2.1) :=
    hs.comp contMDiff_snd
  have hz' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, V) ∞ (fun p : ℝ × (ℝ × V) => p.2.2) :=
    hz.comp contMDiff_snd
  exact
    (hs'.add
          (((hη.contMDiff.comp contMDiff_fst).mul (hβ.contMDiff.comp hz')).mul
            ((hD.contMDiff.comp hs').sub hs'))).prodMk_space
      hz'

/-- At cutoff zero the blend is the identity. -/
theorem MorseCancellation.longitudinalBlend_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hη : η 0 = 0) (p : ℝ × V) :
    longitudinalBlend D β η (0, p) = p := by
  simp only [longitudinalBlend, longitudinalBlendDisplacement, hη, MulZeroClass.zero_mul,
    add_zero]

/-- The displacement vanishes outside the support. -/
theorem MorseCancellation.longitudinalBlendDisplacement_zero_outside {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlendDisplacement D β η t p = 0 := by
  by_cases hs : p.1 ∈ Set.Icc l u
  · have hb : β p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨hs, h⟩)
    simp only [longitudinalBlendDisplacement, hb, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · have hd := hfix p.1 (fun h => hs ⟨h.1.le, h.2.le⟩)
    simp only [longitudinalBlendDisplacement, hd, sub_self, MulZeroClass.mul_zero]

/-- The blend is fixed outside the support. -/
theorem MorseCancellation.longitudinalBlend_fixed_outside {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlend D β η (t, p) = p := by
  rw [longitudinalBlend, longitudinalBlendDisplacement_zero_outside η hfix t p hp, add_zero]

/-- The blend has positive longitudinal derivative. -/
theorem MorseCancellation.longitudinalBlend_derivative_positive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hDpos : ∀ s, 0 < deriv D s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (p : ℝ × V) :
    0 <
      fderiv ℝ
        (RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hscalar :=
    RegularHeightCoordinates.scalar_derivative
      (RegularHeightCoordinates.contDiff_displacedHeight hu) p.1 p.2
  have hd :=
    (hasDerivAt_id p.1).add
      (((hD.differentiable (by simp) p.1).hasDerivAt.sub (hasDerivAt_id p.1)).const_mul
        (η t * β p.2))
  have hrate :
    fderiv ℝ
        (RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) =
      1 + (η t * β p.2) * (deriv D p.1 - 1) :=
    hscalar.deriv.symm.trans hd.deriv
  rw [hrate]
  have hweight : η t * β p.2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hηrange t).1 (hβrange p.2).1,
      mul_le_one₀ (hηrange t).2 (hβrange p.2).1 (hβrange p.2).2⟩
  have hpos := MorseRearrangement.positive_blended_slope hweight (hDpos p.1) zero_lt_one
  nlinarith

/-- The blend preserves the transverse slices. -/
theorem MorseCancellation.longitudinalBlend_slices {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} {l u : ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hDpos : ∀ s, 0 < deriv D s)
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞,
      ∀ p, d p = longitudinalBlend D β η (t, p) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hcompact : HasCompactSupport (longitudinalBlendDisplacement D β η t) :=
    HasCompactSupport.intro (CompactIccSpace.isCompact_Icc.prod hc.isCompact)
      (longitudinalBlendDisplacement_zero_outside η hfix t)
  exact
    ⟨RegularHeightCoordinates.longitudinalDiffeomorph hu hcompact
        (longitudinalBlend_derivative_positive hD hβ hDpos hβrange hηrange t),
      fun _ => rfl⟩
