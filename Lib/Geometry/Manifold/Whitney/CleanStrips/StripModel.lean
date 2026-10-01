/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.CircleGluing

/-!
# The linear model of a strip chart

The model space of a strip chart is `StripCoordinates.Space A B = (ℝ × A) × B`: a line (the time
of the strip), a factor `A` completing it to a sheet, and a normal factor `B`. A strip map
`F : ℝ × ℝ → Space A B` restricting to the centre line `t ↦ ((t, 0), 0)` on the axis has
horizontal derivative `center 1`; if moreover its normal derivative (the derivative of the normal
component in the vertical direction) is nonzero, its derivative is injective along the axis.

The file contains:

* the flat model `(t, s) ↦ ((t, 0), s • v t)` and the interpolation `StripCoordinates.blend` of two
  strip maps by cut-off functions of the time, which keeps the centre line and the normal
  derivative `v`;
* the injectivity criteria for linear maps `ℝ × ℝ → Space A B`, and the transverse inclusion
  `a ↦ ((0, a), 0)` of the sheet directions, which meets the image of an immersed strip only at
  `0`;
* the detector `(t, s) ↦ (t, ⟪v t, (F (t, s)).2⟫)`, a planar map with injective derivative along
  the axis wherever `v ≠ 0`.

This is the linear algebra behind the strip neighbourhoods of the Whitney trick (Milnor,
*Lectures on the h-cobordism theorem*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- Partial derivative in the first variable: if `F : ℝ × ℝ → E` is differentiable at `(t, s)`, then
the horizontal slice `u ↦ F (u, s)` has derivative `fderiv ℝ F (t, s) (1, 0)` at `t`.
-/
theorem StripCoordinates.hasDerivAt_horizontalSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℝ × ℝ) → E} {t s : ℝ} (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (u, s)) (fderiv ℝ F (t, s) (1, 0)) t := by
  have hi : HasDerivAt (fun u : ℝ => (u, s)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  exact hF.hasFDerivAt.comp_hasDerivAt t hi

/-- The model space of a strip chart: a line, a transverse factor `A` along the sheet, and a normal
factor `B`.
-/
abbrev StripCoordinates.Space (A B : Type*) :=
  (ℝ × A) × B

/-- The centre line `t ↦ ((t, 0), 0)` of a strip chart. -/
def StripCoordinates.center {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (t : ℝ) : Space A B :=
  ((t, 0), 0)

/-- The flat strip model `(t, s) ↦ ((t, 0), s • v t)`: the centre line together with the normal
field `v`.
-/
def StripCoordinates.model {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (v : ℝ → B) (p : ℝ × ℝ) : Space A B :=
  ((p.1, 0), p.2 • v p.1)

/-- The normal derivative of a strip map at time `t`: the derivative of its normal component in the
vertical direction at `(t, 0)`.
-/
def StripCoordinates.normalDerivative {A B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : (ℝ × ℝ) → Space A B) (t : ℝ) : B :=
  fderiv ℝ (fun p => (F p).2) (t, 0) (0, 1)

/-- The interpolation of two strip maps with the flat model, using the two cut-off functions `β₀`
and `β₁` of the time parameter; it equals `F₀` where `β₀ = 1` and `β₁ = 0`, and `F₁` where the
two are exchanged.
-/
def StripCoordinates.blend {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (F₀ F₁ : (ℝ × ℝ) → Space A B)
    (β₀ β₁ : ℝ → ℝ) (p : ℝ × ℝ) : Space A B :=
  model v p + β₀ p.1 • (F₀ p - model v p) + β₁ p.1 • (F₁ p - model v p)

/-- The flat strip model is smooth when the normal field is. -/
theorem StripCoordinates.contDiff_model {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (model (A := A) v) :=
  (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.smul (hv.comp contDiff_fst))

/-- The interpolation of two strip maps is smooth when its ingredients are. -/
theorem StripCoordinates.contDiff_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (blend v F₀ F₁ β₀ β₁) :=
  ((contDiff_model hv).add ((hβ₀.comp contDiff_fst).smul (hF₀.sub (contDiff_model hv)))).add
    ((hβ₁.comp contDiff_fst).smul (hF₁.sub (contDiff_model hv)))

/-- The flat strip model restricts to the centre line on the axis. -/
theorem StripCoordinates.model_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (t : ℝ) :
    model (A := A) v (t, 0) = StripCoordinates.center t := by
  simp only [model, StripCoordinates.center, zero_smul]

/-- The interpolation still restricts to the centre line on the axis, provided each of the two maps
does wherever its cut-off is nonzero.
-/
theorem StripCoordinates.blend_zero {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {β₀ β₁ : ℝ → ℝ} (h₀ : ∀ t, β₀ t ≠ 0 → F₀ (t, 0) = StripCoordinates.center t)
    (h₁ : ∀ t, β₁ t ≠ 0 → F₁ (t, 0) = StripCoordinates.center t) (t : ℝ) :
    blend v F₀ F₁ β₀ β₁ (t, 0) = StripCoordinates.center t := by
  have hterm₀ : β₀ t • (F₀ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, model_zero, sub_self, smul_zero]
  have hterm₁ : β₁ t • (F₁ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, model_zero, sub_self, smul_zero]
  change
    model v (t, 0) + β₀ t • (F₀ (t, 0) - model v (t, 0)) + β₁ t • (F₁ (t, 0) - model v (t, 0)) =
      StripCoordinates.center t
  rw [hterm₀, hterm₁, add_zero, add_zero, model_zero]

/-- Where the first cut-off is `1` and the second `0` the interpolation equals the first map. -/
theorem StripCoordinates.blend_eq_left {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 1)
    (h₁ : β₁ p.1 = 0) : blend v F₀ F₁ β₀ β₁ p = F₀ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

/-- Where the first cut-off is `0` and the second `1` the interpolation equals the second map. -/
theorem StripCoordinates.blend_eq_right {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 0)
    (h₁ : β₁ p.1 = 1) : blend v F₀ F₁ β₀ β₁ p = F₁ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

/-- The interpolation has normal derivative `v` at every time, provided each of the two maps does
wherever its cut-off is nonzero.
-/
theorem StripCoordinates.normalDerivative_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (h₀ : ∀ t, β₀ t ≠ 0 → normalDerivative F₀ t = v t)
    (h₁ : ∀ t, β₁ t ≠ 0 → normalDerivative F₁ t = v t) (t : ℝ) :
    normalDerivative (blend v F₀ F₁ β₀ β₁) t = v t := by
  have hm : HasDerivAt (fun s : ℝ => s • v t) (v t) 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (v t)
  have hd₀ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₀.snd.contDiffAt.differentiableAt (by simp))
  have hd₁ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₁.snd.contDiffAt.differentiableAt (by simp))
  have hterm₀ : β₀ t • (normalDerivative F₀ t - v t) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, sub_self, smul_zero]
  have hterm₁ : β₁ t • (normalDerivative F₁ t - v t) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, sub_self, smul_zero]
  have hblend :
    HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2)
      (v t + β₀ t • (normalDerivative F₀ t - v t) + β₁ t • (normalDerivative F₁ t - v t)) 0 :=
    HasDerivAt.add (HasDerivAt.add hm (HasDerivAt.const_smul (β₀ t) (HasDerivAt.sub hd₀ hm)))
      (HasDerivAt.const_smul (β₁ t) (HasDerivAt.sub hd₁ hm))
  have hblend' : HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2) (v t) 0 := by
    simpa only [hterm₀, hterm₁, add_zero] using hblend
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_blend hv hF₀ hF₁ hβ₀ hβ₁).snd.contDiffAt.differentiableAt (by simp))).unique
      hblend'

/-- A strip map whose restriction to the axis is the centre line has horizontal derivative
`center 1` at each point of the axis.
-/
theorem StripCoordinates.horizontal_derivative_of_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : ∀ s, F (s, 0) = StripCoordinates.center s) :
    fderiv ℝ F (t, 0) (1, 0) = StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have heq : (fun s : ℝ => F (s, 0)) = StripCoordinates.center := funext hc
  rw [heq] at hd
  have hcenter :
    HasDerivAt (StripCoordinates.center : ℝ → Space A B) (StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique hcenter

/-- The same conclusion under the weaker hypothesis that the restriction to the axis agrees with the
centre line only near `t`.
-/
theorem StripCoordinates.horizontal_derivative_of_center_germ {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : (fun s : ℝ => F (s, 0)) =ᶠ[𝓝 t] StripCoordinates.center) :
    fderiv ℝ F (t, 0) (1, 0) = StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have hcenter :
    HasDerivAt (StripCoordinates.center : ℝ → Space A B) (StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique (hcenter.congr_of_eventuallyEq hc)

/-- The normal derivative is the normal component of the vertical derivative. -/
theorem StripCoordinates.normalDerivative_eq_snd_fderiv {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) : normalDerivative F t = (fderiv ℝ F (t, 0) (0, 1)).2 := by
  have hd := hF.hasFDerivAt.snd
  rw [normalDerivative, hd.fderiv]
  rfl

/-- A linear map `ℝ × ℝ → Space A B` sending `(1, 0)` to `center 1` and having nonzero normal
component on `(0, 1)` is injective.
-/
theorem StripCoordinates.injective_of_horizontal_and_normal {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : (ℝ × ℝ) →L[ℝ] Space A B) (hh : L (1, 0) = StripCoordinates.center 1)
    (hn : (L (0, 1)).2 ≠ 0) : Function.Injective L := by
  have hker : ∀ p : ℝ × ℝ, L p = 0 → p = 0 := by
    rintro ⟨a, b⟩ hp
    have hsplit : (a, b) = a • ((1 : ℝ), 0) + b • (0, 1) := by ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hh] at hp
    have hb0 : b • (L (0, 1)).2 = 0 := by
      simpa [StripCoordinates.center] using congrArg Prod.snd hp
    have hb : b = 0 := (smul_eq_zero.mp hb0).resolve_right hn
    subst b
    have ha : a = 0 := by
      simpa [StripCoordinates.center] using congrArg (fun q : Space A B => q.1.1) hp
    subst a
    rfl
  intro p q hpq
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hpq, sub_self]

/-- A strip map restricting to the centre line on the axis and with nonvanishing normal derivative
at `t` has injective derivative at `(t, 0)`; so it is an immersion along the centre line.
-/
theorem StripCoordinates.injective_fderiv_at_center {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) (hc : ∀ s, F (s, 0) = StripCoordinates.center s)
    (hn : normalDerivative F t ≠ 0) : Function.Injective (fderiv ℝ F (t, 0)) := by
  apply
    injective_of_horizontal_and_normal (fderiv ℝ F (t, 0)) (horizontal_derivative_of_center hF hc)
  rwa [← normalDerivative_eq_snd_fderiv hF]

/-- The inclusion `a ↦ ((0, a), 0)` of the transverse factor of the sheet into the strip model
space.
-/
def StripCoordinates.sheetTransverseInclusion {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] : A →L[ℝ] Space A B :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B).comp (ContinuousLinearMap.inr ℝ ℝ A)

/-- The value of the transverse inclusion: `a ↦ ((0, a), 0)`. -/
theorem StripCoordinates.sheetTransverseInclusion_apply {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (a : A) :
    (sheetTransverseInclusion : A →L[ℝ] Space A B) a = ((0, a), 0) :=
  rfl

/-- The transverse directions of the sheet meet the image of an immersed strip only at the origin.
-/
theorem StripCoordinates.sheetTransverse_eq_strip_iff {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (L : (ℝ × ℝ) →L[ℝ] Space A B)
    (hh : L (1, 0) = StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0) (a : A)
    (p : ℝ × ℝ) : sheetTransverseInclusion a = L p ↔ a = 0 ∧ p = 0 := by
  constructor
  · intro heq
    have hsplit : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
    have hexp : L p = p.1 • StripCoordinates.center 1 + p.2 • L (0, 1) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_smul, hh]
    rw [hexp] at heq
    have hp2zero : p.2 • (L (0, 1)).2 = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        (congrArg Prod.snd heq).symm
    have hp2 : p.2 = 0 := (smul_eq_zero.mp hp2zero).resolve_right hn
    rw [hp2, zero_smul, add_zero] at heq
    have hp1 : p.1 = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        (congrArg (fun q : Space A B => q.1.1) heq).symm
    have ha : a = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.2) heq
    exact ⟨ha, Prod.ext hp1 hp2⟩
  · rintro ⟨rfl, rfl⟩
    rw [map_zero, map_zero]

/-- If `Q` has kernel exactly the image of the strip differential, then `Q` is injective on the
transverse factor of the sheet; the transverse directions map isomorphically onto the normal
quotient.
-/
theorem StripCoordinates.injective_sheetTransverse_normalQuotient {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : Space A B →L[ℝ] Z)
    (hh : L (1, 0) = StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0)
    (hker : Q.ker = L.range) : Function.Injective (Q.comp sheetTransverseInclusion) := by
  have hz : ∀ a : A, Q (sheetTransverseInclusion a) = 0 → a = 0 := by
    intro a ha
    have hmem : sheetTransverseInclusion a ∈ L.range := by
      rw [← hker]
      exact ha
    obtain ⟨p, hp⟩ := hmem
    exact ((sheetTransverse_eq_strip_iff L hh hn a p).mp hp.symm).1
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  change (Q.comp sheetTransverseInclusion) (a - b) = 0
  rw [map_sub, hab, sub_self]

/-- Kernels and images transport along an injective map: if `Q` has kernel the image of `T ∘ L`,
then `Q ∘ T` has kernel the image of `L`.
-/
theorem StripCoordinates.ker_comp_eq_range_of_injective {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Space A B →L[ℝ] V) (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : V →L[ℝ] Z)
    (hT : Function.Injective T) (hker : Q.ker = (T.comp L).range) : (Q.comp T).ker = L.range := by
  ext v
  constructor
  · intro hv
    have hmem : T v ∈ (T.comp L).range := by
      rw [← hker]
      exact hv
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hT hp⟩
  · rintro ⟨p, rfl⟩
    have hmem : T (L p) ∈ Q.ker := by
      rw [hker]
      exact ⟨p, rfl⟩
    exact hmem

/-- A linear endomorphism of the plane fixing `(1, 0)` and with nonzero second component on `(0, 1)`
is injective.
-/
theorem StripCoordinates.injective_plane_of_horizontal_and_normal
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hh : L (1, 0) = (1, 0)) (hn : (L (0, 1)).2 ≠ 0) :
    Function.Injective L := by
  let i : (ℝ × ℝ) →L[ℝ] Space ℝ ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hh' : (i.comp L) (1, 0) = StripCoordinates.center 1 := by
    change i (L (1, 0)) = StripCoordinates.center 1
    rw [hh]
    rfl
  have hi := injective_of_horizontal_and_normal (i.comp L) hh' hn
  intro p q hpq
  exact hi (congrArg i hpq)

/-- The detector map `(t, s) ↦ (t, ⟪v t, (F (t, s)).2⟫)` of a strip map, which records the time and
the component of the normal part along the normal field `v`.
-/
def StripCoordinates.detector {A B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (v : ℝ → B) (F : (ℝ × ℝ) → Space A B) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, ⟪v p.1, (F p).2⟫_ℝ)

/-- The detector map is smooth when the normal field and the strip map are. -/
theorem StripCoordinates.contDiff_detector {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (detector v F) :=
  contDiff_fst.prodMk ((hv.comp contDiff_fst).inner ℝ hF.snd)

/-- A strip map through the centre line has detector vanishing on the axis. -/
theorem StripCoordinates.detector_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (t : ℝ) :
    detector v F (t, 0) = (t, 0) := by
  simp only [detector, hc, StripCoordinates.center, inner_zero_right]

/-- The vertical derivative of the detector at a point of the axis is `(0, ‖v t‖²)`. -/
theorem StripCoordinates.detector_vertical_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hn : ∀ t, normalDerivative F t = v t) (t : ℝ) :
    fderiv ℝ (detector v F) (t, 0) (0, 1) = (0, ⟪v t, v t⟫_ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => (F (t, s)).2) (v t) 0 := by
    have h :=
      hasDerivAt_verticalSlice (t := t) (s := 0) (hF.snd.contDiffAt.differentiableAt (by simp))
    change HasDerivAt _ (normalDerivative F t) 0 at h
    rwa [hn t] at h
  have hinner : HasDerivAt (fun s : ℝ => ⟪v t, (F (t, s)).2⟫_ℝ) (⟪v t, v t⟫_ℝ) 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) (v t)).inner ℝ hd
  have hslice : HasDerivAt (fun s : ℝ => detector v F (t, s)) (0, ⟪v t, v t⟫_ℝ) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk hinner
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_detector hv hF).contDiffAt.differentiableAt (by simp))).unique
      hslice

/-- The detector of a strip map through the centre line with normal derivative `v` has injective
derivative wherever `v` does not vanish.
-/
theorem StripCoordinates.injective_fderiv_detector_at_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    {v : ℝ → B} {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (hn : ∀ t, normalDerivative F t = v t)
    {t : ℝ} (ht : v t ≠ 0) : Function.Injective (fderiv ℝ (detector v F) (t, 0)) := by
  have hQ : DifferentiableAt ℝ (detector v F) (t, 0) :=
    (contDiff_detector hv hF).contDiffAt.differentiableAt (by simp)
  have hh : fderiv ℝ (detector v F) (t, 0) (1, 0) = (1, 0) := by
    have hd := hasDerivAt_horizontalSlice hQ
    have heq : (fun s : ℝ => detector v F (s, 0)) = fun s => (s, 0) := funext (detector_zero hc)
    rw [heq] at hd
    exact hd.unique ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ)))
  apply injective_plane_of_horizontal_and_normal _ hh
  rw [detector_vertical_derivative hv hF hn t]
  exact inner_self_ne_zero.mpr ht

end
