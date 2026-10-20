/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Collar.SmallPerturbation

/-!
# Small weighted translations and finite composites

A slice of a Lipschitz function of two variables is Lipschitz with the same constant
(`SmallPerturbation.lipschitzWith_slice`). For a compactly supported smooth weight there is a radius
below which every translation by a weighted vector is a diffeomorphism, uniformly in the time
parameter, and the identity off the support of the weight
(`SmallPerturbation.exists_uniform_radius_bumpTranslation`).

`SmallPerturbation.composeFamily` composes the first `n` members of a family of time-dependent maps;
smoothness, being the identity at time zero, fixing the complement of a set, preserving a quantity
and being a diffeomorphism pass from the members to the composites.

Cf. Hirsch, *Differential Topology*, Ch. 2 (small perturbations of diffeomorphisms are
diffeomorphisms).

## Tags

diffeomorphism, perturbation, bump function
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- A slice of a Lipschitz function of two variables is Lipschitz with the same constant. -/
theorem SmallPerturbation.lipschitzWith_slice {E : Type*} [NormedAddCommGroup E]
    {β : ℝ × E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (t : ℝ) :
    LipschitzWith k (fun x : E => β (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β (t, x)) (β (t, y)) ≤ (k : ℝ) * Dist.dist (t, x) (t, y) := hβ.dist_le_mul _ _
    _ = (k : ℝ) * Dist.dist x y := by
      rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ Dist.dist x y)]

/-- For a compactly supported smooth weight there is a radius below which every translation by a
weighted vector is a diffeomorphism, uniformly in the time parameter, and is the identity off
the support of the weight. -/
theorem SmallPerturbation.exists_uniform_radius_bumpTranslation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : ℝ × E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ t : ℝ,
          ∀ a : E,
            ‖a‖ < ε →
              ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
                (∀ x, d x = x + β (t, x) • a) ∧ ∀ x ∉ tsupport (fun y : E => β (t, y)), d x = x :=
  by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro t a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hr : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hr
  have hslice : ContDiff ℝ ∞ (fun x : E => β (t, x)) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨bumpTranslation hslice (lipschitzWith_slice hk t) a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport (fun y : E => β (t, y)) hne)

/-- The composite of the first `n` members of a family of time-dependent maps. -/
def SmallPerturbation.composeFamily {E : Type*} (B : ℕ → ℝ × E → E) : ℕ → ℝ × E → E
  | 0, p => p.2
  | n + 1, p => B n (p.1, composeFamily B n p)

/-- A composite of smooth members of the family is smooth. -/
theorem SmallPerturbation.contDiff_composeFamily {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : ℕ → ℝ × E → E} (hB : ∀ i, ContDiff ℝ ∞ (B i)) (n : ℕ) :
    ContDiff ℝ ∞ (composeFamily B n) := by
  induction n with
  | zero => exact contDiff_snd
  | succ n ih => exact (hB n).comp (contDiff_fst.prodMk ih)

/-- If every member of the family is the identity at time zero, so is every composite. -/
theorem SmallPerturbation.composeFamily_zero {E : Type*} {B : ℕ → ℝ × E → E}
    (hB : ∀ i x, B i (0, x) = x) (n : ℕ) (x : E) : composeFamily B n (0, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n _).trans ih

/-- If every member of the family fixes the complement of a set, so does every composite. -/
theorem SmallPerturbation.composeFamily_fixed {E : Type*} {B : ℕ → ℝ × E → E} {C : Set E}
    (hB : ∀ i t x, x ∉ C → B i (t, x) = x) (n : ℕ) (t : ℝ) {x : E} (hx : x ∉ C) :
    composeFamily B n (t, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B n (t, composeFamily B n (t, x)) = x
    rw [ih]
    exact hB n t x hx

/-- A quantity preserved by every member of the family is preserved by every composite. -/
theorem SmallPerturbation.composeFamily_preserves {E : Type*} {F : Type*}
    {B : ℕ → ℝ × E → E} {f : E → F} (hB : ∀ i t x, f (B i (t, x)) = f x) (n : ℕ) (t : ℝ) (x : E) :
    f (composeFamily B n (t, x)) = f x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n t _).trans ih

/-- If every member of the family is a diffeomorphism at every time, so is every composite. -/
theorem SmallPerturbation.exists_diffeomorph_composeFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : ℕ → ℝ × E → E}
    (hB : ∀ i t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = B i (t, x)) (n : ℕ) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = composeFamily B n (t, x) := by
  induction n with
  | zero => exact ⟨Diffeomorph.refl 𝓘(ℝ, E) E ∞, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨e, he⟩ := hB n t
    refine ⟨d.trans e, ?_⟩
    intro x
    change e (d x) = B n (t, composeFamily B n (t, x))
    rw [he, hd]

end
