/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Continuous symmetric bilinear forms and congruence

For a real normed space `E`: the space `Bilinear E = E →L[ℝ] E →L[ℝ] ℝ` of continuous bilinear
forms, its submodule `symmetricForms E` of symmetric forms, the symmetrization projection
`B ↦ (B + Bᵀ)/2`, the congruence action `congruence B L = B (L ·) (L ·)` (smooth in `L`, with
zero derivative at `L = 0`), and raising an index along an isomorphism `E ≃L[ℝ] E →L[ℝ] ℝ`.

This is a continuous-linear-map version of part of `LinearMap.BilinForm` / `LinearMap.IsSymm`,
kept in this form because the Morse lemma needs the topology on the space of forms.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The space of continuous bilinear forms. -/
abbrev SmoothMorseLemma.Bilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

/-- The submodule of symmetric bilinear forms. -/
def SmoothMorseLemma.symmetricForms (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (Bilinear E)
    where
  carrier := {B | ∀ u v, B u v = B v u}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro B C hB hC u v
    change B u v + C u v = B v u + C v u
    rw [hB u v, hC u v]
  smul_mem' := by
    intro c B hB u v
    change c * B u v = c * B v u
    rw [hB u v]

/-- A symmetric continuous bilinear form. -/
abbrev SmoothMorseLemma.SymmetricForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  symmetricForms E

/-- Symmetric forms equal on diagonal inputs are equal. -/
@[ext]
theorem SmoothMorseLemma.symmetricForm_ext (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : SymmetricForm E} (h : ∀ u v, S.val u v = T.val u v) : S = T :=
  Subtype.ext (ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => h u v)

/-- The flipped bilinear form. -/
def SmoothMorseLemma.flipBilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Bilinear E →L[ℝ] Bilinear E :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The symmetrization of a bilinear form. -/
def SmoothMorseLemma.symmetrize (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Bilinear E →L[ℝ] SymmetricForm E :=
  (((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (Bilinear E) + flipBilinear E)).codRestrict
    (symmetricForms E)
    (fun B u v => by
      change (2 : ℝ)⁻¹ * (B u v + B v u) = (2 : ℝ)⁻¹ * (B v u + B u v)
      ring)

/-- Symmetrization averages the form and its flip. -/
@[simp]
theorem SmoothMorseLemma.symmetrize_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) (u v : E) : (symmetrize E B).val u v = (2 : ℝ)⁻¹ * (B u v + B v u) :=
  rfl

/-- The congruence action of a linear map on a bilinear form. -/
def SmoothMorseLemma.congruence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) (L : E →L[ℝ] E) : Bilinear E :=
  B.bilinearComp L L

/-- Congruence evaluates the form on the transformed vectors. -/
@[simp]
theorem SmoothMorseLemma.congruence_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) (L : E →L[ℝ] E) (u v : E) : congruence B L u v = B (L u) (L v) :=
  rfl

/-- Congruence at the zero map is zero. -/
@[simp]
theorem SmoothMorseLemma.congruence_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) : congruence B (0 : E →L[ℝ] E) = 0 := by
  ext u v
  simp [congruence]

/-- Congruence is smooth in the transforming map. -/
theorem SmoothMorseLemma.contDiff_congruence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) : ContDiff ℝ ∞ (congruence B) := by
  have h₁ : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => B.comp L) := contDiff_const.clm_comp contDiff_id
  have h₂ : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => (B.comp L).flip) :=
    (flipBilinear E).contDiff.comp h₁
  exact (flipBilinear E).contDiff.comp (h₂.clm_comp contDiff_id)

/-- A linear equivalence raises a form to an operator. -/
def SmoothMorseLemma.raiseIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : Bilinear E →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E H.symm.toContinuousLinearMap

/-- A symmetric form raises to a self-adjoint operator. -/
def SmoothMorseLemma.raiseSymmetricIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : SymmetricForm E →L[ℝ] (E →L[ℝ] E) :=
  (raiseIndex H).comp (symmetricForms E).subtypeL

/-- The raised symmetric form evaluates the form. -/
@[simp]
theorem SmoothMorseLemma.raiseSymmetricIndex_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (S : SymmetricForm E) (u : E) :
    raiseSymmetricIndex H S u = H.symm (S.val u) :=
  rfl

/-- The derivative of congruence at zero. -/
theorem SmoothMorseLemma.hasFDerivAt_congruence_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : Bilinear E) :
    HasFDerivAt (congruence B) (0 : (E →L[ℝ] E) →L[ℝ] Bilinear E) 0 := by
  have h₁ := (hasFDerivAt_const B (0 : E →L[ℝ] E)).clm_comp (hasFDerivAt_id (0 : E →L[ℝ] E))
  have h₂ := (flipBilinear E).hasFDerivAt.comp 0 h₁
  have h₃ := h₂.clm_comp (hasFDerivAt_id (0 : E →L[ℝ] E))
  have h₄ := (flipBilinear E).hasFDerivAt.comp 0 h₃
  convert h₄ using 1 <;>
    first
    | rfl
    | simp
