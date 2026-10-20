/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.PartialDiffeomorph
public import Lib.Analysis.Calculus.MorseLemma.SymmetricForm

/-!
# Smooth congruence to a nondegenerate symmetric form

Let `H : E ≃L[ℝ] (E →L[ℝ] ℝ)` be a symmetric isomorphism on a finite-dimensional real space.
Every symmetric form `A` near `H` is congruent to `H` by an operator depending smoothly on `A`:
there are an open `U ∋ H` and a smooth `L : SymmetricForm E → (E →L[ℝ] E)` with `L H = id` and
`H (L A ·) (L A ·) = A` on `U` (`SmoothMorseLemma.exists_smooth_congruence_factor`, by the
inverse function theorem applied to the congruence polynomial `S ↦ 2 S + Sym(H(H⁻¹S ·, H⁻¹S ·))`).
Combined with a smooth factorization `f x = f 0 + (1/2) A(x)(x, x)` this yields a partial
diffeomorphism `e` with `e 0 = 0`, `De(0) = id` and `f = f 0 + (1/2) H(e ·, e ·)`
(`SmoothMorseLemma.exists_quadratic_chart_of_smooth_congruence`): the coordinate-free proof of
the Morse lemma (cf. Lang, *Fundamentals of Differential Geometry*, the Morse–Palais lemma).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The Morse lemma: near a nondegenerate critical point there are coordinates in which the function is a purely quadratic form of the critical value - `f = f(p) - x_1^2 - ... - x_i^2 + x_{i+1}^2 + ...` (Morse Lemma; Milnor, Morse Theory, Lemma 2.2). -/
theorem SmoothMorseLemma.exists_quadratic_chart_of_smooth_congruence {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (A : E → SymmetricForm E) (hA : ContDiff ℝ ∞ A) (H : SymmetricForm E) (hA0 : A 0 = H)
    (hfactor : ∀ x, f x = f 0 + (1 / 2 : ℝ) * (A x).val x x) (V : Set (SymmetricForm E))
    (hV : IsOpen V) (hHV : H ∈ V) (L : SymmetricForm E → E →L[ℝ] E) (hL : ContDiffOn ℝ ∞ L V)
    (hL0 : L H = ContinuousLinearMap.id ℝ E) (hcong : ∀ B ∈ V, congruence H.val (L B) = B.val) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (0 : E) ∈ e.source ∧
        e 0 = 0 ∧
          HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
            (∀ x ∈ e.source, f x = f 0 + (1 / 2 : ℝ) * H.val (e x) (e x)) ∧
              (∀ y ∈ e.target, f (e.symm y) = f 0 + (1 / 2 : ℝ) * H.val y y) := by
  let U : Set E := A ⁻¹' V
  have hU : IsOpen U := hV.preimage hA.continuous
  have h0 : (0 : E) ∈ U := by
    change A 0 ∈ V
    rw [hA0]
    exact hHV
  have hLA : ContDiffOn ℝ ∞ (fun x => L (A x)) U := hL.comp hA.contDiffOn (fun _ hx => hx)
  let φ : E → E := fun x => L (A x) x
  have hφ : ContDiffOn ℝ ∞ φ U := hLA.clm_apply contDiffOn_id
  have hLA0 : L (A 0) = ContinuousLinearMap.id ℝ E := by rw [hA0, hL0]
  have hd : HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 := by
    have h := ((hLA.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)).hasFDerivAt
    simpa only [id_eq, hLA0, ContinuousLinearMap.comp_id, map_zero, add_zero] using
      h.clm_apply (hasFDerivAt_id (0 : E))
  obtain ⟨e, he0, heU, he⟩ :=
    exists_partialDiffeomorph_of_contDiffOn hU hφ 0 h0 (ContinuousLinearEquiv.refl ℝ E) hd
  have heφ : (e : E → E) = φ := funext he
  have hezero : e 0 = 0 := by
    rw [he]
    exact map_zero (L (A 0))
  have hnormal (x : E) (hx : x ∈ e.source) : f x = f 0 + (1 / 2 : ℝ) * H.val (e x) (e x) := by
    have hquad := congrArg (fun B : Bilinear E => B x x) (hcong (A x) (heU hx))
    change H.val (L (A x) x) (L (A x) x) = (A x).val x x at hquad
    rw [he]
    change f x = f 0 + (1 / 2 : ℝ) * H.val (L (A x) x) (L (A x) x)
    rw [hquad]
    exact hfactor x
  refine ⟨e, he0, hezero, ?_, hnormal, ?_⟩
  · rw [heφ]
    exact hd
  · intro y hy
    have hr : e (e.symm y) = y := e.right_inv hy
    simpa only [hr] using hnormal (e.symm y) (e.map_target hy)

/-- The congruence polynomial of the symmetric Taylor factor. -/
def SmoothMorseLemma.congruencePolynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (S : SymmetricForm E) : SymmetricForm E :=
  (2 : ℝ) • S + symmetrize E (congruence H.toContinuousLinearMap (raiseSymmetricIndex H S))

/-- The congruence polynomial at zero is the Hessian factor. -/
@[simp]
theorem SmoothMorseLemma.congruencePolynomial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : congruencePolynomial H 0 = 0 := by
  simp [congruencePolynomial]

/-- The congruence polynomial is smooth. -/
theorem SmoothMorseLemma.contDiff_congruencePolynomial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : ContDiff ℝ ∞ (congruencePolynomial H) :=
  (contDiff_id.const_smul (2 : ℝ)).add
    ((symmetrize E).contDiff.comp
      ((contDiff_congruence H.toContinuousLinearMap).comp (raiseSymmetricIndex H).contDiff))

/-- The congruence polynomial has invertible derivative at zero. -/
theorem SmoothMorseLemma.hasFDerivAt_congruencePolynomial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    HasFDerivAt (congruencePolynomial H) ((2 : ℝ) • ContinuousLinearMap.id ℝ (SymmetricForm E))
      0 := by
  have hc :
    HasFDerivAt (congruence H.toContinuousLinearMap) (0 : (E →L[ℝ] E) →L[ℝ] Bilinear E)
      (raiseSymmetricIndex H (0 : SymmetricForm E)) := by
    simpa only [map_zero] using hasFDerivAt_congruence_zero H.toContinuousLinearMap
  have hq := hc.comp (0 : SymmetricForm E) (raiseSymmetricIndex H).hasFDerivAt
  have hs := (symmetrize E).hasFDerivAt.comp (0 : SymmetricForm E) hq
  have h := ((hasFDerivAt_id (0 : SymmetricForm E)).const_smul (2 : ℝ)).add hs
  convert h using 1 <;>
    first
    | rfl
    | simp

/-- The reference symmetric form of the Hessian. -/
def SmoothMorseLemma.referenceSymmetricForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u) : SymmetricForm E :=
  ⟨H.toContinuousLinearMap, hH⟩

/-- The reference form evaluates the Hessian. -/
@[simp]
theorem SmoothMorseLemma.referenceSymmetricForm_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u) (u v : E) :
    (referenceSymmetricForm H hH).val u v = H u v :=
  rfl

/-- The congruence polynomial shifted by the reference form. -/
theorem SmoothMorseLemma.congruencePolynomial_add_reference {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u)
    (S : SymmetricForm E) :
    (congruencePolynomial H S + referenceSymmetricForm H hH).val =
      congruence H.toContinuousLinearMap (ContinuousLinearMap.id ℝ E + raiseSymmetricIndex H S) :=
  by
  ext u v
  have hcross : H u (H.symm (S.val v)) = S.val u v := by
    rw [hH, H.apply_symm_apply, S.property v u]
  have hquad :
    H (H.symm (S.val v)) (H.symm (S.val u)) = H (H.symm (S.val u)) (H.symm (S.val v)) := hH _ _
  have hquad' : S.val v (H.symm (S.val u)) = S.val u (H.symm (S.val v)) := by
    simpa only [H.apply_symm_apply] using hquad
  simp only [congruencePolynomial, Submodule.coe_add, Submodule.coe_smul, add_apply, smul_apply,
    smul_eq_mul, symmetrize_apply, congruence_apply, raiseSymmetricIndex_apply,
    referenceSymmetricForm_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    map_add, hcross, H.apply_symm_apply, hquad']
  ring

/-- The double congruence equivalence of the Taylor factor. -/
def SmoothMorseLemma.congruenceDoubleEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    SymmetricForm E ≃L[ℝ] SymmetricForm E :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SymmetricForm E)
    (Units.mk0 (2 : ℝ) (by norm_num))

/-- The double congruence equivalence computes the map. -/
theorem SmoothMorseLemma.congruenceDoubleEquiv_toContinuousLinearMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (congruenceDoubleEquiv E).toContinuousLinearMap =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (SymmetricForm E) := by
  ext S
  rfl

/-- The congruence polynomial gives a partial diffeomorphism. -/
theorem SmoothMorseLemma.exists_congruencePolynomial_partialDiffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ∃ e :
      PartialDiffeomorph 𝓘(ℝ, SymmetricForm E) 𝓘(ℝ, SymmetricForm E) (SymmetricForm E)
        (SymmetricForm E) ∞,
      (0 : SymmetricForm E) ∈ e.source ∧ ∀ S, e S = congruencePolynomial H S := by
  apply
    exists_partialDiffeomorph_of_contDiff (contDiff_congruencePolynomial H) 0
      (congruenceDoubleEquiv E)
  rw [congruenceDoubleEquiv_toContinuousLinearMap]
  exact hasFDerivAt_congruencePolynomial_zero H

/-- A smooth congruence factor trivializing the Taylor factor exists. -/
theorem SmoothMorseLemma.exists_smooth_congruence_factor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hH : ∀ u v, H u v = H v u) :
    ∃ U : Set (SymmetricForm E),
      IsOpen U ∧
        referenceSymmetricForm H hH ∈ U ∧
          ∃ L : SymmetricForm E → (E →L[ℝ] E),
            ContDiffOn ℝ ∞ L U ∧
              L (referenceSymmetricForm H hH) = ContinuousLinearMap.id ℝ E ∧
                ∀ A ∈ U, congruence H.toContinuousLinearMap (L A) = A.val := by
  obtain ⟨e, he0, he⟩ := exists_congruencePolynomial_partialDiffeomorph H
  have he_zero : e (0 : SymmetricForm E) = 0 := by rw [he, congruencePolynomial_zero]
  have hzero_target : (0 : SymmetricForm E) ∈ e.target := by
    simpa only [he_zero] using e.toPartialEquiv.map_source he0
  have he_symm_zero : e.invFun (0 : SymmetricForm E) = 0 := by
    have h := e.toPartialEquiv.left_inv he0
    change e.invFun (e.toFun 0) = 0 at h
    change e.toFun 0 = 0 at he_zero
    rwa [he_zero] at h
  let U : Set (SymmetricForm E) := (fun A => A - referenceSymmetricForm H hH) ⁻¹' e.target
  let L : SymmetricForm E → (E →L[ℝ] E) := fun A =>
    ContinuousLinearMap.id ℝ E +
      raiseSymmetricIndex H (e.invFun (A - referenceSymmetricForm H hH))
  have hU : IsOpen U := e.open_target.preimage (continuous_id.sub continuous_const)
  have hHU : referenceSymmetricForm H hH ∈ U := by
    simpa only [U, Set.mem_preimage, sub_self] using hzero_target
  have hinv : ContDiffOn ℝ ∞ (fun A => e.invFun (A - referenceSymmetricForm H hH)) U :=
    e.contMDiffOn_invFun.contDiffOn.comp (contDiff_id.sub contDiff_const).contDiffOn
      (fun _ hA => hA)
  refine ⟨U, hU, hHU, L, ?_, ?_, ?_⟩
  · exact contDiffOn_const.add ((raiseSymmetricIndex H).contDiff.comp_contDiffOn hinv)
  · simp only [L, sub_self, he_symm_zero, map_zero, add_zero]
  · intro A hA
    have hq :
      congruencePolynomial H (e.invFun (A - referenceSymmetricForm H hH)) =
        A - referenceSymmetricForm H hH := by
      rw [← he]
      exact e.toPartialEquiv.right_inv hA
    change
      congruence H.toContinuousLinearMap
          (ContinuousLinearMap.id ℝ E +
            raiseSymmetricIndex H (e.invFun (A - referenceSymmetricForm H hH))) =
        A.val
    rw [← congruencePolynomial_add_reference H hH, hq, sub_add_cancel]
