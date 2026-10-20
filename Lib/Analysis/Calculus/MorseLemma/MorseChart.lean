/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.Cutoff
public import Lib.Analysis.Calculus.MorseLemma.PartialDiffeomorph
public import Lib.Analysis.Calculus.MorseLemma.SymmetricForm
public import Lib.Analysis.Calculus.MorseLemma.TaylorFactor
public import Lib.Analysis.Calculus.MorseLemma.Congruence
public import Lib.Analysis.Calculus.MorseLemma.SignedCoordinates
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The Morse lemma in a finite-dimensional normed space

Let `f` be `C^∞` on an open set `U` of a finite-dimensional real normed space `E` and let
`a ∈ U` be a nondegenerate critical point (`Df(a) = 0`, `D²f(a)` bijective). Then there is a
partial diffeomorphism `e` defined near `a`, with `e a = 0` and `De(a) = id`, in which
`f = f a + (1/2) D²f(a)(e ·, e ·)` (`SmoothMorseLemma.exists_morse_chart_of_contDiffOn`), and,
after Sylvester's diagonalization, coordinates in which `f = f a + ∑ i, w i * y i ^ 2` with
`w i ∈ {-1, 1}` (`SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn`).

This is the Morse lemma (Milnor, *Morse Theory*, Lemma 2.2).

## References

* [John Milnor, *Morse Theory*][milnor63], Lemma 2.2
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The Hessian equivalence at a Morse critical point. -/
def SmoothMorseLemma.hessianEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (a : E)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ f) a).toLinearMap hn).toContinuousLinearEquiv

/-- A Morse chart centered at zero exists near a critical point. -/
theorem SmoothMorseLemma.exists_morse_chart_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : fderiv ℝ f 0 = 0) (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (0 : E) ∈ e.source ∧
        e 0 = 0 ∧
          HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
            (∀ x ∈ e.source, f x = f 0 + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 (e x) (e x)) ∧
              (∀ y ∈ e.target, f (e.symm y) = f 0 + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 y y) := by
  let H := hessianEquiv f 0 hn
  have hH : ∀ u v, H u v = H v u := by
    intro u v
    have hs := (symmetricTaylorFactor f 0).property u v
    rw [symmetricTaylorFactor_zero hf] at hs
    exact hs
  obtain ⟨V, hV, hHV, L, hL, hL0, hcong⟩ := exists_smooth_congruence_factor H hH
  have hA0 : symmetricTaylorFactor f 0 = referenceSymmetricForm H hH := by
    apply Subtype.ext
    exact symmetricTaylorFactor_zero hf
  obtain ⟨e, he0, hezero, hederiv, hnormal, hinverse⟩ :=
    exists_quadratic_chart_of_smooth_congruence f (symmetricTaylorFactor f)
      (contDiff_symmetricTaylorFactor hf) (referenceSymmetricForm H hH) hA0
      (map_eq_add_symmetricTaylorFactor hf hc) V hV hHV L hL hL0 hcong
  exact ⟨e, he0, hezero, hederiv, hnormal, hinverse⟩

/-- The Hessian is unchanged by adding a constant. -/
theorem SmoothMorseLemma.hessian_comp_add_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (a x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (a + y))) x = fderiv ℝ (fderiv ℝ f) (a + x) := by
  have h : fderiv ℝ (fun y => f (a + y)) = fun y => fderiv ℝ f (a + y) :=
    funext fun y => fderiv_comp_add_left a
  rw [h, fderiv_comp_add_left]

/-- A Morse chart exists near a Morse critical point. -/
theorem SmoothMorseLemma.exists_morse_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧
        e a = 0 ∧
          HasFDerivAt e (ContinuousLinearMap.id ℝ E) a ∧
            (∀ x ∈ e.source, f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x)) ∧
              (∀ y ∈ e.target, f (e.symm y) = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a y y) := by
  let g : E → ℝ := fun x => f (a + x)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hgc : fderiv ℝ g 0 = 0 := by simpa only [g, fderiv_comp_add_left, add_zero] using hc
  have hgn : Function.Bijective (fderiv ℝ (fderiv ℝ g) 0) := by
    simpa only [g, hessian_comp_add_left, add_zero] using hn
  obtain ⟨e, he0, hezero, hederiv, hnormal, _⟩ := exists_morse_chart_zero hg hgc hgn
  let φ := translateChart a e
  have haφ : a ∈ φ.source := by
    change a ∈ (translateChart a e).source
    rw [mem_translateChart_source, sub_self]
    exact he0
  have hφzero : φ a = 0 := by
    change e (a - a) = 0
    rw [sub_self, hezero]
  have hφderiv : HasFDerivAt φ (ContinuousLinearMap.id ℝ E) a := by
    have hφfun : (φ : E → E) = fun x => e (x - a) := funext (translateChart_apply a e)
    rw [hφfun]
    have hdshift : HasFDerivAt (fun x : E => x - a) (ContinuousLinearMap.id ℝ E) a :=
      (hasFDerivAt_id a).sub_const a
    have hdouter : HasFDerivAt e (ContinuousLinearMap.id ℝ E) (a - a) := by
      simpa only [sub_self] using hederiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      hdouter.comp (f := fun x : E => x - a) a hdshift
  have hφnormal (x : E) (hx : x ∈ φ.source) :
    f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (φ x) (φ x) := by
    have hx' : x - a ∈ e.source := (mem_translateChart_source a e x).mp hx
    have hpoint : a + (x - a) = x := by simp [sub_eq_add_neg]
    simpa only [g, hessian_comp_add_left, add_zero, hpoint, φ, translateChart_apply] using
      hnormal (x - a) hx'
  refine ⟨φ, haφ, hφzero, hφderiv, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

/-- A Morse chart exists for a `C^n` function on a set. -/
theorem SmoothMorseLemma.exists_morse_chart_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (a : E) (ha : a ∈ U) (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧
        e.source ⊆ U ∧
          e a = 0 ∧
            HasFDerivAt e (ContinuousLinearMap.id ℝ E) a ∧
              (∀ x ∈ e.source, f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x)) ∧
                (∀ y ∈ e.target,
                  f (e.symm y) = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a y y) := by
  obtain ⟨g, hg, heq, hga, hdf, hH, _⟩ :=
    exists_contDiff_extension_preserving_derivatives hf hU ha
  have hgc : fderiv ℝ g a = 0 := hdf.trans hc
  have hgn : Function.Bijective (fderiv ℝ (fderiv ℝ g) a) := by
    rw [hH]
    exact hn
  obtain ⟨e, hea, hezero, hederiv, hnormal, _⟩ := exists_morse_chart hg a hgc hgn
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds ha) heq)
  let φ := restrictChart e W hWopen
  have haφ : a ∈ φ.source := ⟨hea, haW⟩
  have hφU : φ.source ⊆ U := fun _ hx => (hWsub hx.2).1
  have hφnormal (x : E) (hx : x ∈ φ.source) :
    f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (φ x) (φ x) := by
    have hxeq : g x = f x := (hWsub hx.2).2
    simpa only [φ, restrictChart_apply, hxeq, hga, hH] using hnormal x hx.1
  refine ⟨φ, haφ, hφU, hezero, hederiv, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

/-- The Hessian of a `C^n` function is symmetric. -/
theorem SmoothMorseLemma.hessian_symmetric_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {U : Set E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {a : E}
    (ha : a ∈ U) (u v : E) : fderiv ℝ (fderiv ℝ f) a u v = fderiv ℝ (fderiv ℝ f) a v u := by
  have hs :=
    (hf.contDiffAt (hU.mem_nhds ha)).isSymmSndFDerivAt
      (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  exact hs u v

/-- A signed Morse chart exists for a `C^n` function. -/
theorem SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (a : E) (ha : a ∈ U) (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ e :
          PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) E
            (Fin (Module.finrank ℝ E) → ℝ) ∞,
          a ∈ e.source ∧
            e.source ⊆ U ∧
              e a = 0 ∧
                (∀ x ∈ e.source, f x = f a + ∑ i, w i * (e x i) ^ 2) ∧
                  (∀ y ∈ e.target, f (e.symm y) = f a + ∑ i, w i * y i ^ 2) := by
  obtain ⟨e, hea, heU, hezero, _, hnormal, _⟩ := exists_morse_chart_of_contDiffOn hf hU a ha hc hn
  obtain ⟨w, hw, C, hCzero, hC⟩ :=
    exists_signed_diffeomorph (fderiv ℝ (fderiv ℝ f) a) (hessian_symmetric_of_contDiffOn hf hU ha)
      hn
  let φ := e.trans C.toPartialDiffeomorph
  have hsource : φ.source = e.source := by
    ext x
    change (x ∈ e.source ∧ e x ∈ (Set.univ : Set E)) ↔ x ∈ e.source
    simp only [Set.mem_univ, and_true]
  have haφ : a ∈ φ.source := hsource ▸ hea
  have hφU : φ.source ⊆ U := hsource ▸ heU
  have hφzero : φ a = 0 := by
    change C (e a) = 0
    rw [hezero, hCzero]
  have hφnormal (x : E) (hx : x ∈ φ.source) : f x = f a + ∑ i, w i * (φ x i) ^ 2 := by
    have hx' : x ∈ e.source := hsource ▸ hx
    calc
      f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x) := hnormal x hx'
      _ = f a + ∑ i, w i * (C (e x) i) ^ 2 := by rw [hC]
      _ = f a + ∑ i, w i * (φ x i) ^ 2 := rfl
  refine ⟨w, hw, φ, haφ, hφU, hφzero, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)
