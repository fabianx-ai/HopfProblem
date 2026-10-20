/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle

/-!
# Linear perturbations and the Morse condition in a vector space

For a smooth `f : E → ℝ` on a finite-dimensional real space, `MorsePerturbation.IsMorse f`
says that every critical point has bijective Hessian. Identifying `E` with its dual by a basis
(`dualEquiv`), the linear perturbation `f - ⟨a, ·⟩` is Morse whenever `a` is a regular value of
the coordinate gradient of `f` (`isMorse_of_regularValue`; by Sard's theorem almost every `a`).
The nondegeneracy condition "`Df ≠ 0` or `D²f` bijective" is open in parametrized families
(`isOpen_goodJetOn`), and an open condition holding on a compact set holds on a neighbourhood of
the parameter (`isOpen_forall_mem_compact`, the tube lemma).

These are the local steps of the existence of Morse functions (Milnor, *Lectures on the
h-cobordism theorem*, Theorem 2.5; cf. Milnor, *Morse Theory*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The linear equivalence between the space and its dual given by a basis. -/
def MorsePerturbation.dualEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : E ≃L[ℝ] (E →L[ℝ] ℝ) := by
  classical
    exact
    ((Module.Basis.ofVectorSpace ℝ E).toDualEquiv.trans
        LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

/-- The gradient of a function in dual coordinates. -/
def MorsePerturbation.coordinateGradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ) (x : E) : E :=
  dualEquiv.symm (fderiv ℝ f x)

/-- A linear perturbation of a function by a dual vector. -/
def MorsePerturbation.linearPerturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ) (a : E) (x : E) : ℝ :=
  f x - dualEquiv a x

/-- A function is Morse if `0` is a regular value of its coordinate gradient. -/
def MorsePerturbation.IsMorse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) : Prop :=
  ∀ x, fderiv ℝ f x = 0 → Function.Bijective (fderiv ℝ (fderiv ℝ f) x)

/-- The derivative of a `C^n` function is `C^(n−1)`. -/
theorem MorsePerturbation.contDiff_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.fderiv_right (by simp)

/-- The coordinate gradient of a `C^n` function is `C^(n−1)`. -/
theorem MorsePerturbation.contDiff_coordinateGradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordinateGradient f) :=
  dualEquiv.symm.contDiff.comp (contDiff_fderiv hf)

/-- The derivative of a linear perturbation shifts by the dual vector. -/
theorem MorsePerturbation.fderiv_linearPerturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E) :
    fderiv ℝ (linearPerturbation f a) x = fderiv ℝ f x - dualEquiv a := by
  unfold linearPerturbation
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (dualEquiv a).differentiableAt,
    ContinuousLinearMap.fderiv]

/-- A linear perturbation does not change the Hessian. -/
theorem MorsePerturbation.hessian_linearPerturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E) :
    fderiv ℝ (fderiv ℝ (linearPerturbation f a)) x = fderiv ℝ (fderiv ℝ f) x := by
  have heq : fderiv ℝ (linearPerturbation f a) = fun y => fderiv ℝ f y - dualEquiv a :=
    funext (fderiv_linearPerturbation hf a)
  rw [heq, fderiv_sub_const]

/-- The derivative of the coordinate gradient is the Hessian. -/
theorem MorsePerturbation.fderiv_coordinateGradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    fderiv ℝ (coordinateGradient f) x =
      dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
  exact
    (dualEquiv.symm.hasFDerivAt.comp x
        ((contDiff_fderiv hf).differentiable (by simp) x).hasFDerivAt).fderiv

/-- Regularity of the gradient at `0` gives the Morse condition. -/
theorem MorsePerturbation.isMorse_of_regularValue {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {a : E}
    (ha : a ∈ RegularValues.regularValues (coordinateGradient f)) :
    IsMorse (linearPerturbation f a) := by
  intro x hx
  rw [fderiv_linearPerturbation hf a x, sub_eq_zero] at hx
  have hxa : coordinateGradient f x = a := by simp [coordinateGradient, hx]
  have hbij := RegularValues.bijective_fderiv_of_mem_regularValues ha hxa
  rw [hessian_linearPerturbation hf a x]
  have heq :
    (fun v : E => dualEquiv (fderiv ℝ (coordinateGradient f) x v)) = fderiv ℝ (fderiv ℝ f) x := by
    funext v
    rw [fderiv_coordinateGradient hf x]
    exact dualEquiv.apply_symm_apply _
  rw [← heq]
  exact dualEquiv.bijective.comp hbij

/-- An open property holding on a compact set holds on a neighborhood. -/
theorem MorsePerturbation.isOpen_forall_mem_compact {P X : Type*} [TopologicalSpace P]
    [TopologicalSpace X] {K : Set X} (hK : IsCompact K) {U : Set (P × X)} (hU : IsOpen U) :
    IsOpen {p : P | ∀ x ∈ K, (p, x) ∈ U} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let B : Set (P × K) := {q | (q.1, (q.2 : X)) ∉ U}
  have hB : IsClosed B :=
    hU.isClosed_compl.preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hproj : IsClosed ((Prod.fst : P × K → P) '' B) := isClosedMap_fst_of_compactSpace B hB
  have heq : {p : P | ∀ x ∈ K, (p, x) ∈ U} = ((Prod.fst : P × K → P) '' B)ᶜ := by
    ext p
    constructor
    · intro hp ⟨⟨q, x⟩, hbad, hq⟩
      change q = p at hq
      subst q
      exact hbad (hp x x.property)
    · intro hp x hx
      by_contra hbad
      exact hp ⟨(p, ⟨x, hx⟩), hbad, rfl⟩
  rw [heq]
  exact hproj.isOpen_compl

/-- The spatial derivative of a parametric `C^n` family is `C^(n−1)`. -/
theorem MorsePerturbation.contDiff_spatialDerivative {P E F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : P → E → F} (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun q : P × E => fderiv ℝ (f q.1) q.2) := by
  let g : (P × E) → E → F := fun q x => f q.1 x
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hg.fderiv contDiff_snd (by simp)

/-- The Hessian is bijective exactly at Morse points. -/
theorem MorsePerturbation.bijective_hessian_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] (E →L[ℝ] ℝ)) :
    Function.Bijective A ↔ (dualEquiv.symm.toContinuousLinearMap.comp A).det ≠ 0 := by
  rw [← RegularValues.bijective_iff_det_ne_zero]
  constructor
  · intro hA
    exact dualEquiv.symm.bijective.comp hA
  · intro hA
    have heq : (fun x : E => dualEquiv ((dualEquiv.symm.toContinuousLinearMap.comp A) x)) = A := by
      funext x
      exact dualEquiv.apply_symm_apply _
    rw [← heq]
    exact dualEquiv.bijective.comp hA

/-- The spatial derivative is `C^(n−1)` at a point. -/
theorem MorsePerturbation.contDiffAt_spatialDerivative {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P → E → F} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) q) :
    ContDiffAt ℝ ∞ (fun r : P × E => fderiv ℝ (f r.1) r.2) q := by
  let g : (P × E) → E → F := fun r x => f r.1 x
  have hg : ContDiffAt ℝ ∞ (Function.uncurry g) (q, q.2) :=
    hf.comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hg.fderiv contDiffAt_snd (by simp)

/-- The spatial derivative is `C^(n−1)` on a set. -/
theorem MorsePerturbation.contDiffOn_spatialDerivative {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P → E → F} {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) U) :
    ContDiffOn ℝ ∞ (fun q : P × E => fderiv ℝ (f q.1) q.2) U := by
  intro q hq
  exact (contDiffAt_spatialDerivative (hf.contDiffAt (hU.mem_nhds hq))).contDiffWithinAt

/-- The good-jet condition is open. -/
theorem MorsePerturbation.isOpen_goodJetOn {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : P → E → ℝ} {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) U) :
    IsOpen
      {q : P × E |
        q ∈ U ∧
          (fderiv ℝ (f q.1) q.2 ≠ 0 ∨ Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1)) q.2))} := by
  have h₁ := contDiffOn_spatialDerivative hU hf
  have h₂ := contDiffOn_spatialDerivative (f := fun p x => fderiv ℝ (f p) x) hU h₁
  have hd :
    ContinuousOn
      (fun q : P × E =>
        (dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det)
      U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.clm_comp h₂.continuousOn)
  have ha :=
    h₁.continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  have hb := hd.isOpen_inter_preimage hU (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  have heq :
    {q : P × E |
        q ∈ U ∧
          (fderiv ℝ (f q.1) q.2 ≠ 0 ∨ Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1)) q.2))} =
      (U ∩ (fun q : P × E => fderiv ℝ (f q.1) q.2) ⁻¹' {0}ᶜ) ∪
        (U ∩
          (fun q : P × E =>
              (dualEquiv.symm.toContinuousLinearMap.comp
                  (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det) ⁻¹'
            {0}ᶜ) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff, bijective_hessian_iff]
    exact and_or_left
  rw [heq]
  exact ha.union hb

/-- The Hessian as a continuous linear equivalence at a Morse point. -/
def MorsePerturbation.hessianEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (x : E)
    (h : Function.Bijective (fderiv ℝ (fderiv ℝ f) x)) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ f) x).toLinearMap h).toContinuousLinearEquiv

/-- The Hessian equivalence computes the Hessian. -/
@[simp]
theorem MorsePerturbation.hessianEquiv_toContinuousLinearMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ) (x : E)
    (h : Function.Bijective (fderiv ℝ (fderiv ℝ f) x)) :
    (hessianEquiv f x h).toContinuousLinearMap = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  rfl
