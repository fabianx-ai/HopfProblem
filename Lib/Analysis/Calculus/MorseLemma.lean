/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The Morse lemma and the signed Morse chart

At a nondegenerate critical point of a `C^∞` function there are charts in which the function
is a signed sum of squares (Milnor, Morse Theory, Lemma 2.2). The headline statement:

* `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn` — existence of the signed Morse
  chart around a critical point.

The file also carries the perturbation machinery feeding it and the existence of Morse
functions on compact manifolds (`ManifoldMorse.exists_morse_function`, Milnor
h-cobordism Thm 2.5): `MorsePerturbation.*`, `ManifoldPerturbation.perturb`,
`ManifoldMorse.IsMorseOn`, `exists_compact_plateau`, `exists_morse_extension`,
`exists_morse_function_of_haar`, and the parametrized-integral tools
(`contDiff_parametric_intervalIntegral*`).

## Outline of the proof

1. *Perturbations.*  `dualEquiv`, `coordinateGradient`, `linearPerturbation`;
   `coordinateVector`, `perturb`, `contMDiff_perturb`.
2. *Morse-ness is open.*  `IsMorseOn`, `contDiffOn_chartExpression`, `exists_compact_plateau`,
   `exists_morse_extension`, `exists_morse_function_of_haar`, `exists_morse_function`.
3. *The Morse lemma.*  `translationToZero`, `translateChart` (+ `_apply`, `_source`),
   `restrictChart`, and the parametrized-integral form culminating in
   `exists_signed_morse_chart_of_contDiffOn`.

## Main definitions and results

* `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn` : the signed Morse chart.
* `ManifoldMorse.exists_morse_function` : existence of Morse functions.

## References

* [John Milnor, *Morse Theory*][milnor63], Lemma 2.2
* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], Theorem 2.5

## Tags

Morse lemma, signed chart, Morse function existence
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped ContDiff Convolution

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Linear perturbations and the Morse condition -/

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

/-! ### Manifold perturbations -/

/-- A coordinate vector field on a chart. -/
def ManifoldPerturbation.coordinateVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (x : M) : E :=
  φ x • extChartAt 𝓘(ℝ, E) p x

/-- The coordinate vector field is smooth. -/
theorem ManifoldPerturbation.contMDiff_coordinateVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (coordinateVector φ) :=
  φ.contMDiff_smul contMDiffOn_extChartAt

/-- The perturbation of a manifold function by a parameter. -/
def ManifoldPerturbation.perturb {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (f : M → ℝ) (a : E) (x : M) : ℝ :=
  f x - MorsePerturbation.dualEquiv a (coordinateVector φ x)

/-- The perturbation is jointly smooth. -/
theorem ManifoldPerturbation.contMDiff_perturb {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (fun q : E × M => perturb φ f q.1 q.2) :=
  (hf.comp contMDiff_snd).sub
    ((MorsePerturbation.dualEquiv.contDiff.contMDiff.comp contMDiff_fst).clm_apply
      ((contMDiff_coordinateVector φ).comp contMDiff_snd))

/-- The zero perturbation is the original function. -/
@[simp]
theorem ManifoldPerturbation.perturb_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (f : M → ℝ) : perturb φ f 0 = f := by
  funext x
  simp [perturb]

/-- Being Morse at a point: the point is a nondegenerate critical point of `f` - the Hessian there is a nondegenerate quadratic form (Milnor, Morse Theory, Section 2). -/
def ManifoldMorse.IsMorseAt (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (x : M) : Prop :=
  ∃ e : OpenPartialHomeomorph M E,
    e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      x ∈ e.source ∧
        (fderiv ℝ (f ∘ e.symm) (e x) ≠ 0 ∨
          Function.Bijective (fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)))

/-- Being Morse on a set: `f` is Morse at every point of the set (all critical points in the set are nondegenerate). -/
def ManifoldMorse.IsMorseOn (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (K : Set M) : Prop :=
  ∀ x ∈ K, IsMorseAt E f x

/-- Being a Morse function: `f` is smooth and all its critical points are nondegenerate (Milnor, Morse Theory, Section 2). -/
def ManifoldMorse.IsMorse (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : Prop :=
  ∀ x, IsMorseAt E f x

/-! ### Morse points on a manifold -/

/-- The Morse-on predicate is preserved under unions. -/
theorem ManifoldMorse.IsMorseOn.union {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {K L : Set M}
    (hK : ManifoldMorse.IsMorseOn E f K) (hL : ManifoldMorse.IsMorseOn E f L) :
    ManifoldMorse.IsMorseOn E f (K ∪ L) := by
  intro x hx
  rcases hx with hx | hx
  · exact hK x hx
  · exact hL x hx

/-- The chart expression of a smooth function is smooth. -/
theorem ManifoldMorse.contDiffOn_chartExpression {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
  (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn

/-- Morse at a point transfers across an eventual chart equality. -/
theorem ManifoldMorse.isMorseAt_of_chart_eventuallyEq {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {g : E → ℝ} {x : M} {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hx : x ∈ e.source)
    (hg : MorsePerturbation.IsMorse g) (heq : f ∘ e.symm =ᶠ[𝓝 (e x)] g) : IsMorseAt E f x :=
  by
  refine ⟨e, he, hx, ?_⟩
  by_cases hc : fderiv ℝ (f ∘ e.symm) (e x) = 0
  · right
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    exact hg (e x) ((heq.fderiv_eq (𝕜 := ℝ)).symm.trans hc)
  · exact Or.inl hc

/-- The function expressed in a chart is smooth on the chart domain. -/
theorem ManifoldMorse.contDiffOn_inChart {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (fun q : P × E => f q.1 (e.symm q.2)) {q : P × E | q.2 ∈ e.target} := by
  intro q hq
  have hi := contMDiffAt_symm_of_mem_maximalAtlas he hq
  have hmap :
    ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞ (fun r : P × E => (r.1, e.symm r.2)) q :=
    contDiffAt_fst.contMDiffAt.prodMk (hi.comp q contDiffAt_snd.contMDiffAt)
  exact (hf.contMDiffAt.comp q hmap).contDiffAt.contDiffWithinAt

/-- Morse-in-chart points form an open set. -/
theorem ManifoldMorse.isOpen_morseInChart {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen
      {q : P × M |
        q.2 ∈ e.source ∧
          (fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0 ∨
            Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1 ∘ e.symm)) (e q.2)))} := by
  have hg :=
    MorsePerturbation.isOpen_goodJetOn (f := fun a y => f a (e.symm y))
      (e.open_target.preimage (continuous_snd : Continuous (Prod.snd : P × E → E)))
      (contDiffOn_inChart hf he)
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, S]
  constructor
  · rintro ⟨hq, hg⟩
    exact ⟨hq, e.map_source hq, hg⟩
  · rintro ⟨hq, -, hg⟩
    exact ⟨hq, hg⟩

/-- Morse points form an open set. -/
theorem ManifoldMorse.isOpen_isMorseAt {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | IsMorseAt E (f q.1) q.2} := by
  have heq :
    {q : P × M | IsMorseAt E (f q.1) q.2} =
      ⋃ (e : OpenPartialHomeomorph M E) (_ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M),
        {q : P × M |
          q.2 ∈ e.source ∧
            (fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0 ∨
              Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1 ∘ e.symm)) (e q.2)))} := by
    ext q
    simp only [Set.mem_ofPred_eq, IsMorseAt, Set.mem_iUnion, exists_prop]
  rw [heq]
  exact isOpen_iUnion fun e => isOpen_iUnion fun he => isOpen_morseInChart hf he

/-- The Morse-on locus is open. -/
theorem ManifoldMorse.isOpen_isMorseOn {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) {K : Set M}
    (hK : IsCompact K) : IsOpen {p : P | IsMorseOn E (f p) K} :=
  MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_isMorseAt hf)

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

/-- The critical-point set of a Morse function: the set of points where the differential vanishes (Milnor, Morse Theory, Section 2). -/
def ManifoldMorse.criticalPoints {M : Type*} [TopologicalSpace M] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M] (f : M → ℝ) : Set M :=
  {x | mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0}

/-- A point is critical exactly when its chart derivative vanishes. -/
theorem ManifoldMorse.mem_criticalPoints_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : M} (hx : x ∈ e.source) :
    x ∈ criticalPoints E f ↔ fderiv ℝ (f ∘ e.symm) (e x) = 0 := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hcomp :
    fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e x) (hf.mdifferentiableAt (by simp))
        (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  rw [hcomp]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 ↔ _
  constructor
  · intro h
    rw [h]
    ext v
    rfl
  · intro h
    ext v
    obtain ⟨w, hw⟩ := he'.symm.mfderiv_surjective (e.map_source hx) v
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A w) h
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) w) = 0 at hh
    rw [hw] at hh
    exact hh

/-- The critical points are closed. -/
theorem ManifoldMorse.criticalPoints_isClosed {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) : IsClosed (criticalPoints E f) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hxS : x ∈ e.source := mem_chart_source E x
  have hd := (contDiffOn_chartExpression hf he).fderiv_of_isOpen e.open_target (m := ∞) (by simp)
  let V : Set E := e.target ∩ (fderiv ℝ (f ∘ e.symm)) ⁻¹' {0}ᶜ
  have hV : IsOpen V :=
    hd.continuousOn.isOpen_inter_preimage e.open_target
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  have hU := e.continuousOn.isOpen_inter_preimage e.open_source hV
  have hxU : x ∈ e.source ∩ e ⁻¹' V :=
    ⟨hxS, e.map_source hxS, fun h => hx ((mem_criticalPoints_iff hf he hxS).mpr h)⟩
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy hc
  exact hy.2.2 ((mem_criticalPoints_iff hf he hy.1).mp hc)

/-- The critical points of a Morse function form a discrete set: nondegeneracy forces the Hessian to be invertible there (Milnor, Morse Theory, Section 2). -/
theorem ManifoldMorse.criticalPoints_isDiscrete {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) : IsDiscrete (criticalPoints E f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc : fderiv ℝ (f ∘ e.symm) (e x) = 0 := (mem_criticalPoints_iff hf he hxS).mp hx
    have hloc :=
      (contDiffOn_chartExpression hf he).contDiffAt (e.open_target.mem_nhds (e.map_source hxS))
    have hdf := hloc.fderiv_right (m := ∞) (by simp)
    let L := MorsePerturbation.hessianEquiv (f ∘ e.symm) (e x) hH
    have hL : HasFDerivAt (fderiv ℝ (f ∘ e.symm)) L.toContinuousLinearMap (e x) := by
      rw [show L.toContinuousLinearMap = fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x) from
          MorsePerturbation.hessianEquiv_toContinuousLinearMap _ _ hH]
      exact (hdf.differentiableAt (by simp)).hasFDerivAt
    let d := hdf.toOpenPartialHomeomorph (fderiv ℝ (f ∘ e.symm)) hL (by simp)
    have hd : e x ∈ d.source := hdf.mem_toOpenPartialHomeomorph_source hL (by simp)
    let U := e.source ∩ e ⁻¹' d.source
    have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source d.open_source
    refine ⟨U, hU, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyc⟩
      apply Set.mem_singleton_iff.mpr
      apply e.injOn hy.1 hxS
      apply d.injOn hy.2 hd
      exact ((mem_criticalPoints_iff hf he hy.1).mp hyc).trans hc.symm
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨⟨hxS, hd⟩, hx⟩

/-- A Morse function on a compact manifold has finitely many critical points: discrete plus compact equals finite - the counting tool behind the surgery windows (Milnor, Morse Theory, Section 2). -/
theorem ManifoldMorse.finite_criticalPoints {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) : (criticalPoints E f).Finite :=
  (criticalPoints_isClosed hf).isCompact.finite (criticalPoints_isDiscrete hf hm)

/-! ### Descent and prescribed-derivative fields -/

/-- A chart coordinate direction field. -/
def FlowConstruction.chartDirection {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (e : OpenPartialHomeomorph M E) (w : E) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e (fun y => (NormedSpace.fromTangentSpace y).symm w)

/-- The chart direction field is smooth on the chart domain. -/
theorem FlowConstruction.contMDiffOn_chartDirection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, chartDirection e w x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  have hW :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y : E => (⟨y, (NormedSpace.fromTangentSpace y).symm w⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x).IsInvertible := ⟨he'.mfderiv hx, rfl⟩
  exact
    ((hW (e x)).mpullback_vectorField_preimage (contMDiffAt_of_mem_maximalAtlas he hx) hinv
        (by simp)).contMDiffWithinAt

/-- The chart direction differentiates the function as the derivative component. -/
theorem FlowConstruction.mvfderiv_chartDirection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (chartDirection e w x) = fderiv ℝ (f ∘ e.symm) (e x) w := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have h₁ := he'.comp_symm_deriv (e.map_source hx)
  rw [e.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he'.symm_comp_deriv hx)
  have hc :
    fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e x) (hf.mdifferentiableAt (by simp))
        (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  unfold chartDirection
  rw [VectorField.mpullback_apply, hi]
  exact (congrArg (fun A : E →L[ℝ] ℝ => A w) hc).symm

/-- Near a regular point there is a unit-speed field. -/
theorem FlowConstruction.exists_unitSpeedField_near_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {p : M} (hp : p ∉ ManifoldMorse.criticalPoints E f) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧
          ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
            ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
              ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) f x (V x) = 1 := by
  classical
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hpS : p ∈ e.source := mem_chart_source E p
  have hdf : fderiv ℝ (f ∘ e.symm) (e p) ≠ 0 := fun h =>
    hp ((ManifoldMorse.mem_criticalPoints_iff hf he hpS).mpr h)
  have hw : ∃ w : E, fderiv ℝ (f ∘ e.symm) (e p) w ≠ 0 := by
    by_contra! h
    exact hdf (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hw
  let D : M → ℝ := fun x => fderiv ℝ (f ∘ e.symm) (e x) w
  have hder :=
    (ManifoldMorse.contDiffOn_chartExpression hf he).fderiv_of_isOpen e.open_target (m := ∞)
      (by simp)
  have hD : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D e.source :=
    (hder.clm_apply contDiffOn_const).contMDiffOn.comp (contMDiffOn_of_mem_maximalAtlas he)
      (fun _ hx => e.map_source hx)
  let U : Set M := e.source ∩ D ⁻¹' {0}ᶜ
  have hU : IsOpen U :=
    hD.continuousOn.isOpen_inter_preimage e.open_source
      (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  let V : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => (D x)⁻¹ • chartDirection e w x
  refine ⟨U, hU, ⟨hpS, hw⟩, V, ?_, ?_⟩
  · exact
      ((hD.mono Set.inter_subset_left).inv₀ (fun _ hx => hx.2)).smul_section
        ((contMDiffOn_chartDirection he w).mono Set.inter_subset_left)
  · intro x hx
    change mvfderiv 𝓘(ℝ, E) f x ((D x)⁻¹ • chartDirection e w x) = 1
    rw [map_smul, smul_eq_mul, mvfderiv_chartDirection hf he w hx.1]
    exact inv_mul_cancel₀ hx.2

/-- Near a regular point a prescribed nonzero derivative field exists. -/
theorem FlowConstruction.exists_prescribedDerivativeField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f χ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = χ x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x => {w | mvfderiv 𝓘(ℝ, E) f x w = χ x}
  have hC (x : M) : Convex ℝ (C x) :=
    (convex_singleton (χ x)).linear_preimage (mvfderiv 𝓘(ℝ, E) f x).toLinearMap
  have hlocal :
    ∀ p : M,
      ∃ U ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              U ∧
            ∀ x ∈ U, V x ∈ C x := by
    intro p
    by_cases hp : p ∉ ManifoldMorse.criticalPoints E f
    · obtain ⟨U, hU, hpU, V, hV, hVunit⟩ := exists_unitSpeedField_near_regular hf hp
      refine ⟨U, hU.mem_nhds hpU, (fun x => χ x • V x), hχ.contMDiffOn.smul_section hV, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x (χ x • V x) = χ x
      rw [map_smul, hVunit x hx, smul_eq_mul, mul_one]
    · have hps : p ∉ tsupport χ := fun h => hp (hsupp h)
      refine
        ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl.mem_nhds hps, (fun _ => 0),
          (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E))).contMDiffOn, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x 0 = χ x
      rw [map_zero, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, hV⟩

/-- Local descent fields glue to a descent field near a regular set. -/
theorem FlowConstruction.exists_gluedDescentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {ι : Type*} [Finite ι] (U K : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsClosed (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : ManifoldMorse.criticalPoints E f ⊆ ⋃ i, K i)
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc :
      ∀ i,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hdesc :
      ∀ i x,
        x ∈ U i →
          x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
          ∀ i x, x ∈ K i → V x = Vloc i x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w |
      (x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
        ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, Set.mem_Iio] using h
    · intro i hxi
      rw [hu.2 i hxi, hv.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal :
    ∀ p : M,
      ∃ W ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              W ∧
            ∀ x ∈ W, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      refine ⟨U i, (hU i).mem_nhds (hKU i hpi), Vloc i, hVloc i, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (Set.disjoint_left.mp (hdisj hij) hx (hKU j hxj))
    · have hpreg : p ∉ ManifoldMorse.criticalPoints E f := fun h => hp (hcover h)
      obtain ⟨W, hW, hpW, V, hV, hVf⟩ := exists_unitSpeedField_near_regular hf hpreg
      refine
        ⟨W ∩ (⋃ i, K i)ᶜ, (hW.inter hclosed.isOpen_compl).mem_nhds ⟨hpW, hp⟩, (fun x => -(V x)),
          hV.neg_section.mono Set.inter_subset_left, ?_⟩
      intro x hx
      refine ⟨?_, ?_⟩
      · intro _
        change mvfderiv 𝓘(ℝ, E) f x (-V x) < 0
        rw [map_neg, hVf x hx.1]
        norm_num
      · intro i hxi
        exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).1, fun i x hx => (hV x).2 i hx⟩

/-- A descent field exists on a closed patch of regular points. -/
theorem MorseCancellation.exists_closed_patch_descent_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (V₀ : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V₀ x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero₀ : ∀ x ∈ ManifoldMorse.criticalPoints E f, V₀ x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V₀ x) < 0)
    {ι : Type*} [Finite ι] (K U : ι → Set M) (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc :
      ∀ i,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hzero : ∀ i x, x ∈ U i → x ∈ ManifoldMorse.criticalPoints E f → Vloc i x = 0)
    (hdesc :
      ∀ i x,
        x ∈ U i →
          x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ i x, x ∈ K i → V x = Vloc i x := by
  classical
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w |
      (x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
        (x ∈ ManifoldMorse.criticalPoints E f → w = 0) ∧ ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, Set.mem_Iio] using h
    · intro hcrit
      rw [hu.2.1 hcrit, hv.2.1 hcrit, smul_zero, smul_zero, add_zero]
    · intro i hxi
      rw [hu.2.2 i hxi, hv.2.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal :
    ∀ p : M,
      ∃ O ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              O ∧
            ∀ x ∈ O, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      let R := ⋃ j : { j : ι // j ≠ i }, K j
      have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hK j)
      have hpR : p ∉ R := by
        intro hpR
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpR
        exact Set.disjoint_left.mp (hdisj (fun h => j.property h.symm)) hpi hpj
      refine
        ⟨U i ∩ Rᶜ, ((hU i).inter hR.isOpen_compl).mem_nhds ⟨hKU i hpi, hpR⟩, Vloc i,
          (hVloc i).mono Set.inter_subset_left, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx.1, hzero i x hx.1, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨⟨j, fun h => hij h.symm⟩, hxj⟩))
    · refine ⟨(⋃ i, K i)ᶜ, hclosed.isOpen_compl.mem_nhds hp, V₀, hV₀.contMDiffOn, ?_⟩
      intro x hx
      refine ⟨hdesc₀ x, hzero₀ x, ?_⟩
      intro i hxi
      exact False.elim (hx (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).2.1, fun x => (hV x).1, fun i x hx => (hV x).2.2 i hx⟩

/-- A field on a partial chart. -/
def FlowConstruction.partialChartField {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) e (fun y => (NormedSpace.fromTangentSpace y).symm (W y))

/-- The partial chart field is smooth on its domain. -/
theorem FlowConstruction.contMDiffOn_partialChartField {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) {W : F → F} (hW : ContDiff ℝ ∞ W) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, partialChartField e W x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hW' :
    ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).tangent) ∞
      (fun y : F =>
        (⟨y, (NormedSpace.fromTangentSpace y).symm (W y)⟩ : TangentBundle 𝓘(ℝ, F) F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hW
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x).IsInvertible := ⟨he.mfderiv hx, rfl⟩
  exact
    ((hW' (e x)).mpullback_vectorField_preimage
        ((e.contMDiffOn x hx).contMDiffAt (e.open_source.mem_nhds hx)) hinv
        (by simp)).contMDiffWithinAt

/-- The partial chart field's derivative of the function. -/
theorem FlowConstruction.mvfderiv_partialChartField {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (partialChartField e W x) = fderiv ℝ (f ∘ e.symm) (e x) (W (e x)) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  have hc :
    fderiv ℝ (f ∘ e'.symm) (e' x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (e' x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e' x) (hf.mdifferentiableAt (by simp))
        (he.mdifferentiableAt_symm (e'.map_source hx))]
    rw [e'.left_inv hx]
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change
    mvfderiv 𝓘(ℝ, E) f x
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
          ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x)))) =
      _
  rw [hi]
  exact (congrArg (fun A : F →L[ℝ] ℝ => A (W (e' x))) hc).symm

/-- A partition of unity normalized near a closed set exists. -/
theorem HolomorphicCousin.exists_smoothPartitionOfUnity_normalized_near_closed {ι E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : Set.univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M,
      IsOpen V ∧
        K ⊆ V ∧
          closure V ⊆ U i₀ ∧
            ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
              ρ.IsSubordinate U ∧
                Set.EqOn (ρ i₀) (fun _ => 1) (closure V) ∧
                  ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) (closure V) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨V, hVo, hKV, hVU⟩ := normal_exists_closure_subset hK (hUo i₀) hKU
  let W : ι → Set M := fun i => if i = i₀ then U i else U i \ closure V
  have hWo (i : ι) : IsOpen (W i) := by
    by_cases hi : i = i₀
    · simpa only [W, if_pos hi] using hUo i
    · simpa only [W, if_neg hi] using (hUo i).sdiff isClosed_closure
  have hWc : Set.univ ⊆ ⋃ i, W i := by
    intro x hx
    by_cases hxV : x ∈ closure V
    · apply Set.mem_iUnion_of_mem i₀
      simpa only [W, if_pos rfl] using hVU hxV
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hUc hx)
      apply Set.mem_iUnion_of_mem i
      by_cases hi : i = i₀
      · simpa only [W, if_pos hi] using hxi
      · simpa only [W, if_neg hi, Set.mem_sdiff] using And.intro hxi hxV
  obtain ⟨ρ, hρW⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ W hWo hWc
  have hρU : ρ.IsSubordinate U := by
    intro i x hx
    have hxi := hρW i hx
    by_cases hi : i = i₀
    · simpa only [W, if_pos hi] using hxi
    · exact (show x ∈ U i \ closure V by simpa only [W, if_neg hi] using hxi).1
  have hdisjoint (i : ι) (hi : i ≠ i₀) : Disjoint (tsupport (ρ i)) (closure V) := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    have hxi : x ∈ U i \ closure V := by simpa only [W, if_neg hi] using hρW i hx
    exact hxi.2 hxV
  have hzero (x : M) (hx : x ∈ closure V) (i : ι) (hi : i ≠ i₀) : ρ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => Set.disjoint_left.mp (hdisjoint i hi) hs hx
  refine ⟨V, hVo, hKV, hVU, ρ, hρU, ?_, hdisjoint⟩
  intro x hx
  exact
    (finsum_eq_single (fun i => ρ i x) i₀ (hzero x hx)).symm.trans (ρ.sum_eq_one (Set.mem_univ x))

/-- A partition of unity summing to `1` near a closed set exists. -/
theorem HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed {ι E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : Set.univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M,
      IsOpen V ∧
        K ⊆ V ∧
          V ⊆ U i₀ ∧
            ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
              ρ.IsSubordinate U ∧
                (∀ x ∈ V, ρ i₀ x = 1) ∧
                  (∀ i, i ≠ i₀ → ∀ x ∈ V, ρ i x = 0) ∧
                    ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) V := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρU, hρone, hρdisjoint⟩ :=
    exists_smoothPartitionOfUnity_normalized_near_closed I U hUo hUc i₀ hK hKU
  refine ⟨V, hVo, hKV, subset_closure.trans hVU, ρ, hρU, ?_, ?_, ?_⟩
  · intro x hx
    exact hρone (subset_closure hx)
  · intro i hi x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => Set.disjoint_left.mp (hρdisjoint i hi) hs (subset_closure hx)
  · intro i hi
    exact (hρdisjoint i hi).mono_right subset_closure

/-- A smooth cutoff equal to `1` near a closed set exists. -/
theorem LineBundleTransport.exists_smooth_cutoff_near_closed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
        tsupport χ ⊆ U ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn χ (fun _ => 1) W := by
  classical
  let O : Bool → Set E := fun b => if b then Kᶜ else U
  have hOo (b : Bool) : IsOpen (O b) := by
    cases b
    · exact hU
    · exact hK.isOpen_compl
  have hOc : Set.univ ⊆ ⋃ b, O b := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, fun hk => hx (hKU hk)⟩
  obtain ⟨W, hWo, hKW, hWU, ρ, hρ, hρone, -, -⟩ :=
    HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed (modelWithCornersSelf ℝ E)
      O hOo hOc Bool.false hK hKU
  exact ⟨ρ Bool.false, (ρ Bool.false).contMDiff.contDiff, hρ Bool.false, W, hWo, hKW, hWU, hρone⟩

/-- A smooth extension of a local section exists near a closed set. -/
theorem LineBundleTransport.exists_smooth_extension_near_closed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K U : Set E} {f : E → F} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn G f W := by
  obtain ⟨χ, hχ, hχU, W, hWo, hKW, hWU, hχone⟩ := exists_smooth_cutoff_near_closed hK hU hKU
  let G : E → F := fun x => χ x • f x
  have hG : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ G := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU : x ∈ U := hχU (tsupport_smul_subset_left χ f hx)
    exact hχ.contMDiff.contMDiffAt.smul ((hf.contDiffAt (hU.mem_nhds hxU)).contMDiffAt)
  refine ⟨G, hG.contDiff, W, hWo, hKW, hWU, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [hχone hx, one_smul]

/-- A smooth cutoff on an interval exists. -/
theorem LineBundleTransport.exists_interval_cutoff (a b : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ Set.EqOn χ (fun _ => 1) (Set.uIcc a b) := by
  obtain ⟨R, -, hR⟩ :=
    (isCompact_uIcc : IsCompact (Set.uIcc a b)).isBounded.subset_ball_lt (0 : ℝ) 0
  obtain ⟨χ, hχ, hχU, W, -, hKW, -, hχone⟩ :=
    exists_smooth_cutoff_near_closed (isCompact_uIcc : IsCompact (Set.uIcc a b)).isClosed
      Metric.isOpen_ball hR
  refine ⟨χ, hχ, ?_, hχone.mono hKW⟩
  exact
    (ProperSpace.isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport χ)
      (hχU.trans Metric.ball_subset_closedBall)

/-- A smooth function with a prescribed compact plateau exists on any smooth manifold:
the tool for making perturbations constant off a compact set. -/
theorem ManifoldMorse.exists_compact_plateau {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] (p : M) :
    ∃ (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (U L : Set M),
      IsOpen U ∧
        U ⊆ (chartAt E p).source ∧ Set.EqOn φ (fun _ => 1) U ∧ IsCompact L ∧ L ∈ 𝓝 p ∧ L ⊆ U := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let φ : SmoothBumpFunction 𝓘(ℝ, E) p := Classical.choice inferInstance
  have hN : {x : M | φ x = 1} ∩ (chartAt E p).source ∈ 𝓝 p :=
    Filter.inter_mem φ.eventuallyEq_one
      ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))
  obtain ⟨U, hUN, hU, hpU⟩ := mem_nhds_iff.mp hN
  obtain ⟨L, hpL, hLU, hL⟩ := local_compact_nhds (hU.mem_nhds hpU)
  exact ⟨φ, U, L, hU, fun x hx => (hUN hx).2, fun x hx => (hUN hx).1, hL, hpL, hLU⟩

/-- A perturbation eventually agrees with the chart expression. -/
theorem ManifoldMorse.perturb_inChart_eventuallyEq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) {f : M → ℝ} {G : E → ℝ} {U : Set M} {V : Set E}
    (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source) (hφ : Set.EqOn φ (fun _ => 1) U)
    (hV : IsOpen V) (hG : Set.EqOn G (f ∘ (chartAt E p).symm) V) (a : E) {x : M} (hx : x ∈ U)
    (hxV : chartAt E p x ∈ V) :
    ManifoldPerturbation.perturb φ f a ∘ (chartAt E p).symm =ᶠ[𝓝 (chartAt E p x)]
      MorsePerturbation.linearPerturbation G a := by
  let e := chartAt E p
  have hxt : e x ∈ e.target := e.map_source (hUs hx)
  have hi : ContinuousAt e.symm (e x) := e.symm.continuousAt hxt
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (e x) := by
    apply hi.preimage_mem_nhds
    simpa only [e.left_inv (hUs hx)] using hU.mem_nhds hx
  filter_upwards [hpre, e.open_target.mem_nhds hxt, hV.mem_nhds hxV] with y hyU hyt hyV
  have hφy := hφ hyU
  have hGy := hG hyV
  change G y = f (e.symm y) at hGy
  change
    f (e.symm y) -
        MorsePerturbation.dualEquiv a (φ (e.symm y) • extChartAt 𝓘(ℝ, E) p (e.symm y)) =
      G y - MorsePerturbation.dualEquiv a y
  rw [hφy, one_smul, ← hGy]
  congr 2
  simpa only [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq] using
    e.right_inv hyt

/-- A smooth function prescribed on a closed subset of a smooth manifold extends to a
Morse function on the whole manifold (Milnor, \*Morse Theory\* Section 1). -/
theorem ManifoldMorse.exists_morse_extension {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p)
    {U L K : Set M} (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source)
    (hφ : Set.EqOn φ (fun _ => 1) U) (hL : IsCompact L) (hLU : L ⊆ U) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hK : IsCompact K) (hfK : IsMorseOn E f K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : E,
      ‖a‖ < ε ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (ManifoldPerturbation.perturb φ f a) ∧
          IsMorseOn E (ManifoldPerturbation.perturb φ f a) (L ∪ K) := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hLc : IsCompact (e '' L) := hL.image_of_continuousOn (e.continuousOn.mono (hLU.trans hUs))
  have hLt : e '' L ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs (hLU hx))
  obtain ⟨G, hG, V, hV, hLV, -, hGV⟩ :=
    LineBundleTransport.exists_smooth_extension_near_closed hLc.isClosed e.open_target hLt
      (contDiffOn_chartExpression hf he)
  have hfamily := ManifoldPerturbation.contMDiff_perturb φ hf
  let A : Set E := {a | IsMorseOn E (ManifoldPerturbation.perturb φ f a) K}
  have hA : IsOpen A := isOpen_isMorseOn (f := ManifoldPerturbation.perturb φ f) hfamily hK
  have hA₀ : (0 : E) ∈ A := by simpa [A] using hfK
  have hd :=
    RegularValues.dense_regularValues μ
      ((MorsePerturbation.contDiff_coordinateGradient hG).differentiable (by simp))
  obtain ⟨a, ha, haA, haε⟩ :=
    hd.exists_mem_open (hA.inter Metric.isOpen_ball) ⟨0, hA₀, Metric.mem_ball_self hε⟩
  refine ⟨a, mem_ball_zero_iff.mp haε, ?_, ?_⟩
  · exact hfamily.comp (contMDiff_const.prodMk contMDiff_id)
  · refine IsMorseOn.union ?_ haA
    intro x hx
    apply
      isMorseAt_of_chart_eventuallyEq he (hUs (hLU hx))
        (MorsePerturbation.isMorse_of_regularValue hG ha)
    exact
      perturb_inChart_eventuallyEq φ hU hUs hφ hV hGV a (hLU hx) (hLV (Set.mem_image_of_mem e hx))

/-- Every smooth function on a compact smooth manifold can be uniformly approximated by
a Morse function; in particular a compact smooth manifold admits a Morse function
(Milnor, \*Morse Theory\* Section 1). -/
theorem ManifoldMorse.exists_morse_function_of_haar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f := by
  classical
  choose φ U L hU hUs hφ hL hn hLU using exists_compact_plateau (E := E) (M := M)
  obtain ⟨s, hs⟩ := finite_cover_nhds hn
  have hfinite :
    ∀ t : Finset M, ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorseOn E f (⋃ p ∈ t, L p) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, contMDiff_const, ?_⟩
      intro x hx
      simp at hx
    | @insert p t hp ih =>
      obtain ⟨f, hf, hm⟩ := ih
      have hK : IsCompact (⋃ q ∈ t, L q) := t.isCompact_biUnion (fun q _ => hL q)
      obtain ⟨a, -, hfa, hma⟩ :=
        exists_morse_extension μ (φ p) (hU p) (hUs p) (hφ p) (hL p) (hLU p) hf hK hm (ε := 1)
          zero_lt_one
      refine ⟨ManifoldPerturbation.perturb (φ p) f a, hfa, ?_⟩
      have heq : (⋃ q ∈ Insert.insert p t, L q) = L p ∪ ⋃ q ∈ t, L q := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨q, hq | hq, hx⟩
          · subst q
            exact Or.inl hx
          · exact Or.inr ⟨q, hq, hx⟩
        · rintro (hx | ⟨q, hq, hx⟩)
          · exact ⟨p, Or.inl rfl, hx⟩
          · exact ⟨q, Or.inr hq, hx⟩
      rw [heq]
      exact hma
  obtain ⟨f, hf, hm⟩ := hfinite s
  refine ⟨f, hf, fun x => hm x ?_⟩
  rw [hs]
  exact Set.mem_univ x

/-- Every compact smooth manifold admits a Morse function (Milnor, Morse Theory, Section 1; Hatcher, Algebraic Topology, Section 0). -/
theorem ManifoldMorse.exists_morse_function (E : Type*) (M : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact exists_morse_function_of_haar (E := E) (M := M) MeasureTheory.Measure.addHaar

/-! ### The second-order Taylor factor -/

/-- A parametric interval integral of a `C^n` integrand is `C^n`. -/
theorem SmoothMorseLemma.contDiff_parametric_intervalIntegral_of_le {P F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : P × ℝ → F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := LineBundleTransport.exists_interval_cutoff a b
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc a b)
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  let g : P → ℝ → F := fun p t => χ (-t) • G (p, -t)
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => g q.1 q.2) :=
    (hχ.comp contDiff_snd.neg).smul (hG.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hk : IsCompact (-tsupport χ) := hχc.isCompact.neg
  have hgs : ∀ p t, p ∈ (Set.univ : Set P) → t ∉ -tsupport χ → g p t = 0 := by
    intro p t _ ht
    have ht' : -t ∉ tsupport χ := by simpa using ht
    change χ (-t) • G (p, -t) = 0
    rw [image_eq_zero_of_notMem_tsupport ht', zero_smul]
  have hf : MeasureTheory.LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) μ :=
    MeasureTheory.locallyIntegrable_const _
  have hc :=
    MeasureTheory.contDiffOn_convolution_right_with_param_comp (μ := μ) (n := (⊤ : ℕ∞)) L (v :=
      fun _ : P => (0 : ℝ)) contDiffOn_const isOpen_univ hk hgs hf hg.contDiffOn
  have heq (p : P) : ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0 = ∫ t in a..b, G (p, t) := by
    rw [intervalIntegral.integral_of_le hab]
    change (∫ t, (1 : ℝ) • (χ (-(0 - t)) • G (p, -(0 - t))) ∂μ) = ∫ t in Set.Ioc a b, G (p, t)
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hχt : χ t = 1 := hχone (Set.mem_uIcc_of_le ht.1.le ht.2)
    simp only [zero_sub, neg_neg, hχt, one_smul]
  have hfun :
    (fun p => ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0) = (fun p => ∫ t in a..b, G (p, t)) :=
    funext heq
  rw [← hfun]
  exact contDiffOn_univ.mp hc

/-- A parametric interval integral is smooth. -/
theorem SmoothMorseLemma.contDiff_parametric_intervalIntegral {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] (G : P × ℝ → F)
    (hG : ContDiff ℝ ∞ G) (a b : ℝ) : ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  rcases le_total a b with hab | hba
  · exact contDiff_parametric_intervalIntegral_of_le G hG a b hab
  · have he : (fun p => ∫ t in a..b, G (p, t)) = (fun p => -(∫ t in b..a, G (p, t))) :=
      funext fun _ => intervalIntegral.integral_symm b a
    rw [he]
    exact (contDiff_parametric_intervalIntegral_of_le G hG b a hba).neg

/-- The Hessian integrand of the second-order Taylor expansion. -/
def SmoothMorseLemma.taylorHessianIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (q : E × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 - q.2) • fderiv ℝ (fderiv ℝ f) (q.2 • q.1)

/-- The second-order Taylor remainder factor. -/
def SmoothMorseLemma.secondTaylorFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, taylorHessianIntegrand f (x, t)

/-- The Taylor Hessian integrand is smooth. -/
theorem SmoothMorseLemma.contDiff_taylorHessianIntegrand {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (taylorHessianIntegrand f) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := .of_norm_smul_le (fun c B => norm_smul_le c B)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := (contDiff_infty_iff_fderiv.mp hdf).2
  exact (contDiff_const.sub contDiff_snd).smul (hH.comp (contDiff_snd.smul contDiff_fst))

/-- The second Taylor factor is smooth. -/
theorem SmoothMorseLemma.contDiff_secondTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (secondTaylorFactor f) :=
  (contDiff_parametric_intervalIntegral (taylorHessianIntegrand f)
        (contDiff_taylorHessianIntegrand hf) 0 1).const_smul
    (2 : ℝ)

/-- The second Taylor factor evaluates the integral formula. -/
theorem SmoothMorseLemma.secondTaylorFactor_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) u v := by
  have hc : Continuous (fun t : ℝ => taylorHessianIntegrand f (x, t)) :=
    (contDiff_taylorHessianIntegrand hf).continuous.comp (continuous_const.prodMk continuous_id)
  have hi :
    IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t))
      MeasureTheory.MeasureSpace.volume 0 1 :=
    hc.intervalIntegrable 0 1
  have hiu :
    IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t) u)
      MeasureTheory.MeasureSpace.volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  simp only [secondTaylorFactor, smul_apply]
  rw [ContinuousLinearMap.intervalIntegral_apply hi u,
    ContinuousLinearMap.intervalIntegral_apply hiu v]
  simp only [taylorHessianIntegrand, smul_apply, smul_eq_mul]

/-- The second Taylor factor vanishes at the basepoint. -/
theorem SmoothMorseLemma.secondTaylorFactor_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) : secondTaylorFactor f 0 = fderiv ℝ (fderiv ℝ f) 0 := by
  have hw : (∫ t in (0 : ℝ)..1, (1 - t)) = (1 / 2 : ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t)) = (∫ _t in (0 : ℝ)..1, (1 : ℝ)) - ∫ t in (0 : ℝ)..1, t :=
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)
      _ = 1 / 2 := by norm_num [integral_id]
  have hz :
    (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) 0) =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 :=
    (intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t) (fderiv ℝ (fderiv ℝ f) 0)).trans
      (congrArg (fun c : ℝ => c • fderiv ℝ (fderiv ℝ f) 0) hw)
  simp only [secondTaylorFactor, taylorHessianIntegrand, smul_zero]
  exact (congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => (2 : ℝ) • B) hz).trans (by norm_num [smul_smul])

/-- The second Taylor factor is symmetric. -/
theorem SmoothMorseLemma.secondTaylorFactor_symmetric {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v = secondTaylorFactor f x v u := by
  rw [secondTaylorFactor_apply hf, secondTaylorFactor_apply hf]
  apply congrArg (fun r : ℝ => 2 * r)
  apply intervalIntegral.integral_congr
  intro t _
  have hs : IsSymmSndFDerivAt ℝ f (t • x) :=
    hf.contDiffAt.isSymmSndFDerivAt
      (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun r : ℝ => (1 - t) * r) (hs u v)

/-- A function with vanishing jet is its second Taylor factor plus a linear term. -/
theorem SmoothMorseLemma.map_eq_add_linear_add_secondTaylorFactor {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    f x = f 0 + fderiv ℝ f 0 x + (1 / 2 : ℝ) * secondTaylorFactor f x x x := by
  have ht :=
    map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := x) (n := 1)
      (fun t _ => hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have ht' :
    f x = f 0 + fderiv ℝ f 0 x + ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x :=
    by simpa [Finset.sum_range_succ, iteratedFDeriv_two_apply, smul_eq_mul] using ht
  rw [secondTaylorFactor_apply hf]
  calc
    f x = f 0 + fderiv ℝ f 0 x + ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x :=
      ht'
    _ =
        f 0 + fderiv ℝ f 0 x +
          (1 / 2 : ℝ) * (2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x) := by
      ring

/-! ### Symmetric forms and congruence -/

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

/-- The second Taylor factor as a symmetric form. -/
def SmoothMorseLemma.symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : SymmetricForm E :=
  symmetrize E (secondTaylorFactor f x)

/-- The symmetric Taylor factor is smooth. -/
theorem SmoothMorseLemma.contDiff_symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (symmetricTaylorFactor f) :=
  (symmetrize E).contDiff.comp (contDiff_secondTaylorFactor hf)

/-- The symmetric Taylor factor evaluates the second factor. -/
theorem SmoothMorseLemma.symmetricTaylorFactor_coe {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    (symmetricTaylorFactor f x).val = secondTaylorFactor f x := by
  ext u v
  change
    (2 : ℝ)⁻¹ * (secondTaylorFactor f x u v + secondTaylorFactor f x v u) =
      secondTaylorFactor f x u v
  rw [secondTaylorFactor_symmetric hf x v u]
  ring

/-- The symmetric Taylor factor vanishes at the basepoint. -/
theorem SmoothMorseLemma.symmetricTaylorFactor_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    (symmetricTaylorFactor f 0).val = fderiv ℝ (fderiv ℝ f) 0 := by
  rw [symmetricTaylorFactor_coe hf, secondTaylorFactor_zero]

/-- The function equals its linear term plus the symmetric quadratic factor. -/
theorem SmoothMorseLemma.map_eq_add_symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : fderiv ℝ f 0 = 0) (x : E) :
    f x = f 0 + (1 / 2 : ℝ) * (symmetricTaylorFactor f x).val x x := by
  rw [symmetricTaylorFactor_coe hf]
  simpa only [hc, zero_apply, add_zero] using map_eq_add_linear_add_secondTaylorFactor hf x

/-- A `C^n` map on a set with invertible derivative restricts to a partial diffeomorphism. -/
theorem SmoothMorseLemma.exists_partialDiffeomorph_of_contDiffOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (a : E)
    (ha : a ∈ U) (f' : E ≃L[ℝ] F) (hderiv : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      a ∈ e.source ∧ e.source ⊆ U ∧ ∀ x : E, e x = f x := by
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hU.mem_nhds ha)
  have hdc : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds ha)
  have hinv : {x : E | ∃ l : E ≃L[ℝ] F, (l : E →L[ℝ] F) = fderiv ℝ f x} ∈ 𝓝 a := by
    have hn := f'.nhds
    rw [← hderiv.fderiv] at hn
    exact hdc.preimage_mem_nhds hn
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds ha) hinv)
  let e : OpenPartialHomeomorph E F := (hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W
  have heW : e.source ⊆ W := by
    intro x hx
    change x ∈ ((hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W).source at hx
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen] at hx
    exact hx.2
  have heU : e.source ⊆ U := fun x hx => (hWsub (heW hx)).1
  have hae : a ∈ e.source := by
    change a ∈ ((hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen]
    exact ⟨hfa.mem_toOpenPartialHomeomorph_source hderiv (by simp), haW⟩
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := ?_
        contMDiffOn_invFun := ?_ }, hae, heU, fun _ => rfl⟩
  · change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f e.source
    exact (hf.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro y hy
    have hxW := heW (e.map_target hy)
    obtain ⟨hxU, l, hl⟩ := hWsub hxW
    have hfx : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (hU.mem_nhds hxU)
    have hdx : HasFDerivAt f (l : E →L[ℝ] F) (e.symm y) := by
      rw [hl]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hdx hfx).contDiffWithinAt

/-- A `C^n` map with invertible derivative is a partial diffeomorphism. -/
theorem SmoothMorseLemma.exists_partialDiffeomorph_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (a : E) (f' : E ≃L[ℝ] F)
    (hderiv : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞, a ∈ e.source ∧ ∀ x : E, e x = f x := by
  obtain ⟨e, ha, _, he⟩ :=
    exists_partialDiffeomorph_of_contDiffOn isOpen_univ hf.contDiffOn a (Set.mem_univ a) f' hderiv
  exact ⟨e, ha, he⟩

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

/-! ### The congruence polynomial -/

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

/-! ### The Morse chart -/

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

/-- A compactly supported `C^n` function agreeing on a closed ball exists. -/
theorem SmoothMorseLemma.exists_contDiff_compactlySupported_eqOn_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    {a : E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧
        HasCompactSupport g ∧
          tsupport g ⊆ U ∧
            ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U ∧ Set.EqOn g f (Metric.closedBall a r) := by
  obtain ⟨r, hr, hrU⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let β : ContDiffBump a :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβU : tsupport (β : E → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    exact hrU
  have hg : ContDiff ℝ ∞ (fun x => β x * f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (β : E → ℝ)
    · exact β.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hβU hx)))
    · have hzero : (β : E → ℝ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hconst : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) x := contDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp only [hy, Pi.zero_apply, MulZeroClass.zero_mul]
  refine
    ⟨fun x => β x * f x, hg, β.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hβU,
      β.rIn, β.rIn_pos, ?_, ?_⟩
  · exact (Metric.closedBall_subset_closedBall β.rIn_lt_rOut.le).trans hrU
  · intro x hx
    change β x * f x = f x
    rw [β.one_of_mem_closedBall hx, one_mul]

/-- A `C^n` extension of a local germ exists. -/
theorem SmoothMorseLemma.exists_contDiff_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} {a : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨g, hg, _, _, r, hr, _, he⟩ :=
    exists_contDiff_compactlySupported_eqOn_closedBall hf hU ha
  refine ⟨g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr] with x hx
  exact he (Metric.ball_subset_closedBall hx)

/-- A `C^n` extension preserving derivatives exists. -/
theorem SmoothMorseLemma.exists_contDiff_extension_preserving_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    {a : E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧
        g =ᶠ[𝓝 a] f ∧
          g a = f a ∧
            fderiv ℝ g a = fderiv ℝ f a ∧
              fderiv ℝ (fderiv ℝ g) a = fderiv ℝ (fderiv ℝ f) a ∧
                ∀ n : ℕ, iteratedFDeriv ℝ n g =ᶠ[𝓝 a] iteratedFDeriv ℝ n f := by
  obtain ⟨g, hg, he⟩ := exists_contDiff_extension hf hU ha
  exact
    ⟨g, hg, he, he.self_of_nhds, he.fderiv_eq, he.fderiv.fderiv_eq, fun n =>
      he.iteratedFDeriv ℝ n⟩

/-- A chart restricted to a smaller domain. -/
def SmoothMorseLemma.restrictChart {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : Set E) (hU : IsOpen U) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞
    where
  __ := e.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := e.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono Set.inter_subset_left

/-- The restricted chart computes the chart. -/
@[simp]
theorem SmoothMorseLemma.restrictChart_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (U : Set E) (hU : IsOpen U) (x : E) :
    restrictChart e U hU x = e x :=
  rfl

/-- The translation of the model space moving a point to zero. -/
def SmoothMorseLemma.translationToZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞
    where
  toFun x := x - a
  invFun x := a + x
  left_inv x := by simp [sub_eq_add_neg]
  right_inv x := by simp [sub_eq_add_neg, add_assoc]
  contMDiff_toFun :=
    (show ContDiff ℝ ∞ (fun x : E => x - a) from contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun :=
    (show ContDiff ℝ ∞ (fun x : E => a + x) from contDiff_const.add contDiff_id).contMDiff

def SmoothMorseLemma.diffeomorphToPartialDiffeomorph {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (h : Diffeomorph I J X Y ∞) : PartialDiffeomorph I J X Y ∞ where
  toPartialEquiv := h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

/-- A chart translated to center a point. -/
def SmoothMorseLemma.translateChart {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ :=
  (diffeomorphToPartialDiffeomorph (translationToZero a)).trans e

/-- The translated chart computes the shifted chart. -/
@[simp]
theorem SmoothMorseLemma.translateChart_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (x : E) : translateChart a e x = e (x - a) :=
  rfl

/-- Membership in the translated chart's source. -/
@[simp]
theorem SmoothMorseLemma.mem_translateChart_source {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (x : E) :
    x ∈ (translateChart a e).source ↔ x - a ∈ e.source := by
  change (x ∈ Set.univ ∧ x - a ∈ e.source) ↔ x - a ∈ e.source
  simp only [Set.mem_univ, true_and]

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

/-! ### Signed coordinates -/

/-- The quadratic form of half the Hessian. -/
def SmoothMorseLemma.halfHessianQuadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Bilinear E) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((1 / 2 : ℝ) • H.toLinearMap₁₂)

/-- The half-Hessian quadratic form evaluates the Hessian. -/
@[simp]
theorem SmoothMorseLemma.halfHessianQuadratic_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (x : E) : halfHessianQuadratic H x = (1 / 2 : ℝ) * H x x :=
  rfl

/-- The half-Hessian form is associated to the Hessian. -/
theorem SmoothMorseLemma.halfHessianQuadratic_associated {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x) :
    QuadraticMap.associated (halfHessianQuadratic H) = (1 / 2 : ℝ) • H.toLinearMap₁₂ := by
  apply QuadraticMap.associated_left_inverse ℝ (B₁ := (1 / 2 : ℝ) • H.toLinearMap₁₂)
  intro x y
  change (1 / 2 : ℝ) * H x y = (1 / 2 : ℝ) * H y x
  rw [hH]

/-- The nondegenerate half-Hessian form separates points. -/
theorem SmoothMorseLemma.halfHessianQuadratic_separatingLeft {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHinj : Function.Injective H) :
    (QuadraticMap.associated (halfHessianQuadratic H)).SeparatingLeft := by
  rw [halfHessianQuadratic_associated H hH]
  intro x hx
  apply hHinj
  ext y
  have hxy := hx y
  change (1 / 2 : ℝ) * H x y = 0 at hxy
  simpa using (mul_eq_zero.mp hxy).resolve_left (by norm_num)

/-- Signed coordinates diagonalizing the Hessian exist. -/
theorem SmoothMorseLemma.exists_signed_coordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ C : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
          ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, ⟨C⟩⟩ :=
    (halfHessianQuadratic H).equivalent_one_neg_one_weighted_sum_squared
      (halfHessianQuadratic_separatingLeft H hH hHbij.1)
  refine ⟨w, hw, C.toLinearEquiv.toContinuousLinearEquiv, ?_⟩
  intro x
  change (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2
  simpa only [QuadraticMap.weightedSumSquares_apply, halfHessianQuadratic_apply, smul_eq_mul,
    pow_two] using (C.map_app x).symm

/-- A signed coordinate diffeomorphism exists. -/
theorem SmoothMorseLemma.exists_signed_diffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ C : E ≃ₘ[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
          C 0 = 0 ∧ ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, C, hC⟩ := exists_signed_coordinates H hH hHbij
  exact ⟨w, hw, C.toDiffeomorph, C.map_zero, hC⟩

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

/-! ### Signed Morse charts on manifolds -/

/-- The partial diffeomorphism of a Morse chart. -/
def ManifoldMorse.chartPartialDiffeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞
    where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

/-- A signed Morse chart: a chart in which the function is a signed quadratic form. -/
structure ManifoldMorse.SignedMorseChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (x : M) where
  weights : Fin (Module.finrank ℝ E) → ℝ
  signs : ∀ i, weights i = -1 ∨ weights i = 1
  chart :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) M (Fin (Module.finrank ℝ E) → ℝ)
      ∞
  mem_source : x ∈ chart.source
  center : chart x = 0
  equation : ∀ y ∈ chart.source, f y = f x + ∑ i, weights i * (chart y i) ^ 2
  inverse_equation : ∀ y ∈ chart.target, f (chart.symm y) = f x + ∑ i, weights i * y i ^ 2

/-- A signed Morse chart exists near a Morse critical point. -/
theorem ManifoldMorse.nonempty_signedMorseChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (x : M)
    (hx : x ∈ criticalPoints E f) : Nonempty (SignedMorseChart (E := E) f x) := by
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc := (mem_criticalPoints_iff hf he hxS).mp hx
    obtain ⟨w, hw, d, hdx, -, hd₀, hdeq, hdinv⟩ :=
      SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn (contDiffOn_chartExpression hf he)
        e.open_target (e x) (e.map_source hxS) hc hH
    let c := (chartPartialDiffeomorph e he).trans d
    refine ⟨⟨w, hw, c, ⟨hxS, hdx⟩, hd₀, ?_, ?_⟩⟩
    · intro y hy
      have hyS : y ∈ e.source := hy.1
      have hyd : e y ∈ d.source := hy.2
      change f y = f x + ∑ i, w i * (d (e y) i) ^ 2
      simpa only [Function.comp_apply, e.left_inv hyS, e.left_inv hxS] using hdeq (e y) hyd
    · intro y hy
      have hyd : y ∈ d.target := hy.1
      change f (e.symm (d.symm y)) = f x + ∑ i, w i * y i ^ 2
      simpa only [Function.comp_apply, e.left_inv hxS] using hdinv y hyd

/-! ### Handle splitting of signed charts -/

/-- The negative eigenspace of a signed form. -/
abbrev MorseHandle.Negative {ι : Type*} (w : ι → ℝ) :=
  { i // w i = -1 }

/-- The positive eigenspace of a signed form. -/
abbrev MorseHandle.Positive {ι : Type*} (w : ι → ℝ) :=
  { i // w i ≠ -1 }

/-- The negative coordinates of a Morse chart. -/
abbrev MorseHandle.NegativeSpace {ι : Type*} (w : ι → ℝ) :=
  EuclideanSpace ℝ (Negative w)

/-- The positive coordinates of a Morse chart. -/
abbrev MorseHandle.PositiveSpace {ι : Type*} (w : ι → ℝ) :=
  EuclideanSpace ℝ (Positive w)

attribute [local instance 100] Classical.propDecidable in
/-- The space splits as negative times positive. -/
def MorseHandle.splitLinearEquiv {ι : Type*} (w : ι → ℝ) :
    (ι → ℝ) ≃ₗ[ℝ] (NegativeSpace w × PositiveSpace w) := by
  let e : (ι → ℝ) ≃ₗ[ℝ] ((Negative w → ℝ) × (Positive w → ℝ)) :=
    { toEquiv := Equiv.piEquivPiSubtypeProd (fun i => w i = -1) (fun _ => ℝ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact
    e.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Negative w → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Positive w → ℝ)).symm)

attribute [local instance 100] Classical.propDecidable in
/-- The split coordinates of a point. -/
def MorseHandle.splitCoordinates {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (ι → ℝ) ≃L[ℝ] (NegativeSpace w × PositiveSpace w) :=
  (splitLinearEquiv w).toContinuousLinearEquiv

attribute [local instance 100] Classical.propDecidable in
/-- The signed quadratic form is `‖−‖² − ‖+‖²` on the split. -/
theorem MorseHandle.signedSum_eq_norms {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    ∑ i, w i * (z i) ^ 2 = -‖(splitCoordinates w z).1‖ ^ 2 + ‖(splitCoordinates w z).2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hneg : (∑ i : Negative w, w i.1 * (z i.1) ^ 2) = -∑ i : Negative w, (z i.1) ^ 2 := by
    calc
      _ = ∑ i : Negative w, -(z i.1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [i.2, neg_one_mul]
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hpos : (∑ i : Positive w, w i.1 * (z i.1) ^ 2) = ∑ i : Positive w, (z i.1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hw i.1).resolve_left i.2, one_mul]
  calc
    ∑ i, w i * (z i) ^ 2 =
        (∑ i : Negative w, w i.1 * (z i.1) ^ 2) + ∑ i : Positive w, w i.1 * (z i.1) ^ 2 :=
      (Fintype.sum_subtype_add_sum_subtype (fun i => w i = -1) (fun i => w i * (z i) ^ 2)).symm
    _ = _ := by rw [hneg, hpos]; rfl

attribute [local instance 100] Classical.propDecidable in
/-- The split of a signed-sum pair computes the norms. -/
theorem MorseHandle.signedSum_symm_eq_norms {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : NegativeSpace w × PositiveSpace w) :
    ∑ i, w i * ((splitCoordinates w).symm z i) ^ 2 = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    signedSum_eq_norms w hw ((splitCoordinates w).symm z)

/-- The negative coordinate space of a signed Morse chart. -/
abbrev ManifoldMorse.SignedMorseChart.NegativeCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :=
  MorseHandle.NegativeSpace c.weights

/-- The positive coordinate space of a signed Morse chart. -/
abbrev ManifoldMorse.SignedMorseChart.PositiveCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :=
  MorseHandle.PositiveSpace c.weights

attribute [local instance 100] Classical.propDecidable in
/-- The negative and positive ranks sum to the dimension. -/
theorem ManifoldMorse.SignedMorseChart.finrank_negative_add_positive {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :
    Module.finrank ℝ c.NegativeCoordinates + Module.finrank ℝ c.PositiveCoordinates =
      Module.finrank ℝ E := by
  have h := (MorseHandle.splitLinearEquiv c.weights).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using h.symm

attribute [local instance 100] Classical.propDecidable in
/-- The signed Morse chart split into negative and positive factors. -/
def ManifoldMorse.SignedMorseChart.splitChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) M
      (c.NegativeCoordinates × c.PositiveCoordinates) ∞ :=
  c.chart.trans (MorseHandle.splitCoordinates c.weights).toDiffeomorph.toPartialDiffeomorph

attribute [local instance 100] Classical.propDecidable in
/-- Membership in the split chart's source. -/
theorem ManifoldMorse.SignedMorseChart.splitChart_mem_source {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) : x ∈ c.splitChart.source :=
  ⟨c.mem_source, Set.mem_univ _⟩

attribute [local instance 100] Classical.propDecidable in
/-- The split chart is centered at the critical point. -/
@[simp]
theorem ManifoldMorse.SignedMorseChart.splitChart_center {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) : c.splitChart x = 0 := by
  change MorseHandle.splitCoordinates c.weights (c.chart x) = 0
  rw [c.center, map_zero]

attribute [local instance 100] Classical.propDecidable in
/-- In the split chart the function is the signed norm sum. -/
theorem ManifoldMorse.SignedMorseChart.splitChart_equation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) {y : M}
    (hy : y ∈ c.splitChart.source) :
    f y = f x - ‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2 := by
  rw [c.equation y hy.1, MorseHandle.signedSum_eq_norms c.weights c.signs]
  change f x + (-‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2) = _
  ring

attribute [local instance 100] Classical.propDecidable in
/-- The inverse split chart computes the function as the signed sum. -/
theorem ManifoldMorse.SignedMorseChart.splitChart_inverse_equation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x)
    {y : c.NegativeCoordinates × c.PositiveCoordinates} (hy : y ∈ c.splitChart.target) :
    f (c.splitChart.symm y) = f x - ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  change f (c.chart.symm ((MorseHandle.splitCoordinates c.weights).symm y)) = _
  rw [c.inverse_equation ((MorseHandle.splitCoordinates c.weights).symm y) hy.2,
    MorseHandle.signedSum_symm_eq_norms c.weights c.signs]
  ring

attribute [local instance 100] Classical.propDecidable in
/-- A closed product block exists inside the split chart. -/
theorem ManifoldMorse.SignedMorseChart.exists_closed_productBlock {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :
    ∃ r > (0 : ℝ),
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target := by
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.toOpenPartialHomeomorph.map_source c.splitChart_mem_source
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (c.splitChart.open_target.mem_nhds hzero)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

attribute [local instance 100] Classical.propDecidable in
/-- The descent field `−∇f` in split Morse coordinates. -/
def ManifoldMorse.SignedMorseChart.descentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) : (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  FlowConstruction.partialChartField c.splitChart MorseHandle.descent

attribute [local instance 100] Classical.propDecidable in
/-- The descent field is smooth on the chart domain. -/
theorem ManifoldMorse.SignedMorseChart.contMDiffOn_descentField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [CompleteSpace E]
    [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, c.descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) c.splitChart.source :=
  FlowConstruction.contMDiffOn_partialChartField c.splitChart
    MorseHandle.contDiff_descent

attribute [local instance 100] Classical.propDecidable in
/-- The descent field vanishes at the critical point. -/
@[simp]
theorem ManifoldMorse.SignedMorseChart.descentField_center {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) : c.descentField p = 0 := by
  have hzero : MorseHandle.descent (c.splitChart p) = 0 := by
    rw [c.splitChart_center]
    simp [MorseHandle.descent]
  unfold descentField FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, hzero, map_zero, map_zero]

attribute [local instance 100] Classical.propDecidable in
/-- The descent field strictly decreases the function. -/
theorem ManifoldMorse.SignedMorseChart.mvfderiv_descentField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) =
      -2 * (‖(c.splitChart x).1‖ ^ 2 + ‖(c.splitChart x).2‖ ^ 2) := by
  rw [descentField, FlowConstruction.mvfderiv_partialChartField hf c.splitChart _ hx]
  have hcoord :
    (f ∘ c.splitChart.symm) =ᶠ[𝓝 (c.splitChart x)]
      (fun z => f p + MorseHandle.quadratic z) := by
    filter_upwards [c.splitChart.open_target.mem_nhds
        (c.splitChart.toOpenPartialHomeomorph.map_source hx)] with
      z hz
    change f (c.splitChart.symm z) = f p + (-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
    rw [c.splitChart_inverse_equation hz]
    ring
  rw [hcoord.fderiv_eq, fderiv_const_add]
  exact MorseHandle.fderiv_quadratic_descent _

attribute [local instance 100] Classical.propDecidable in
/-- The descent field's derivative is negative off the critical point. -/
theorem ManifoldMorse.SignedMorseChart.mvfderiv_descentField_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) (hxp : x ≠ p) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) < 0 := by
  have hcoord : c.splitChart x ≠ 0 := by
    intro h
    apply hxp
    exact
      c.splitChart.toOpenPartialHomeomorph.injOn hx c.splitChart_mem_source
        (h.trans c.splitChart_center.symm)
  rw [c.mvfderiv_descentField hf hx]
  simpa only [MorseHandle.fderiv_quadratic_descent] using
    MorseHandle.fderiv_quadratic_descent_neg hcoord

/-- An adapted descent field exists near a Morse critical point. -/
theorem ManifoldMorse.exists_adaptedDescentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ p ∈ criticalPoints E f,
              ∃ c : SignedMorseChart (E := E) f p, ∀ᶠ x in 𝓝 p, V x = c.descentField x := by
  classical
  let S := criticalPoints E f
  have hS : S.Finite := finite_criticalPoints hf hm
  let : Fintype S := hS.fintype
  let c (p : S) : SignedMorseChart (E := E) f (p : M) :=
    Classical.choice (nonempty_signedMorseChart hf hm p.1 p.2)
  obtain ⟨U₀, hU₀, hdisj₀⟩ := hS.t2_separation
  let U (p : S) : Set M := U₀ p ∩ (c p).splitChart.source
  have hU (p : S) : IsOpen (U p) := (hU₀ p).2.inter (c p).splitChart.open_source
  have hpU (p : S) : (p : M) ∈ U p := ⟨(hU₀ p).1, (c p).splitChart_mem_source⟩
  have hdisj : Pairwise (fun p q : S => Disjoint (U p) (U q)) := by
    intro p q hpq
    exact
      (hdisj₀ p.2 q.2 (fun h => hpq (Subtype.ext h))).mono Set.inter_subset_left
        Set.inter_subset_left
  choose K hKnhds hKclosed hKU using
    (fun p : S => exists_mem_nhds_isClosed_subset ((hU p).mem_nhds (hpU p)))
  have hcover : criticalPoints E f ⊆ ⋃ p : S, K p := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, mem_of_mem_nhds (hKnhds ⟨p, hp⟩)⟩
  have hVloc (p : S) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, (c p).descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U p) :=
    (c p).contMDiffOn_descentField.mono Set.inter_subset_right
  have hdesc (p : S) (x : M) (hx : x ∈ U p) (hreg : x ∉ criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f x ((c p).descentField x) < 0 :=
    (c p).mvfderiv_descentField_neg hf hx.2 (fun h => hreg (h.symm ▸ p.2))
  obtain ⟨V, hV, hstrict, hmatch⟩ :=
    FlowConstruction.exists_gluedDescentField hf U K hU hKclosed hKU hdisj hcover
      (fun p => (c p).descentField) hVloc hdesc
  refine ⟨V, hV, ?_, hstrict, ?_⟩
  · intro p hp
    rw [hmatch ⟨p, hp⟩ p (mem_of_mem_nhds (hKnhds ⟨p, hp⟩))]
    exact (c ⟨p, hp⟩).descentField_center
  · intro p hp
    refine ⟨c ⟨p, hp⟩, ?_⟩
    filter_upwards [hKnhds ⟨p, hp⟩] with x hx
    exact hmatch ⟨p, hp⟩ x hx

/-- A descent field vanishing at a critical point is prescribed. -/
theorem MorseCancellation.morse_descentField_zero_at_critical {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ c.splitChart.source) (hcrit : x ∈ ManifoldMorse.criticalPoints E f) :
    c.descentField x = 0 := by
  by_cases hxp : x = p
  · subst x
    exact c.descentField_center
  · have hneg := c.mvfderiv_descentField_neg hf hx hxp
    have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 := hcrit
    have hz : mvfderiv 𝓘(ℝ, E) f x (c.descentField x) = 0 := by
      unfold mvfderiv
      rw [hc]
      rfl
    rw [hz] at hneg
    exact False.elim (lt_irrefl (0 : ℝ) hneg)

/-- A prescribed Morse patch field exists near a critical point. -/
theorem MorseCancellation.exists_prescribed_morse_patch_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ ManifoldMorse.criticalPoints E f)
    (c : ∀ i, ManifoldMorse.SignedMorseChart (E := E) f (p i)) (K : ι → Set M)
    (hK : ∀ i, IsClosed (K i)) (hKchart : ∀ i, K i ⊆ (c i).splitChart.source)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ i x, x ∈ K i → V x = (c i).descentField x := by
  obtain ⟨V₀, hV₀, hzero₀, hdesc₀, -⟩ := ManifoldMorse.exists_adaptedDescentField hf hm
  apply
    exists_closed_patch_descent_field V₀ hV₀ hzero₀ hdesc₀ K (fun i => (c i).splitChart.source) hK
      (fun i => (c i).splitChart.open_source) hKchart hdisj (fun i => (c i).descentField)
      (fun i => (c i).contMDiffOn_descentField)
  · exact fun i x hx hc => morse_descentField_zero_at_critical (c i) hf hx hc
  · intro i x hx hreg
    exact (c i).mvfderiv_descentField_neg hf hx (fun h => hreg (h.symm ▸ hp i))

attribute [local instance 100] Classical.propDecidable in
/-- A closed product block in split Morse coordinates. -/
def MorseCancellation.morseClosedBlock {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ) : Set M :=
  c.splitChart.symm ''
    (Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
      Metric.closedBall (0 : c.PositiveCoordinates) R)

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block lies in the chart source. -/
theorem MorseCancellation.morseClosedBlock_subset_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    morseClosedBlock c R ⊆ c.splitChart.source := by
  rintro x ⟨z, hz, rfl⟩
  exact c.splitChart.map_target' (hblock hz)

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block's height bound. -/
theorem MorseCancellation.morseClosedBlock_height {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    morseClosedBlock c R ⊆ f ⁻¹' Set.Icc (f p - R ^ 2) (f p + R ^ 2) := by
  rintro x ⟨z, hz, rfl⟩
  have hn : ‖z.1‖ ≤ R := mem_closedBall_zero_iff.mp hz.1
  have hp : ‖z.2‖ ≤ R := mem_closedBall_zero_iff.mp hz.2
  have hn2 : ‖z.1‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hp2 : ‖z.2‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  change f (c.splitChart.symm z) ∈ Set.Icc (f p - R ^ 2) (f p + R ^ 2)
  rw [c.splitChart_inverse_equation (hblock hz)]
  constructor <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block is a neighborhood of the critical point. -/
theorem MorseCancellation.morseClosedBlock_mem_nhds {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target)
    {z : c.NegativeCoordinates × c.PositiveCoordinates} (hn : ‖z.1‖ < R) (hp : ‖z.2‖ < R) :
    morseClosedBlock c R ∈ 𝓝 (c.splitChart.symm z) := by
  have hz : z ∈ c.splitChart.target :=
    hblock ⟨mem_closedBall_zero_iff.mpr hn.le, mem_closedBall_zero_iff.mpr hp.le⟩
  have hx : c.splitChart.symm z ∈ c.splitChart.source := c.splitChart.map_target' hz
  have hc : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have ho :
    Metric.ball (0 : c.NegativeCoordinates) R ×ˢ Metric.ball (0 : c.PositiveCoordinates) R ∈
      𝓝 (c.splitChart (c.splitChart.symm z)) := by
    rw [hc]
    exact
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
        ⟨mem_ball_zero_iff.mpr hn, mem_ball_zero_iff.mpr hp⟩
  have hnear := (c.splitChart.toOpenPartialHomeomorph.continuousAt hx) ho
  filter_upwards [c.splitChart.open_source.mem_nhds hx, hnear] with y hy hcy
  exact
    ⟨c.splitChart y, ⟨Metric.ball_subset_closedBall hcy.1, Metric.ball_subset_closedBall hcy.2⟩,
      c.splitChart.left_inv' hy⟩

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block is compact. -/
theorem MorseCancellation.isCompact_morseClosedBlock {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [FiniteDimensional ℝ E] (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    IsCompact (morseClosedBlock c R) :=
  (ProperSpace.isCompact_closedBall (0 : c.NegativeCoordinates) R).prod
      (ProperSpace.isCompact_closedBall (0 : c.PositiveCoordinates) R) |>.image_of_continuousOn
    (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono hblock)
