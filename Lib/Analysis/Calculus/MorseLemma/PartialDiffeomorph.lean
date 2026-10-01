/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Partial diffeomorphisms from the inverse function theorem

A `C^∞` map between real Banach spaces whose derivative at `a` is a continuous linear
isomorphism restricts to a partial diffeomorphism on a neighbourhood of `a` (the inverse function
theorem, cf. Mathlib's `ContDiffAt.toOpenPartialHomeomorph`, here packaged as a
`PartialDiffeomorph`). The file also collects the elementary operations on partial
diffeomorphisms of model spaces used in the proof of the Morse lemma.

## Main declarations

* `SmoothMorseLemma.exists_partialDiffeomorph_of_contDiffOn`,
  `SmoothMorseLemma.exists_partialDiffeomorph_of_contDiff`: the inverse function theorem.
* `SmoothMorseLemma.restrictChart`: restriction of a partial diffeomorphism to an open set.
* `SmoothMorseLemma.translationToZero`, `SmoothMorseLemma.translateChart`: precomposition with
  the translation `x ↦ x - a`.
* `SmoothMorseLemma.diffeomorphToPartialDiffeomorph`: a diffeomorphism as a partial one.
* `ManifoldMorse.chartPartialDiffeomorph`: a chart of the maximal `C^∞` atlas as a partial
  diffeomorphism.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

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
