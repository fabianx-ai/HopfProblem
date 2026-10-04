/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.LinearPerturbation

/-!
# Nondegenerate critical points on a manifold

For `f : M → ℝ` on a manifold modelled on a real normed space `E` (model `𝓘(ℝ, E)`):
`ManifoldMorse.IsMorseAt E f x` (in some chart of the maximal atlas, `x` is regular or a
critical point with bijective Hessian), `IsMorseOn`, `IsMorse`, and the set
`criticalPoints E f` of zeros of `mfderiv f`. The Morse locus is open in smooth families
(`isOpen_isMorseAt`, `isOpen_isMorseOn`); the critical set is closed, discrete for a Morse
function (nondegenerate critical points are isolated: Milnor, *Morse Theory*, Corollary 2.3),
hence finite on a compact manifold (`finite_criticalPoints`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

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
