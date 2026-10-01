/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma

/-!
# Openness of the regular locus of a smooth family

For a smooth family `f : P → M → ℝ` (jointly smooth in `(a, x)`), the set of pairs `(a, x)` with
`x` a regular point of `f a` is open; hence for compact `K ⊆ M` the parameters `a` for which
`f a` has no critical point on `K` form an open set, and if near `a₀` the critical set of `f a`
is unchanged on an open neighbourhood `U` of the critical set of `f a₀`, it is eventually
unchanged everywhere. These are the stability statements behind small perturbations of Morse
functions (cf. Milnor, *Lectures on the h-cobordism theorem*, §2).

## Main results

* `ManifoldMorse.isOpen_regularPoint`, `ManifoldMorse.isOpen_regularOn`
* `ManifoldMorse.eventually_criticalPoints_eq`

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65]

## Tags

critical point, regular point, perturbation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Regular loci -/

/-- The regular-in-chart locus is open. -/
theorem ManifoldMorse.isOpen_regularInChart {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen {q : P × M | q.2 ∈ e.source ∧ fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0} := by
  have hU : IsOpen {q : P × E | q.2 ∈ e.target} := e.open_target.preimage continuous_snd
  have hd :=
    MorsePerturbation.contDiffOn_spatialDerivative (f := fun a y => f a (e.symm y)) hU
      (contDiffOn_inChart hf he)
  have hg :=
    hd.continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff, S]
  constructor
  · rintro ⟨hq, hn⟩
    exact ⟨hq, e.map_source hq, hn⟩
  · rintro ⟨hq, -, hn⟩
    exact ⟨hq, hn⟩

/-- For a jointly smooth family `f : P → M → ℝ`, the set of pairs `(a, x)` such that `x` is not a
critical point of `f a` is open in `P × M`. -/
theorem ManifoldMorse.isOpen_regularPoint {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | q.2 ∉ criticalPoints E (f q.1)} := by
  have hslice (a : P) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f a) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  rw [isOpen_iff_mem_nhds]
  intro q hq
  let e := chartAt E q.2
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas q.2
  have hx : q.2 ∈ e.source := mem_chart_source E q.2
  have hmem : q ∈ {r : P × M | r.2 ∈ e.source ∧ fderiv ℝ (f r.1 ∘ e.symm) (e r.2) ≠ 0} :=
    ⟨hx, fun hz => hq ((mem_criticalPoints_iff (hslice q.1) he hx).mpr hz)⟩
  apply Filter.mem_of_superset ((isOpen_regularInChart hf he).mem_nhds hmem)
  intro r hr hcrit
  exact hr.2 ((mem_criticalPoints_iff (hslice r.1) he hr.1).mp hcrit)

/-- The regular locus is open. -/
theorem ManifoldMorse.isOpen_regularOn {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) {K : Set M}
    (hK : IsCompact K) : IsOpen {a : P | ∀ x ∈ K, x ∉ criticalPoints E (f a)} :=
  MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_regularPoint hf)

/-- Let `f : P → M → ℝ` be a jointly smooth family on a compact manifold and `U` an open set
containing the critical points of `f a₀`. If for every parameter `a` the critical points of `f a`
in `U` are exactly those of `f a₀` in `U`, then for `a` near `a₀` the critical sets of `f a` and
`f a₀` are equal. -/
theorem ManifoldMorse.eventually_criticalPoints_eq {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) (a₀ : P) {U : Set M}
    (hU : IsOpen U) (hcover : criticalPoints E (f a₀) ⊆ U)
    (hfixed : ∀ a x, x ∈ U → (x ∈ criticalPoints E (f a) ↔ x ∈ criticalPoints E (f a₀))) :
    ∀ᶠ a in 𝓝 a₀, criticalPoints E (f a) = criticalPoints E (f a₀) := by
  have hreg : ∀ x ∈ Uᶜ, x ∉ criticalPoints E (f a₀) := fun x hx hc => hx (hcover hc)
  have hn := (isOpen_regularOn hf hU.isClosed_compl.isCompact).mem_nhds hreg
  filter_upwards [hn] with a ha
  ext x
  by_cases hx : x ∈ U
  · exact hfixed a x hx
  · exact iff_of_false (ha x hx) (hreg x hx)
