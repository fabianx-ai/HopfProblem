/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Morse.LinearPerturbation
public import Lib.Geometry.Manifold.Morse.CriticalPoints
public import Lib.Analysis.Calculus.MorseLemma.Cutoff

/-!
# Existence of Morse functions

`ManifoldPerturbation.perturb φ f a = f - ⟨a, φ · chart⟩` perturbs `f : M → ℝ` by a linear
function in a chart, cut off by a smooth bump `φ`. By Sard's theorem (via
`RegularValues.dense_regularValues`) and openness of the Morse condition, `f` Morse on a compact
`K` can be perturbed by an arbitrarily small `a` to be Morse also on a compact plateau of `φ`
(`ManifoldMorse.exists_morse_extension`); finitely many such steps give a Morse function on a
compact manifold (`ManifoldMorse.exists_morse_function`).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], Theorem 2.5
* [John Milnor, *Morse Theory*][milnor63], §6
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

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
