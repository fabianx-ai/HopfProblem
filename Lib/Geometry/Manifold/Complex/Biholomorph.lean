/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/



import Lib.Analysis.Complex.Mobius
import Lib.Geometry.Manifold.Instances.RiemannSphere
import Mathlib

/-!
# Biholomorphs of Riemann surfaces

A bijective holomorphic map with holomorphic inverse between Riemann surfaces, built from a
homeomorphism plus holomorphicity on one side (`biholomorphOfHomeomorph`), with the
continuity/regularity transfer lemmas (`contMDiff_of_continuous_of_finite`,
`contMDiff_symm_of_contMDiff`, `contMDiffAt_of_continuousAt_of_punctured`,
`differentiableOn_symm_of_differentiableOn`) — Forster §1–2.

## Main definitions and results

* `TriangleUniformizationGluing.biholomorphOfHomeomorph` : a homeomorphism holomorphic in
  one direction between Riemann surfaces is a biholomorph.
* `TriangleUniformizationGluing.contMDiff_symm_of_contMDiff` : the inverse is smooth.

## References

* [Otto Forster, *Lectures on Riemann Surfaces*][forster81], §1–2

## Tags

biholomorph, Riemann surface, inverse function
-/


open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Removability of smoothness at punctured points -/

/-- The inverse of a chart tends to `x` on the punctured neighborhood of `e x`. -/
theorem
  TriangleUniformizationGluing.openPartialHomeomorph_symm_tendsto_punctured
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    {x : X} (hx : x ∈ e.source) : Filter.Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨(e.tendsto_symm hx).mono_left nhdsWithin_le_nhds, ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, e.left_inv hx] using
    e.symm.eventually_ne_nhdsWithin (e.map_source hx)

/-- A continuous map smooth on a punctured neighborhood is smooth at the point. -/
theorem TriangleUniformizationGluing.contMDiffAt_of_continuousAt_of_punctured {M N : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {f : M → N} {x : M} (hf : ContinuousAt f x)
    (hd : ∀ᶠ z in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let e := chartAt ℂ x
  let e' := chartAt ℂ (f x)
  let F : ℂ → ℂ := e' ∘ f ∘ e.symm
  have hxe : x ∈ e.source := ChartedSpace.mem_chart_source x
  have hye : f x ∈ e'.source := ChartedSpace.mem_chart_source (f x)
  have hcF : ContinuousAt F (e x) := by
    have hcomposed : Filter.Tendsto F (𝓝 (e x)) (𝓝 (e' (f x))) :=
      (e'.continuousAt hye).tendsto.comp (hf.tendsto.comp (e.tendsto_symm hxe))
    simpa only [ContinuousAt, F, Function.comp_apply, e.left_inv hxe] using hcomposed
  have hdomain : ∀ᶠ z in 𝓝 (e x), z ∈ e.target := e.open_target.mem_nhds (e.map_source hxe)
  have htarget : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ e'.source :=
    (hf.tendsto.comp (e.tendsto_symm hxe)).eventually (e'.open_source.mem_nhds hye)
  have hdiff : ∀ᶠ z in 𝓝[≠] (e x), DifferentiableAt ℂ F z := by
    filter_upwards [(openPartialHomeomorph_symm_tendsto_punctured e hxe).eventually
        hd,
      eventually_nhdsWithin_of_eventually_nhds hdomain,
      eventually_nhdsWithin_of_eventually_nhds htarget] with z hz hzDomain hzTarget
    have hcoords : ContDiffAt ℂ ω F (e (e.symm z)) := by
      have h :=
        (contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (x := x) (y := f x)
              (e.map_target hzDomain) hzTarget).mp
          hz
      simpa only [e, e', F, mfld_simps, contDiffWithinAt_univ] using h.2
    rw [e.right_inv hzDomain] at hcoords
    exact hcoords.differentiableAt (by simp)
  have ha := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcF
  apply contMDiffAt_iff.mpr
  refine ⟨hf, ?_⟩
  have hsm : ContDiffAt ℂ ω F (e x) := ha.contDiffAt
  simpa only [e, e', F, mfld_simps] using hsm.contDiffWithinAt (s := Set.univ)

/-- A continuous map smooth off a finite set is smooth everywhere. -/
theorem TriangleUniformizationGluing.contMDiff_of_continuous_of_finite {M N : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {f : M → N} {S : Set M} (hf : Continuous f)
    (hS : S.Finite) (hd : ∀ z ∉ S, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have : T1Space M := ChartedSpace.t1Space ℂ M
  intro x
  apply contMDiffAt_of_continuousAt_of_punctured hf.continuousAt
  have hclosed : IsClosed (S \ { x }) := (hS.subset Set.sdiff_subset).isClosed
  have haway : (S \ { x })ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds haway, self_mem_nhdsWithin] with z hz
    hzx
  exact hd z (fun hzS => hz ⟨hzS, hzx⟩)

/-- The derivative of a differentiable chart is nonzero on a punctured neighborhood. -/
theorem TriangleUniformizationGluing.eventually_deriv_ne_zero_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ) (he : DifferentiableOn ℂ e e.source) {a : ℂ}
    (ha : a ∈ e.source) : ∀ᶠ z in 𝓝[≠] a, deriv e z ≠ 0 := by
  have hda : AnalyticAt ℂ (deriv e) a := (he.analyticAt (e.open_source.mem_nhds ha)).deriv
  rcases hda.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · exfalso
    have hnear : ∀ᶠ z in 𝓝 a, z ∈ e.source ∧ deriv e z = 0 := by
      filter_upwards [e.open_source.mem_nhds ha, hzero] with z hz hdz
      exact ⟨hz, hdz⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hballSource : Metric.ball a r ⊆ e.source := fun z hz => (hball hz).1
    have hconstant : ∀ z ∈ Metric.ball a r, e z = e a := by
      intro z hz
      exact
        Metric.isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
          (he.mono hballSource) (fun w hw => (hball hw).2) hz (Metric.mem_ball_self hr)
    have hballNhds : ∀ᶠ z in 𝓝 a, z ∈ Metric.ball a r := Metric.ball_mem_nhds a hr
    have hballPunctured : ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a r :=
      hballNhds.filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz, hza⟩ :=
      (hballPunctured.and (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] a, z ≠ a)).exists
    exact hza (e.injOn (hballSource hz) ha (hconstant z hz))
  · exact hnonzero

/-- The inverse of a differentiable chart is differentiable on its target. -/
theorem TriangleUniformizationGluing.differentiableOn_symm_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ) (he : DifferentiableOn ℂ e e.source) :
    DifferentiableOn ℂ e.symm e.target := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  apply AnalyticAt.differentiableAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hnonzero := eventually_deriv_ne_zero_of_differentiableOn e he (e.map_target hw)
    rw [eventually_nhdsWithin_iff] at hnonzero
    have hnear := (e.continuousAt_symm hw).tendsto.eventually hnonzero
    rw [eventually_nhdsWithin_iff]
    filter_upwards [e.open_target.mem_nhds hw, hnear] with z hz hdz hzw
    have hinvNe : e.symm z ≠ e.symm w := fun h => hzw (e.symm.injOn hz hw h)
    exact
      (e.hasDerivAt_symm hz (hdz hinvNe)
          (he.hasDerivAt (e.open_source.mem_nhds (e.map_target hz)))).differentiableAt
  · exact e.continuousAt_symm hw

/-- The inverse of a smooth homeomorphism of complex manifolds is smooth. -/
theorem TriangleUniformizationGluing.contMDiff_symm_of_contMDiff {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N] (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm := by
  intro y
  let c : OpenPartialHomeomorph ℂ ℂ :=
    ((chartAt ℂ (e.symm y)).symm.trans e.toOpenPartialHomeomorph).trans (chartAt ℂ y)
  have hc : DifferentiableOn ℂ c c.source := by
    intro z hz
    have hz₁ : z ∈ (chartAt ℂ (e.symm y)).target := hz.1.1
    have hz₂ : e ((chartAt ℂ (e.symm y)).symm z) ∈ (chartAt ℂ y).source := hz.2
    have h₁ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (e.symm y)).symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (e.symm y)) hz₁
    have h₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y) (e ((chartAt ℂ (e.symm y)).symm z)) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y) hz₂
    exact
      ((h₂.comp z ((he _).comp z h₁)).contDiffAt.differentiableAt
          (by simp)).differentiableWithinAt
  have hy : (chartAt ℂ y) y ∈ c.target := by
    refine ⟨(chartAt ℂ y).map_source (mem_chart_source ℂ y), ?_⟩
    change
      (chartAt ℂ y).symm ((chartAt ℂ y) y) ∈ (Set.univ : Set N) ∧
        e.symm ((chartAt ℂ y).symm ((chartAt ℂ y) y)) ∈ (chartAt ℂ (e.symm y)).source
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact ⟨Set.mem_univ _, mem_chart_source ℂ _⟩
  have hinv : ContDiffAt ℂ ω c.symm ((chartAt ℂ y) y) :=
    ((differentiableOn_symm_of_differentiableOn c hc).contDiffOn c.open_target).contDiffAt
      (c.open_target.mem_nhds hy)
  change
    ContDiffAt ℂ ω ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) at hinv
  apply contMDiffAt_iff.mpr
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    contDiffWithinAt_univ] using hinv

/-! ### Promoting a homeomorphism to a biholomorphism -/

/-- A homeomorphism smooth in both directions upgraded to a diffeomorphism of complex manifolds. -/
def TriangleUniformizationGluing.biholomorphOfHomeomorph {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω M]
    [IsManifold 𝓘(ℂ) ω N] (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) M N ω where
  toEquiv := e.toEquiv
  contMDiff_toFun := he
  contMDiff_invFun := contMDiff_symm_of_contMDiff e he

/-- The underlying homeomorphism of the upgraded biholomorphism is the original one. -/
@[simp]
theorem TriangleUniformizationGluing.biholomorphOfHomeomorph_toHomeomorph {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N] (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    (biholomorphOfHomeomorph e he).toHomeomorph = e := by
  ext x
  rfl
