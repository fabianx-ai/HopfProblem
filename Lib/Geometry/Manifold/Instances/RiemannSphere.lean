/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# The Riemann sphere and its two affine charts

`RiemannSphere` is the Riemann sphere `ℂ ⊔ {∞}`, presented through two affine charts
(`TwoAffineCharts`: a chart flag with inversion between the finite and infinite patches),
the infinity parametrization (`infinityParametrization_*`), and the resulting
charted-space and manifold instances.

## Main definitions and results

* `TwoAffineCharts` : the two-chart atlas data (left/right patches, inversion).
* `RiemannSphere` : the sphere type; `RiemannSphere.infinityParametrization_*` : the
  parametrization at infinity.
* The charted-space and `IsManifold` instances for the standard complex model.

## References

* [Otto Forster, *Lectures on Riemann Surfaces*][forster81], §1 (the sphere ℙ¹ as two charts)

## Tags

Riemann sphere, affine charts, manifold instance
-/



open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### The two-affine-chart gluing -/

/-- The space glued from two affine charts by inversion. -/
structure TwoAffineCharts (Y : Type*) [TopologicalSpace Y] where
  left : ℂ → Y
  right : ℂ → Y
  continuous_left : Continuous left
  continuous_right : Continuous right
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  inversion : ∀ z : ℂ, z ≠ 0 → left z = right z⁻¹
  endpoints_ne : left 0 ≠ right 0
  covered : ∀ y : Y, (∃ z, left z = y) ∨ ∃ z, right z = y

/-- A left point is not a right zero. -/
theorem TwoAffineCharts.left_ne_right_zero {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) (z : ℂ) : A.left z ≠ A.right 0 := by
  by_cases hz : z = 0
  · subst z
    exact A.endpoints_ne
  · intro h
    have h' := A.right_injective ((A.inversion z hz).symm.trans h)
    exact inv_ne_zero hz h'

/-- Equality across the two charts is the inversion relation. -/
theorem TwoAffineCharts.cross_eq_iff {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (z w : ℂ) : A.left z = A.right w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  constructor
  · intro h
    have hw : w ≠ 0 := by
      rintro rfl
      exact A.left_ne_right_zero z h
    have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw)
    have hz : z = w⁻¹ := A.left_injective (h.trans hi.symm)
    refine ⟨by rw [hz]; exact inv_ne_zero hw, ?_⟩
    rw [hz, inv_inv]
  · rintro ⟨hz, rfl⟩
    exact A.inversion z hz

/-- The swapped two-chart gluing. -/
def TwoAffineCharts.symm {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y) :
    TwoAffineCharts Y where
  left := A.right
  right := A.left
  continuous_left := A.continuous_right
  continuous_right := A.continuous_left
  left_injective := A.right_injective
  right_injective := A.left_injective
  inversion z hz := by simpa using (A.inversion z⁻¹ (inv_ne_zero hz)).symm
  endpoints_ne := A.endpoints_ne.symm
  covered y := (A.covered y).symm

/-- The extension of a two-chart point to the sphere model. -/
def TwoAffineCharts.extension {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (p : OnePoint ℂ) : Y :=
  p.elim (A.right 0) A.left

/-- The extension is injective. -/
theorem TwoAffineCharts.extension_injective {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) : Function.Injective A.extension := by
  intro p q h
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => rfl
    | coe w => exact False.elim (A.left_ne_right_zero w h.symm)
  | coe z =>
    induction q using OnePoint.rec with
    | infty => exact False.elim (A.left_ne_right_zero z h)
    | coe w => exact congrArg ((↑) : ℂ → OnePoint ℂ) (A.left_injective h)

/-- The extension is surjective. -/
theorem TwoAffineCharts.extension_surjective {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) : Function.Surjective A.extension := by
  intro y
  obtain ⟨z, hz⟩ | ⟨w, hw⟩ := A.covered y
  · exact ⟨(z : OnePoint ℂ), hz⟩
  · by_cases hw0 : w = 0
    · subst w
      exact ⟨(OnePoint.infty), hw⟩
    · refine ⟨(w⁻¹ : ℂ), ?_⟩
      change A.left w⁻¹ = y
      have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw0)
      exact hi.trans hw

/-- The extension is continuous. -/
theorem TwoAffineCharts.extension_continuous {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) : Continuous A.extension := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Filter.Tendsto A.left (Filter.coclosedCompact ℂ) (𝓝 (A.right 0))
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have h : Filter.Tendsto (fun z : ℂ => A.right z⁻¹) (Bornology.cobounded ℂ) (𝓝 (A.right 0)) :=
      A.continuous_right.continuousAt.tendsto.comp Filter.tendsto_inv₀_cobounded
    apply h.congr'
    filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (A.inversion z hz).symm
  · exact A.continuous_left

/-- The two-chart space is homeomorphic to its model. -/
def TwoAffineCharts.homeomorph {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    [T2Space Y] : OnePoint ℂ ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective A.extension ⟨A.extension_injective, A.extension_surjective⟩)
    A.extension_continuous

/-- The left chart is an open embedding. -/
theorem TwoAffineCharts.left_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) [T2Space Y] : Topology.IsOpenEmbedding A.left := by
  have h := A.homeomorph.isOpenEmbedding.comp (OnePoint.isOpenEmbedding_coe (X := ℂ))
  exact h

/-- The right chart is an open embedding. -/
theorem TwoAffineCharts.right_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) [T2Space Y] : Topology.IsOpenEmbedding A.right :=
  A.symm.left_isOpenEmbedding

/-- The left chart's range is the complement of the right zero. -/
theorem TwoAffineCharts.range_left {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y) :
    Set.range A.left = {A.right 0}ᶜ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact A.left_ne_right_zero z
  · intro hy
    change y ≠ A.right 0 at hy
    obtain ⟨z, hz⟩ | ⟨w, hw⟩ := A.covered y
    · exact ⟨z, hz⟩
    · have hw0 : w ≠ 0 := fun h => hy (by rw [← hw, h])
      refine ⟨w⁻¹, ?_⟩
      have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw0)
      exact hi.trans hw

/-- The right chart's range is the complement of the left zero. -/
theorem TwoAffineCharts.range_right {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y) :
    Set.range A.right = {A.left 0}ᶜ :=
  A.symm.range_left

/-- The affine map of a two-chart point. -/
def TwoAffineCharts.affineMap {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (b : Bool) : ℂ → Y :=
  if b then A.right else A.left

/-- The affine map is an open embedding. -/
theorem TwoAffineCharts.affineMap_isOpenEmbedding {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) : Topology.IsOpenEmbedding (A.affineMap b) := by
  cases b
  · exact A.left_isOpenEmbedding
  · exact A.right_isOpenEmbedding

/-- Equality of affine maps is the inversion relation. -/
theorem TwoAffineCharts.affineMap_cross_eq_iff {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) (b : Bool) (z w : ℂ) :
    A.affineMap b z = A.affineMap (!b) w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  cases b
  · exact A.cross_eq_iff z w
  · exact A.symm.cross_eq_iff z w

/-- The affine map computes the inversion. -/
theorem TwoAffineCharts.affineMap_inversion {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    A.affineMap b z = A.affineMap (!b) z⁻¹ :=
  (A.affineMap_cross_eq_iff b z z⁻¹).mpr ⟨hz, rfl⟩

/-- The parametrization of the two-chart space. -/
def TwoAffineCharts.parametrization {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) : OpenPartialHomeomorph ℂ Y :=
  (A.affineMap_isOpenEmbedding b).toOpenPartialHomeomorph (A.affineMap b)

/-- The parametrization lands in the target. -/
@[simp]
theorem TwoAffineCharts.parametrization_target {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) :
    (A.parametrization b).target = Set.range (A.affineMap b) := by simp [parametrization]

/-- The parametrization inverse computes the chart point. -/
@[simp]
theorem TwoAffineCharts.parametrization_symm_apply {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) (z : ℂ) :
    (A.parametrization b).symm (A.affineMap b z) = z :=
  (A.parametrization b).left_inv (Set.mem_univ z)

/-- The chart transition is the inversion. -/
theorem TwoAffineCharts.transition_cross {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) (z : ℂ)
    (hz : z ∈ ((A.parametrization b).trans (A.parametrization (!b)).symm).source) :
    z ≠ 0 ∧ ((A.parametrization b).trans (A.parametrization (!b)).symm) z = z⁻¹ := by
  have hparam (b : Bool) (z : ℂ) : A.parametrization b z = A.affineMap b z := rfl
  have hy : A.affineMap b z ∈ Set.range (A.affineMap (!b)) := by simpa [hparam] using hz.2
  obtain ⟨w, hw⟩ := hy
  have hn := ((A.affineMap_cross_eq_iff b z w).mp hw.symm).1
  refine ⟨hn, ?_⟩
  change (A.parametrization (!b)).symm (A.affineMap b z) = z⁻¹
  rw [A.affineMap_inversion b z hn, parametrization_symm_apply]

/-- The chart transition is holomorphic. -/
theorem TwoAffineCharts.transition_holomorphic {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b c : Bool) :
    ContDiffOn ℂ ω ((A.parametrization b).trans (A.parametrization c).symm)
      ((A.parametrization b).trans (A.parametrization c).symm).source := by
  by_cases hbc : b = c
  · subst c
    apply contDiffOn_id.congr
    intro z _
    exact A.parametrization_symm_apply b z
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    have hi :
      ContDiffOn ℂ ω (fun z : ℂ => z⁻¹)
        ((A.parametrization b).trans (A.parametrization (!b)).symm).source := by
      intro z hz
      exact (contDiffAt_inv ℂ (A.transition_cross b z hz).1).contDiffWithinAt
    exact hi.congr (fun z hz => (A.transition_cross b z hz).2)

/-- The preferred chart at a point. -/
def TwoAffineCharts.preferredChart {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (y : Y) : Bool := by classical exact if y ∈ Set.range A.left then Bool.false else Bool.true

/-- A point lies in its preferred chart. -/
theorem TwoAffineCharts.preferred_mem {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (y : Y) : y ∈ Set.range (A.affineMap (A.preferredChart y)) := by
  classical
  by_cases hy : y ∈ Set.range A.left
  · simp [preferredChart, hy, affineMap]
  · obtain h | h := A.covered y
    · exact False.elim (hy h)
    · simpa [preferredChart, hy, affineMap] using h

/-- The two-chart space's charted-space structure. -/
@[instance_reducible]
def TwoAffineCharts.chartedSpace {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) : ChartedSpace ℂ Y
    where
  atlas := Set.range (fun b : Bool => (A.parametrization b).symm)
  chartAt y := (A.parametrization (A.preferredChart y)).symm
  mem_chart_source
    y := by
    change y ∈ (A.parametrization (A.preferredChart y)).target
    rw [parametrization_target]
    exact A.preferred_mem y
  chart_mem_atlas _ := Set.mem_range_self _

/-- The two-chart space is a smooth manifold. -/
theorem TwoAffineCharts.isManifold {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) :
    letI := A.chartedSpace
    IsManifold (modelWithCornersSelf ℂ ℂ) ω Y := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨b, rfl⟩ := he
  obtain ⟨c, rfl⟩ := he'
  simpa using A.transition_holomorphic b c

/-- The affine map is holomorphic. -/
theorem TwoAffineCharts.affineMap_holomorphic {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (A.affineMap b) := by
  let := A.chartedSpace
  let := A.isManifold
  have he : (A.parametrization b).symm ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ω Y :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self b)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (A.affineMap b)
      Set.univ at h
  exact contMDiffOn_univ.mp h

/-- A map smooth in both affine charts is smooth. -/
theorem TwoAffineCharts.contMDiff_of_comp_affineMaps {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] (I : ModelWithCorners ℂ F H)
    (f : Y → N) (hf : ∀ b, ContMDiff (modelWithCornersSelf ℂ ℂ) I ω (f ∘ A.affineMap b)) :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) I ω f := by
  have hparam (b : Bool) (z : ℂ) : A.parametrization b z = A.affineMap b z := rfl
  let := A.chartedSpace
  intro y
  rw [contMDiffAt_iff_source]
  have hchart : chartAt ℂ y = (A.parametrization (A.preferredChart y)).symm := rfl
  simpa [hparam, extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    (hf (A.preferredChart y)).contMDiffAt.contMDiffWithinAt (s := Set.univ) (x :=
      (A.parametrization (A.preferredChart y)).symm y)

/-! ### The Riemann sphere -/

/-- The Riemann sphere: the two-chart gluing `ℂ ∪ {∞}`. -/
abbrev RiemannSphere :=
  OnePoint ℂ

/-- The parametrization `ℂ ∪ {∞} → sphere`. -/
def RiemannSphere.infinityParametrization (z : ℂ) : RiemannSphere := by
  classical exact if z = 0 then ((OnePoint.infty) : RiemannSphere) else (z⁻¹ : ℂ)

/-- The parametrization sends `0` to `∞`. -/
@[simp]
theorem RiemannSphere.infinityParametrization_zero :
    infinityParametrization 0 = ((OnePoint.infty) : RiemannSphere) := by
  simp [infinityParametrization]

/-- The parametrization computes `1/z` off zero. -/
theorem RiemannSphere.infinityParametrization_of_ne {z : ℂ} (hz : z ≠ 0) :
    infinityParametrization z = (z⁻¹ : ℂ) := by simp [infinityParametrization, hz]

/-- The infinity parametrization is continuous. -/
theorem RiemannSphere.infinityParametrization_continuous : Continuous infinityParametrization := by
  classical
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    change Filter.Tendsto infinityParametrization (𝓝 (0 : ℂ)) (𝓝 (infinityParametrization 0))
    rw [infinityParametrization_zero, ← nhdsNE_sup_pure (0 : ℂ), Filter.tendsto_sup]
    constructor
    · have hc :
        Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ)
          (𝓝 ((OnePoint.infty) : RiemannSphere)) := by
        simpa only [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
          (OnePoint.tendsto_coe_infty (X := ℂ))
      have hi := hc.comp (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
      apply hi.congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 0 := hw
      simp [infinityParametrization, hw']
    · simpa only [infinityParametrization_zero] using
        (tendsto_pure_nhds infinityParametrization (0 : ℂ))
  · have hc : ContinuousAt (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
      OnePoint.continuous_coe.continuousAt.comp (contDiffAt_inv ℂ hz (n := ω)).continuousAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
    exact infinityParametrization_of_ne hw

/-- The infinity parametrization is injective. -/
theorem RiemannSphere.infinityParametrization_injective :
    Function.Injective infinityParametrization := by
  classical
  intro z w he
  by_cases hz : z = 0 <;> by_cases hw : w = 0
  · exact hz.trans hw.symm
  · simp [infinityParametrization, hz, hw] at he
  · simp [infinityParametrization, hz, hw] at he
  · simpa [infinityParametrization, hz, hw] using he

/-- The two standard charts of the sphere. -/
def RiemannSphere.standardCharts : TwoAffineCharts RiemannSphere
    where
  left := ((↑) : ℂ → OnePoint ℂ)
  right := infinityParametrization
  continuous_left := OnePoint.continuous_coe
  continuous_right := infinityParametrization_continuous
  left_injective := OnePoint.coe_injective
  right_injective := infinityParametrization_injective
  inversion z hz := by simp [infinityParametrization, inv_ne_zero hz]
  endpoints_ne := by simp [infinityParametrization]
  covered
    p := by
    induction p using OnePoint.rec with
    | infty => exact Or.inr ⟨0, infinityParametrization_zero⟩
    | coe z => exact Or.inl ⟨z, rfl⟩

/-- The sphere's charted-space structure. -/
instance RiemannSphere.chartedSpace : ChartedSpace ℂ RiemannSphere :=
  standardCharts.chartedSpace

/-- The Riemann sphere is a smooth manifold. -/
instance RiemannSphere.isManifold : IsManifold (modelWithCornersSelf ℂ ℂ) ω RiemannSphere :=
  standardCharts.isManifold
