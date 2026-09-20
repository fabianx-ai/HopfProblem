/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Topology.Algebra.FreeActionLocus
import Lib.Geometry.Manifold.Instances.RiemannSphere
/-!
# The one-point and branched quotient atlases

  The one-point atlas and the branched quotient atlas: charts on a quotient of a
  Riemann surface by a properly discontinuous action, pulled back through the
  quotient map, with the transition maps between the two presentations
  (Forster, Lectures on Riemann Surfaces, Section 1).
-/



open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Branched quotient atlases -/

/-- An atlas on a quotient where charts pull back to smooth local diffeomorphisms along `q`. -/
structure BranchedQuotientAtlas.Data {E M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] (q : M → Q) (ι : Type*) where
  chart : ι → OpenPartialHomeomorph Q E
  cover : ∀ x : Q, ∃ i, x ∈ (chart i).source
  continuous_project : Continuous q
  pullback_contMDiff :
    ∀ i,
      ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (chart i ∘ q)
        (q ⁻¹' (chart i).source)
  overlap_lift :
    ∀ i j,
      i ≠ j →
        ∀ z ∈ ((chart i).symm.trans (chart j)).source,
          ∃ a : M,
            q a = (chart i).symm z ∧
              IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
                (chart i ∘ q) a

/-- A chosen chart index covering a point. -/
def BranchedQuotientAtlas.Data.indexAt {E M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q} {ι : Type*}
    (D : BranchedQuotientAtlas.Data (E := E) q ι) (x : Q) : ι :=
  (D.cover x).choose

/-- The chosen chart covers the point. -/
theorem BranchedQuotientAtlas.Data.mem_chart_source {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (x : Q) :
    x ∈ (D.chart (D.indexAt x)).source :=
  (D.cover x).choose_spec

/-- The charted-space structure induced on the quotient. -/
@[instance_reducible]
def BranchedQuotientAtlas.Data.chartedSpace {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) : ChartedSpace E Q
    where
  atlas := Set.range D.chart
  chartAt x := D.chart (D.indexAt x)
  mem_chart_source := D.mem_chart_source
  chart_mem_atlas x := Set.mem_range_self (D.indexAt x)

/-- Each atlas chart lies in the induced atlas. -/
theorem BranchedQuotientAtlas.Data.chart_mem_atlas {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (i : ι) :
    letI := D.chartedSpace
    D.chart i ∈ atlas E Q :=
  Set.mem_range_self i

/-- The chart at a point is a chosen covering chart. -/
theorem BranchedQuotientAtlas.Data.chartAt_eq {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (x : Q) :
    letI := D.chartedSpace
    chartAt E x = D.chart (D.indexAt x) :=
  rfl

/-! ### The one-point atlas -/

/-- The chart on `Q` given by inclusion into the one-point compactification. -/
def OnePointAtlas.inclusionChart {Q : Type*} [TopologicalSpace Q] [Nonempty Q] :
    OpenPartialHomeomorph Q (OnePoint Q) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : Q → OnePoint Q)

/-- The inclusion chart has source all of `Q`. -/
@[simp]
theorem OnePointAtlas.inclusionChart_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q] :
    (inclusionChart (Q := Q)).source = Set.univ :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_source _

/-- The inclusion chart has target `Q` inside `OnePoint Q`. -/
@[simp]
theorem OnePointAtlas.inclusionChart_target {Q : Type*} [TopologicalSpace Q] [Nonempty Q] :
    (inclusionChart (Q := Q)).target = Set.range ((↑) : Q → OnePoint Q) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_target _

/-- The inverse inclusion chart is the coercion. -/
@[simp]
theorem OnePointAtlas.inclusionChart_symm_coe {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    (q : Q) : (inclusionChart (Q := Q)).symm (q : OnePoint Q) = q :=
  (inclusionChart (Q := Q)).left_inv (by simp)

/-- A chart of `Q` viewed as a chart of `OnePoint Q` away from infinity. -/
def OnePointAtlas.oldChart {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (q : Q) : OpenPartialHomeomorph (OnePoint Q) ℂ :=
  (inclusionChart (Q := Q)).symm.trans (chartAt ℂ q)

/-- The old chart computes the `Q` chart on coerced points. -/
@[simp]
theorem OnePointAtlas.oldChart_coe {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q x : Q) : oldChart q (x : OnePoint Q) = chartAt ℂ q x := by
  change chartAt ℂ q ((inclusionChart (Q := Q)).symm (x : OnePoint Q)) = _
  rw [inclusionChart_symm_coe]

/-- The old chart pulled back to `Q` is the original chart. -/
theorem OnePointAtlas.oldChart_comp_coe {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q : Q) : oldChart q ∘ ((↑) : Q → OnePoint Q) = chartAt ℂ q := by
  funext x
  exact oldChart_coe q x

/-- A coerced point lies in the old chart source exactly in `Q`. -/
@[simp]
theorem OnePointAtlas.coe_mem_oldChart_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q x : Q) :
    (x : OnePoint Q) ∈ (oldChart q).source ↔ x ∈ (chartAt ℂ q).source := by
  change
    ((x : OnePoint Q) ∈ (inclusionChart (Q := Q)).target ∧
        (inclusionChart (Q := Q)).symm (x : OnePoint Q) ∈ (chartAt ℂ q).source) ↔
      _
  simp only [inclusionChart_target, Set.mem_range_self, inclusionChart_symm_coe, true_and]

/-- The old chart source pulls back to the `Q` chart source. -/
theorem OnePointAtlas.oldChart_preimage_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q : Q) :
    ((↑) : Q → OnePoint Q) ⁻¹' (oldChart q).source = (chartAt ℂ q).source := by
  ext x
  exact coe_mem_oldChart_source q x

/-- Infinity is not in the old chart source. -/
theorem OnePointAtlas.infty_not_mem_oldChart_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q : Q) : ((OnePoint.infty) : OnePoint Q) ∉ (oldChart q).source := by
  intro hx
  have hr : ((OnePoint.infty) : OnePoint Q) ∈ Set.range ((↑) : Q → OnePoint Q) :=
    inclusionChart_target (Q := Q) ▸ hx.1
  obtain ⟨x, hx⟩ := hr
  exact OnePoint.coe_ne_infty x hx

/-- The old chart pulled back to `Q` is holomorphic. -/
theorem OnePointAtlas.oldChart_pullback_holomorphic {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] [IsManifold 𝓘(ℂ) ω Q] (q : Q) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (oldChart q ∘ ((↑) : Q → OnePoint Q))
      (((↑) : Q → OnePoint Q) ⁻¹' (oldChart q).source) := by
  rw [oldChart_comp_coe, oldChart_preimage_source]
  exact contMDiffOn_chart

/-- The pulled-back old chart is a local diffeomorphism. -/
theorem OnePointAtlas.oldChart_pullback_localDiffeomorph {Q : Type*} [TopologicalSpace Q]
    [Nonempty Q] [ChartedSpace ℂ Q] [IsManifold 𝓘(ℂ) ω Q] (q x : Q)
    (hx : (x : OnePoint Q) ∈ (oldChart q).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (oldChart q ∘ ((↑) : Q → OnePoint Q)) x := by
  rw [oldChart_comp_coe]
  refine
    ⟨{  toPartialEquiv := (chartAt ℂ q).toPartialEquiv
        open_source := (chartAt ℂ q).open_source
        open_target := (chartAt ℂ q).open_target
        contMDiffOn_toFun := contMDiffOn_chart
        contMDiffOn_invFun := contMDiffOn_chart_symm }, ?_, ?_⟩
  · exact (coe_mem_oldChart_source q x).mp hx
  · exact Set.eqOn_refl _ _

/-- The atlas of `OnePoint Q`: a chart at infinity plus the old charts. -/
def OnePointAtlas.chart {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (e : OpenPartialHomeomorph (OnePoint Q) ℂ) : Option Q → OpenPartialHomeomorph (OnePoint Q) ℂ
  | none => e
  | some q => oldChart q

/-- The one-point atlas covers `OnePoint Q`. -/
theorem OnePointAtlas.chart_cover {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (e : OpenPartialHomeomorph (OnePoint Q) ℂ) (he : ((OnePoint.infty) : OnePoint Q) ∈ e.source)
    (x : OnePoint Q) : ∃ i, x ∈ (chart e i).source := by
  induction x using OnePoint.rec
  · exact ⟨Option.none, he⟩
  · rename_i q
    exact ⟨Option.some q, (coe_mem_oldChart_source q q).mpr (mem_chart_source ℂ q)⟩

/-- Chart overlaps never return to infinity. -/
theorem OnePointAtlas.overlap_ne_infty {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (e : OpenPartialHomeomorph (OnePoint Q) ℂ) (i j : Option Q) (hij : i ≠ j)
    (z : ℂ) (hz : z ∈ ((chart e i).symm.trans (chart e j)).source) :
    (chart e i).symm z ≠ ((OnePoint.infty) : OnePoint Q) := by
  intro hinfty
  cases i with
  | some q =>
    apply infty_not_mem_oldChart_source q
    rw [← hinfty]
    exact (oldChart q).map_target hz.1
  | none =>
    cases j with
    | none => exact hij rfl
    | some q =>
      apply infty_not_mem_oldChart_source q
      rw [← hinfty]
      exact hz.2

/-- The one-point atlas packaged as branched quotient atlas data. -/
def OnePointAtlas.data {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (e : OpenPartialHomeomorph (OnePoint Q) ℂ) [IsManifold 𝓘(ℂ) ω Q]
    (he : ((OnePoint.infty) : OnePoint Q) ∈ e.source)
    (hholo :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ ((↑) : Q → OnePoint Q)) (((↑) : Q → OnePoint Q) ⁻¹' e.source))
    (hlocal :
      ∀ x : Q,
        (x : OnePoint Q) ∈ e.source →
          IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ ((↑) : Q → OnePoint Q)) x) :
    BranchedQuotientAtlas.Data (E := ℂ) ((↑) : Q → OnePoint Q) (Option Q)
    where
  chart := chart e
  cover := chart_cover e he
  continuous_project := OnePoint.continuous_coe
  pullback_contMDiff
    i := by
    cases i with
    | none => exact hholo
    | some q => exact oldChart_pullback_holomorphic q
  overlap_lift i j hij z
    hz := by
    have hne := overlap_ne_infty e i j hij z hz
    obtain ⟨x, hx⟩ : ∃ x : Q, (x : OnePoint Q) = (chart e i).symm z := by
      induction h : (chart e i).symm z using OnePoint.rec
      · exact (hne h).elim
      · rename_i x
        exact ⟨x, rfl⟩
    have hsource : (x : OnePoint Q) ∈ (chart e i).source := by
      rw [hx]
      exact (chart e i).map_target hz.1
    refine ⟨x, hx, ?_⟩
    cases i with
    | none => exact hlocal x hsource
    | some q => exact oldChart_pullback_localDiffeomorph q x hsource

theorem BranchedQuotientAtlas.project_localInverse_eventuallyEq {E M Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace Q] {q : M → Q} (hq : Continuous q) (e : OpenPartialHomeomorph Q E) {z : E}
    (hz : z ∈ e.target) {a : M} (ha : q a = e.symm z)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (e ∘ q) a) :
    q ∘ hf.localInverse =ᶠ[𝓝 z] e.symm := by
  have hcoord : (e ∘ q) a = z := by simp only [Function.comp_apply, ha, e.right_inv hz]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hcont : ContinuousAt (q ∘ hf.localInverse) z := by
    have h := hq.continuousAt.comp hf.localInverse_contMDiffAt.continuousAt
    simpa only [hcoord] using h
  have hsource : ∀ᶠ w in 𝓝 z, q (hf.localInverse w) ∈ e.source :=
    hcont
      (e.open_source.mem_nhds
        (by simpa only [Function.comp_apply, hinv, ha] using e.map_target hz))
  have hright : ∀ᶠ w in 𝓝 z, e (q (hf.localInverse w)) = w := by
    rw [← hcoord]
    exact hf.localInverse_eventuallyEq_right
  filter_upwards [hsource, hright] with w hw he
  change q (hf.localInverse w) = e.symm w
  exact (e.left_inv hw).symm.trans (congrArg e.symm he)

theorem BranchedQuotientAtlas.contDiffAt_transition_of_lift {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    (hq : Continuous q) (e f : OpenPartialHomeomorph Q E)
    (hhol :
      ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (f ∘ q)
        (q ⁻¹' f.source))
    {z : E} (hz : z ∈ (e.symm.trans f).source) {a : M} (ha : q a = e.symm z)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (e ∘ q) a) :
    ContDiffAt ℂ ω (e.symm.trans f) z := by
  have hcoord : (e ∘ q) a = z := by simp only [Function.comp_apply, ha, e.right_inv hz.1]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hfirst :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω hf.localInverse z := by
    simpa only [hcoord] using hf.localInverse_contMDiffAt
  have hsecond : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (f ∘ q) a :=
    hhol.contMDiffAt
      ((f.open_source.preimage hq).mem_nhds
        (by
          change q a ∈ f.source
          rw [ha]
          exact hz.2))
  have hcomp : ContDiffAt ℂ ω ((f ∘ q) ∘ hf.localInverse) z :=
    (hsecond.comp_of_eq hfirst hinv).contDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [project_localInverse_eventuallyEq hq e hz.1 ha hf] with w hw
  change f (e.symm w) = f (q (hf.localInverse w))
  exact congrArg f hw.symm

theorem BranchedQuotientAtlas.Data.contDiffOn_transition {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (i j : ι) :
    ContDiffOn ℂ ω ((D.chart i).symm.trans (D.chart j))
      ((D.chart i).symm.trans (D.chart j)).source := by
  intro z hz
  by_cases hij : i = j
  · subst j
    apply contDiffWithinAt_id.congr_of_mem ?_ hz
    intro w hw
    exact (D.chart i).right_inv hw.1
  · obtain ⟨a, ha, hf⟩ := D.overlap_lift i j hij z hz
    exact
      (BranchedQuotientAtlas.contDiffAt_transition_of_lift D.continuous_project (D.chart i)
          (D.chart j) (D.pullback_contMDiff j) hz ha hf).contDiffWithinAt

theorem BranchedQuotientAtlas.Data.isManifold {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) :
    letI := D.chartedSpace
    IsManifold (modelWithCornersSelf ℂ E) ω Q := by
  let := D.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e f ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using D.contDiffOn_transition i j

theorem BranchedQuotientAtlas.Data.contMDiff_project {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) :
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω q := by
  let := D.chartedSpace
  let := D.isManifold
  intro a
  have hsource := D.mem_chart_source (q a)
  have hhol :=
    (D.pullback_contMDiff (D.indexAt (q a))).contMDiffAt
      (((D.chart (D.indexAt (q a))).open_source.preimage D.continuous_project).mem_nhds hsource)
  apply
    (contMDiffAt_iff_target_of_mem_source (I := (modelWithCornersSelf ℂ E)) (I' :=
        (modelWithCornersSelf ℂ E)) (D.mem_chart_source (q a))).mpr
  refine ⟨D.continuous_project.continuousAt, ?_⟩
  simpa [extChartAt, OpenPartialHomeomorph.extend, D.chartAt_eq, Function.comp_def] using hhol
