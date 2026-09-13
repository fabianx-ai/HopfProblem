/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Covering and discrete quotients

  Quotient covers: the quotient of a space by a properly discontinuous group of
  local homeomorphisms is a covering map, the discreteness of the fiber
  difference set, and the induced smooth structure (Forster, Lectures on Riemann
  Surfaces, Sections 1-3).
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Discrete-quotient smoothness -/

/-- A continuous map differing from the identity by a discrete-submodule value is smooth. -/
theorem contDiffOn_of_sub_mem_discrete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {f : E → E} {s : Set E} (hf : ContinuousOn f s)
    (hL : ∀ x ∈ s, f x - x ∈ L) (n : ℕ∞ω) : ContDiffOn ℂ n f s := by
  let g : s → L := fun x => ⟨f x - x, hL x x.property⟩
  have hg : Continuous g := (hf.domRestrict.sub continuous_subtype_val).subtype_mk _
  have hg' : IsLocallyConstant g := (IsLocallyConstant.iff_continuous g).mpr hg
  intro x hx
  have heq : ∀ᶠ y in 𝓝[s] x, f y - y = f x - x := by
    apply (eventually_nhds_subtype_iff s ⟨x, hx⟩ _).mp
    exact (hg'.eventually_eq ⟨x, hx⟩).mono fun y hy => congrArg Subtype.val hy
  apply
    (contDiff_id.add contDiff_const).contDiffWithinAt.congr_of_eventuallyEq_of_mem (s := s) (f :=
      fun y => y + (f x - x)) ?_ hx
  exact heq.mono fun y hy => (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)

/-- Two continuous lifts of the same local-homeomorphism quotient agree near a point where they coincide. -/
theorem eventuallyEq_of_localHomeomorph_comp_eq {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsLocalHomeomorph q) {f g : Z → X}
    {z : Z} (hf : ContinuousAt f z) (hg : ContinuousAt g z) (hz : f z = g z)
    (he : ∀ᶠ w in 𝓝 z, q (f w) = q (g w)) : f =ᶠ[𝓝 z] g := by
  let e := hq.localInverseAt (f z)
  have hU : e.target ∈ 𝓝 (f z) := e.open_target.mem_nhds hq.self_mem_localInverseAt_target
  have hfU : ∀ᶠ w in 𝓝 z, f w ∈ e.target := hf hU
  have hgU : ∀ᶠ w in 𝓝 z, g w ∈ e.target := hg (hz ▸ hU)
  filter_upwards [hfU, hgU, he] with w hfw hgw hw
  exact hq.injOn_localInverseAt_target hfw hgw hw

/-! ### Charts on a quotient covering -/

/-- A chosen lift of a quotient point under the covering. -/
def CoveringQuotient.representative {M Q G : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (x : Q) : M :=
  (hq.surjective x).choose

/-- The chosen representative projects back to the quotient point. -/
theorem CoveringQuotient.project_representative {M Q G : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (x : Q) : q (representative hq x) = x :=
  (hq.surjective x).choose_spec

/-- A local inverse of the covering near the chosen point `x`. -/
def CoveringQuotient.localInverse {M Q G : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (x : M) :
    OpenPartialHomeomorph Q M :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt x

/-- The inverse of the local inverse is the quotient map. -/
@[simp]
theorem CoveringQuotient.localInverse_symm {M Q G : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (x : M) : (localInverse hq x).symm = q :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt_symm x

/-- The local inverse is a right inverse of the quotient map. -/
theorem CoveringQuotient.project_localInverse {M Q G : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (x : M) {y : Q} (hy : y ∈ (localInverse hq x).source) : q (localInverse hq x y) = y :=
  hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy

/-- A quotient map is smooth when every deck transformation is smooth. -/
theorem CoveringQuotient.contMDiffOn_lift {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (a : M) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (localInverse hq a ∘ q)
      (q ⁻¹' (localInverse hq a).source) := by
  intro x hx
  have hcont : ContinuousAt (localInverse hq a ∘ q) x :=
    ((localInverse hq a).continuousAt hx).comp hq.continuous.continuousAt
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (project_localInverse hq a hx)
  have hsource : ∀ᶠ y in 𝓝 x, q y ∈ (localInverse hq a).source :=
    hq.continuous.continuousAt ((localInverse hq a).open_source.mem_nhds hx)
  have heq : (localInverse hq a ∘ q) =ᶠ[𝓝 x] (fun y => g • y) := by
    apply
      eventuallyEq_of_localHomeomorph_comp_eq hq.isCoveringMap.isLocalHomeomorph hcont
        (hG g).continuous.continuousAt hg.symm
    exact hsource.mono fun y hy => (project_localInverse hq a hy).trans (hq.map_smul g).symm
  exact ((hG g).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt

/-- The quotient chart at `x` composed from a local inverse and a source chart. -/
def CoveringQuotient.chart {E M Q G : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (x : Q) : OpenPartialHomeomorph Q E :=
  (localInverse hq (representative hq x)).trans (chartAt E (representative hq x))

/-- The quotient inherits a charted-space structure from the covering. -/
@[instance_reducible]
def CoveringQuotient.chartedSpace {E M Q G : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) : ChartedSpace E Q
    where
  atlas := Set.range (chart (E := E) hq)
  chartAt := chart (E := E) hq
  mem_chart_source
    x := by
    change
      x ∈ (localInverse hq (representative hq x)).source ∧
        localInverse hq (representative hq x) x ∈ (chartAt E (representative hq x)).source
    constructor
    · have h :=
        hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x :=
          representative hq x)
      simpa only [localInverse, project_representative] using h
    · have h : localInverse hq (representative hq x) x = representative hq x := by
        simpa only [localInverse, project_representative] using
          hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self (x := representative hq x)
      rw [h]
      exact mem_chart_source E (representative hq x)
  chart_mem_atlas x := Set.mem_range_self x

/-- The inverse quotient chart is the source chart's inverse followed by the quotient map. -/
theorem CoveringQuotient.chart_symm {E M Q G : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (x : Q) :
    ((chart (E := E) hq x).symm : E → Q) = q ∘ (chartAt E (representative hq x)).symm := by
  funext z
  change
    (localInverse hq (representative hq x)).symm ((chartAt E (representative hq x)).symm z) = _
  rw [localInverse_symm]
  rfl

/-- Quotient chart transitions differ by a deck transformation. -/
theorem CoveringQuotient.transition_eq {E M Q G : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M]
    {q : M → Q} (hq : IsQuotientCoveringMap q G) (x y : Q) :
    (((chart (E := E) hq x).symm.trans (chart (E := E) hq y)) : E → E) =
      chartAt E (representative hq y) ∘
        (localInverse hq (representative hq y) ∘ q) ∘ (chartAt E (representative hq x)).symm := by
  funext z
  simp only [OpenPartialHomeomorph.trans_apply, chart_symm, Function.comp_apply]
  rfl

/-- Quotient chart transitions are smooth when deck transformations are smooth. -/
theorem CoveringQuotient.contDiffOn_transition {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (x y : Q) :
    ContDiffOn ℂ n ((chart (E := E) hq x).symm.trans (chart (E := E) hq y))
      ((chart (E := E) hq x).symm.trans (chart (E := E) hq y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E (representative hq x)).target := hz.1.1
  have hy : q ((chartAt E (representative hq x)).symm z) ∈ (chart (E := E) hq y).source := by
    simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Function.comp_apply,
      Set.mem_preimage] using hz.2
  have ha := (chartAt E (representative hq x)).map_target hza
  have hb :
    localInverse hq (representative hq y) (q ((chartAt E (representative hq x)).symm z)) ∈
      (chartAt E (representative hq y)).source :=
    hy.2
  have hmid :=
    (contMDiffOn_lift hq n hG (representative hq y)).contMDiffAt
      (((localInverse hq (representative hq y)).open_source.preimage hq.continuous).mem_nhds hy.1)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' :
    ContDiffAt ℂ n
      (chartAt E (representative hq y) ∘
        (localInverse hq (representative hq y) ∘ q) ∘ (chartAt E (representative hq x)).symm)
      z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E (representative hq x)).right_inv hza] using hc
  rw [transition_eq]
  exact hc'.contDiffWithinAt

/-- The quotient of a manifold by a smooth quotient covering is a manifold. -/
theorem CoveringQuotient.isManifold {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M]
    {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    IsManifold (modelWithCornersSelf ℂ E) n Q := by
  let := chartedSpace (E := E) hq
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa using contDiffOn_transition hq n hG x y

/-- The covering projection is smooth for the quotient chart structure. -/
theorem CoveringQuotient.contMDiff_project {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n q := by
  let := chartedSpace (E := E) hq
  let := isManifold hq n hG
  intro x
  have hy : q x ∈ (chart (E := E) hq (q x)).source := mem_chart_source E (q x)
  have hmid :=
    (contMDiffOn_lift hq n hG (representative hq (q x))).contMDiffAt
      (((localInverse hq (representative hq (q x))).open_source.preimage hq.continuous).mem_nhds
        hy.1)
  have hc :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (chartAt E (representative hq (q x))) (localInverse hq (representative hq (q x)) (q x)) := by
    simpa [extChartAt, OpenPartialHomeomorph.extend] using
      (contMDiffAt_extChartAt' (I := modelWithCornersSelf ℂ E) (n := n) hy.2)
  apply
    (contMDiffAt_iff_target_of_mem_source (I := modelWithCornersSelf ℂ E) (I' :=
        modelWithCornersSelf ℂ E) (mem_chart_source E (q x))).mpr
  refine ⟨hq.continuous.continuousAt, ?_⟩
  have hchart : chartAt E (q x) = chart (E := E) hq (q x) := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart, Function.comp_def] using
    hc.comp x hmid

/-- A map out of the quotient is smooth when its lift is. -/
theorem CoveringQuotient.contMDiff_of_comp {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) {F H N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] (I : ModelWithCorners ℂ F H) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M] {f : Q → N}
    (hf : ContMDiff (modelWithCornersSelf ℂ E) I n (f ∘ q)) :
    letI := chartedSpace (E := E) hq
    ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  let := chartedSpace (E := E) hq
  intro x
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (chart (E := E) hq x).source := mem_chart_source E x
  have hsrc :=
    (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp
      (hf.contMDiffAt (x := localInverse hq (representative hq x) x))
  have hchart : chartAt E x = chart (E := E) hq x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart, Function.comp_def] using hsrc

/-- A map out of the quotient is smooth on a set when its lift is. -/
theorem CoveringQuotient.contMDiffOn_of_comp {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) {F H N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] (I : ModelWithCorners ℂ F H) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M] {f : Q → N} {U : Set Q} (hU : IsOpen U)
    (hf : ContMDiffOn (modelWithCornersSelf ℂ E) I n (f ∘ q) (q ⁻¹' U)) :
    letI := chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) I n f U := by
  let := chartedSpace (E := E) hq
  intro x hxU
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (chart (E := E) hq x).source := mem_chart_source E x
  have hpre : localInverse hq (representative hq x) x ∈ q ⁻¹' U := by
    change q (localInverse hq (representative hq x) x) ∈ U
    rw [project_localInverse hq _ hx.1]
    exact hxU
  have hf' := hf.contMDiffAt ((hU.preimage hq.continuous).mem_nhds hpre)
  have hsrc :=
    (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp hf'
  have hchart : chartAt E x = chart (E := E) hq x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart, Function.comp_def] using hsrc

/-- Local inverses of the covering are holomorphic. -/
theorem CoveringQuotient.localInverse_holomorphic {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (a : M) :
    letI := chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (localInverse hq a)
      (localInverse hq a).source :=
  contMDiffOn_of_comp hq (modelWithCornersSelf ℂ E) n (localInverse hq a).open_source
    (contMDiffOn_lift hq n hG a)

/-- The covering projection is a local diffeomorphism. -/
theorem CoveringQuotient.project_isLocalDiffeomorph {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω q := by
  let := chartedSpace (E := E) hq
  intro x
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) M Q ω :=
    { toPartialEquiv := (localInverse hq x).symm.toPartialEquiv
      open_source := (localInverse hq x).open_target
      open_target := (localInverse hq x).open_source
      contMDiffOn_toFun := by
        change
          ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
            (localInverse hq x).symm (localInverse hq x).target
        rw [localInverse_symm]
        exact (contMDiff_project hq ω hG).contMDiffOn
      contMDiffOn_invFun := localInverse_holomorphic hq ω hG x }
  refine ⟨Φ, hq.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target, ?_⟩
  intro y _
  change q y = (localInverse hq x).symm y
  rw [localInverse_symm]

/-! ### Quotients by a discrete submodule -/

/-- Quotienting by a discrete submodule is a local homeomorphism. -/
theorem DiscreteQuotient.quotient_localHomeomorph {E : Type*} [NormedAddCommGroup E]
    (L : Submodule ℤ E) [DiscreteTopology L] : IsLocalHomeomorph (L.mkQ : E → E ⧸ L) := by
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  exact
    (AddSubgroup.isAddQuotientCoveringMap_of_comm L.toAddSubgroup
        DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph

/-- A chosen lift of a quotient point. -/
def DiscreteQuotient.representative {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    (x : E ⧸ L) : E :=
  (L.mkQ_surjective x).choose

/-- The chosen representative projects back to the quotient point. -/
@[simp]
theorem DiscreteQuotient.mkQ_representative {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    (x : E ⧸ L) : L.mkQ (representative L x) = x :=
  (L.mkQ_surjective x).choose_spec

/-- The quotient chart near `x` given by the local inverse of `mkQ`. -/
def DiscreteQuotient.chart {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x : E ⧸ L) : OpenPartialHomeomorph (E ⧸ L) E :=
  (quotient_localHomeomorph L).localInverseAt (representative L x)

/-- The quotient by a discrete submodule is a charted space. -/
instance DiscreteQuotient.chartedSpace {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] : ChartedSpace E (E ⧸ L)
    where
  atlas := Set.range (chart L)
  chartAt := chart L
  mem_chart_source
    x := by
    have h :=
      (quotient_localHomeomorph L).apply_self_mem_localInverseAt_source (x := representative L x)
    simpa only [chart, mkQ_representative] using h
  chart_mem_atlas x := Set.mem_range_self x

/-- The inverse quotient chart is `mkQ`. -/
@[simp]
theorem DiscreteQuotient.chart_symm {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x : E ⧸ L) : (chart L x).symm = (L.mkQ : E → E ⧸ L) :=
  (quotient_localHomeomorph L).localInverseAt_symm (representative L x)

/-- The quotient chart computes points back through `mkQ`. -/
theorem DiscreteQuotient.mkQ_chart {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x y : E ⧸ L) (hy : y ∈ (chart L x).source) : L.mkQ (chart L x y) = y :=
  (quotient_localHomeomorph L).apply_localInverseAt_of_mem hy

/-- Quotient chart transitions differ from the identity by a lattice element. -/
theorem DiscreteQuotient.transition_sub_mem {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x y : E ⧸ L) (z : E)
    (hz : z ∈ ((chart L x).symm.trans (chart L y)).source) :
    ((chart L x).symm.trans (chart L y)) z - z ∈ L := by
  apply (Submodule.Quotient.eq L).mp
  change L.mkQ (((chart L x).symm.trans (chart L y)) z) = L.mkQ z
  rw [OpenPartialHomeomorph.trans_apply, chart_symm]
  apply mkQ_chart
  simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Set.mem_preimage] using hz.2

/-- The quotient by a discrete submodule is a smooth manifold. -/
instance DiscreteQuotient.isManifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    IsManifold (modelWithCornersSelf ℂ E) n (E ⧸ L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have h :=
    contDiffOn_of_sub_mem_discrete L ((chart L x).symm.trans (chart L y)).continuousOn
      (transition_sub_mem L x y) n
  simpa using h

/-- The quotient map `mkQ` is smooth. -/
theorem DiscreteQuotient.contMDiff_mkQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (L.mkQ : E → E ⧸ L) := by
  apply contMDiff_iff.mpr
  refine ⟨L.continuous_mkQ, ?_⟩
  intro x y
  have h : ContDiffOn ℂ n (chart L y ∘ L.mkQ) (L.mkQ ⁻¹' (chart L y).source) := by
    apply contDiffOn_of_sub_mem_discrete L
    · exact (chart L y).continuousOn.comp L.continuous_mkQ.continuousOn (fun z hz => hz)
    · intro z hz
      exact (Submodule.Quotient.eq L).mp (mkQ_chart L y (L.mkQ z) hz)
  have hchart : chartAt E y = chart L y := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chartAt_self_eq] using h

/-- A map out of the quotient is smooth when its composition with `mkQ` is. -/
theorem DiscreteQuotient.contMDiff_of_comp_mkQ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (L : Submodule ℤ E) [DiscreteTopology L] {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) {f : E ⧸ L → M}
    (hf : ContMDiff (modelWithCornersSelf ℂ E) I n (f ∘ L.mkQ)) :
    ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt E x = chart L x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart_symm] using
    (hf.contMDiffAt.contMDiffWithinAt (s := Set.univ) (x := chart L x x))

/-- The quotient by a discrete submodule is an additive Lie group. -/
instance DiscreteQuotient.lieAddGroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    LieAddGroup (modelWithCornersSelf ℂ E) n (E ⧸ L)
    where
  contMDiff_add := by
    have h :
      ContMDiff (modelWithCornersSelf ℂ (E × E)) (modelWithCornersSelf ℂ E) n
        (fun z : E × E => L.mkQ (z.1 + z.2)) :=
      (contMDiff_mkQ L n).comp (contDiff_fst.add contDiff_snd).contMDiff
    intro x
    rw [contMDiffAt_iff_source]
    have hchart : ∀ y : E ⧸ L, chartAt E y = chart L y := fun _ => rfl
    have hs :
      ((extChartAt ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) x).symm :
          E × E → (E ⧸ L) × (E ⧸ L)) =
        fun z => (L.mkQ z.1, L.mkQ z.2) := by
      rw [extChartAt_prod, PartialEquiv.prod_coe_symm]
      simp only [extChartAt_coe_symm, hchart, chart_symm, modelWithCornersSelf_coe_symm,
        Function.comp_def, id_eq]
    have ht :
      extChartAt ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) x x =
        (chart L x.1 x.1, chart L x.2 x.2) :=
      rfl
    have hr : Set.range ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) = Set.univ :=
      Set.range_eq_univ.mpr fun z => ⟨z, rfl⟩
    rw [hs, ht, hr]
    simpa only [Function.comp_def, map_add] using
      (h.contMDiffAt.contMDiffWithinAt (s := Set.univ) (x := (chart L x.1 x.1, chart L x.2 x.2)))
  contMDiff_neg := by
    apply contMDiff_of_comp_mkQ L (modelWithCornersSelf ℂ E) n
    simpa [Function.comp_def, map_neg] using
      (contMDiff_mkQ L n).comp (contDiff_neg : ContDiff ℂ n (fun z : E => -z)).contMDiff

/-- A linear equivalence respecting the lattices descends to a biholomorphism of quotients. -/
def DiscreteQuotient.linearBiholomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : Submodule ℤ E) (K : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology K] (e : E ≃L[ℂ] F)
    (h : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap = K) :
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) (E ⧸ L) (F ⧸ K) ω
    where
  toEquiv := (Submodule.Quotient.equiv L K (e.toLinearEquiv.restrictScalars ℤ) h).toEquiv
  contMDiff_toFun := by
    apply contMDiff_of_comp_mkQ
    exact (contMDiff_mkQ K ω).comp e.contDiff.contMDiff
  contMDiff_invFun := by
    apply contMDiff_of_comp_mkQ
    exact (contMDiff_mkQ L ω).comp e.symm.contDiff.contMDiff

/-! ### Quotient charts over orthants -/

/-- A quotient-covering chart obtained by composing a local inverse of the covering with a source chart. -/
def CoveringOrthant.localChart {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    OpenPartialHomeomorph Q H :=
  (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).trans e

/-- The quotient of the chart centre lies in the local chart's source. -/
theorem CoveringOrthant.self_mem_localChart_source {G M Q H : Type*} [Group G]
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) (ha : a ∈ e.source) :
    q a ∈ (localChart hq e a).source := by
  change
    q a ∈ (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).source ∧
      hq.isCoveringMap.isLocalHomeomorph.localInverseAt a (q a) ∈ e.source
  exact
    ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source, by
      simpa only [IsLocalHomeomorph.localInverseAt_apply_self] using ha⟩

/-- The inverse quotient chart is `q` after the source chart's inverse. -/
theorem CoveringOrthant.localChart_symm {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    ((localChart hq e a).symm : H → Q) = q ∘ e.symm := by
  simp only [localChart, OpenPartialHomeomorph.coe_trans_symm,
    IsLocalHomeomorph.localInverseAt_symm]

/-- The inverse quotient chart applies the inverse source chart followed by the quotient map. -/
@[simp]
theorem CoveringOrthant.localChart_symm_apply {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) (z : H) :
    (localChart hq e a).symm z = q (e.symm z) := by rw [localChart_symm, Function.comp_apply]

/-- The local chart's target lies inside the source chart's target. -/
theorem CoveringOrthant.localChart_target_subset {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    (localChart hq e a).target ⊆ e.target := fun _ hz => hz.1

/-- A coordinate identity in the source chart descends to the quotient chart. -/
theorem CoveringOrthant.localChart_coordinate_identity {G M Q H : Type*} [Group G]
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) {R : Type*}
    (f : Q → R) (F : H → R) (he : ∀ x ∈ e.source, f (q x) = F (e x)) :
    ∀ z ∈ (localChart hq e a).target, f ((localChart hq e a).symm z) = F z := by
  intro z hz
  have hze := localChart_target_subset hq e a hz
  rw [localChart_symm_apply, he (e.symm z) (e.map_target hze), e.right_inv hze]

end Mathoverflow1973
