/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Handle

/-!
# Flows of smooth vector fields on compact manifolds

Flow boxes and partial chart fields (`FlowConstruction.*`), the Morse-block machinery
isolating critical points (`MorseCancellation.morseClosedBlock*`,
`exists_disjoint_morse_block_field`), and inverse-function ingredients
(`isLocalDiffeomorphAt_of_invertible_mvfderiv`).

## Main definitions and results

* `FlowConstruction.*` : flow boxes and partial chart fields.
* `isLocalDiffeomorphAt_of_invertible_mvfderiv` : inverse function theorem form.

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Theorem 9.12

## Tags

flow, compact manifold, inverse function theorem
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

/-! ### Local flows on a manifold -/

/-- A local flow exists on an open subset. -/
theorem FlowConstruction.exists_localFlow_in_open {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {v : E → E} {x₀ : E} (hv : ContDiffAt ℝ 1 v x₀)
    {U : Set E} (hU : IsOpen U) (hxU : x₀ ∈ U) :
    ∃ r > (0 : ℝ),
      ∃ ε > (0 : ℝ),
        ∃ α : E × ℝ → E,
          ContinuousOn α (Metric.ball x₀ r ×ˢ Set.Ioo (-ε) ε) ∧
            ∀ x ∈ Metric.ball x₀ r,
              α (x, 0) = x ∧
                ∀ t ∈ Set.Ioo (-ε) ε,
                  α (x, t) ∈ U ∧ HasDerivAt (fun s => α (x, s)) (v (α (x, t))) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  obtain ⟨α, hα, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hα hc
  have hr' : (0 : ℝ) < r := hr
  have hc₀ : ContinuousAt α (x₀, 0) :=
    hc.continuousAt
      (prod_mem_nhds (Metric.closedBall_mem_nhds x₀ hr') (Icc_mem_nhds (neg_lt_zero.mpr hε) hε))
  have hα₀ : α (x₀, 0) = x₀ := (hα x₀ (Metric.mem_closedBall_self hr'.le)).1
  have hpre : α ⁻¹' U ∈ 𝓝 (x₀, 0) := hc₀.preimage_mem_nhds (hU.mem_nhds (hα₀.symm ▸ hxU))
  have hD : Metric.ball x₀ (r : ℝ) ×ˢ Set.Ioo (-ε) ε ∈ 𝓝 (x₀, 0) :=
    prod_mem_nhds (Metric.ball_mem_nhds x₀ hr') (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hD hpre)
  have hs :
    Metric.ball x₀ δ ×ˢ Set.Ioo (-δ) δ ⊆ (Metric.ball x₀ (r : ℝ) ×ˢ Set.Ioo (-ε) ε) ∩ α ⁻¹' U := by
    intro q hq
    apply hδsub
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hq.1, by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hq.2⟩
  refine ⟨δ, hδ, δ, hδ, α, hc.mono ?_, ?_⟩
  · intro q hq
    exact ⟨Metric.ball_subset_closedBall (hs hq).1.1, Set.Ioo_subset_Icc_self (hs hq).1.2⟩
  · intro x hx
    have hx₀ : (x, (0 : ℝ)) ∈ Metric.ball x₀ δ ×ˢ Set.Ioo (-δ) δ := ⟨hx, neg_lt_zero.mpr hδ, hδ⟩
    have hx' : x ∈ Metric.closedBall x₀ (r : ℝ) := Metric.ball_subset_closedBall (hs hx₀).1.1
    refine ⟨(hα x hx').1, ?_⟩
    intro t ht
    have hq : (x, t) ∈ Metric.ball x₀ δ ×ˢ Set.Ioo (-δ) δ := ⟨hx, ht⟩
    refine ⟨(hs hq).2, ?_⟩
    have ht' := (hs hq).1.2
    exact ((hα x hx').2 t (Set.Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

/-- The coordinate vector field in a chart. -/
def FlowConstruction.coordinateField {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) (y : E) : E :=
  tangentCoordChange 𝓘(ℝ, E) ((chartAt E p).symm y) p ((chartAt E p).symm y)
    (v ((chartAt E p).symm y))

/-- The coordinate field is smooth. -/
theorem FlowConstruction.contDiffAt_coordinateField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (hv :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) p) :
    ContDiffAt ℝ 1 (coordinateField v p) (chartAt E p p) := by
  rw [contMDiffAt_iff] at hv
  have h :=
    hv.2.contDiffAt
      (range_mem_nhds_isInteriorPoint (I := 𝓘(ℝ, E))
        (BoundarylessManifold.isInteriorPoint (x := p)))
  convert h.snd using 1 <;> rfl

/-- The coordinate field is the chart derivative of the direction. -/
theorem FlowConstruction.coordinateField_eq_mfderiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    coordinateField v p y =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) ((chartAt E p).symm y) (v ((chartAt E p).symm y)) := by
  rw [mfderiv_chartAt_eq_tangentCoordChange ((chartAt E p).map_target hy)]
  rfl

/-- The chart inverse differentiates the coordinate field to the direction. -/
theorem FlowConstruction.mfderiv_symm_coordinateField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
        ((NormedSpace.fromTangentSpace y).symm (coordinateField v p y)) =
      v ((chartAt E p).symm y) := by
  let e := chartAt E p
  have he := (mdifferentiable_chart (I := 𝓘(ℝ, E)) p).symm_comp_deriv (e.map_target hy)
  rw [e.right_inv hy] at he
  rw [coordinateField_eq_mfderiv v p hy]
  exact congrArg (fun A : E →L[ℝ] E => A (v (e.symm y))) he

/-- A coordinate curve lifts to a manifold curve. -/
theorem FlowConstruction.hasMFDerivAt_lift_coordinateCurve {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M} {α : ℝ → E} {t : ℝ}
    (hα : HasDerivAt α (coordinateField v p (α t)) t) (ht : α t ∈ (chartAt E p).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((chartAt E p).symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((chartAt E p).symm (α t)))) := by
  have hi := ((mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mdifferentiableAt_symm ht).hasMFDerivAt
  have h := hi.comp t hα.hasFDerivAt.hasMFDerivAt
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm (α t))
        ((NormedSpace.fromTangentSpace t a) •
          (NormedSpace.fromTangentSpace (α t)).symm (coordinateField v p (α t))) =
      (NormedSpace.fromTangentSpace t a) • v ((chartAt E p).symm (α t))
  rw [map_smul, mfderiv_symm_coordinateField v p ht]

/-- A local flow of a vector field exists on the manifold. -/
theorem FlowConstruction.exists_manifoldLocalFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} (p : M)
    (hv :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) p) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧
          ∃ ε > (0 : ℝ),
            ∃ F : M × ℝ → M,
              ContinuousOn F (U ×ˢ Set.Ioo (-ε) ε) ∧
                ∀ x ∈ U,
                  F (x, 0) = x ∧ IsMIntegralCurveOn (fun t => F (x, t)) v (Set.Ioo (-ε) ε) := by
  let e := chartAt E p
  obtain ⟨r, hr, ε, hε, α, hαc, hα⟩ :=
    exists_localFlow_in_open (contDiffAt_coordinateField hv) e.open_target
      (e.map_source (mem_chart_source E p))
  let U : Set M := e.source ∩ e ⁻¹' Metric.ball (e p) r
  have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hpU : p ∈ U := ⟨mem_chart_source E p, Metric.mem_ball_self hr⟩
  let F : M × ℝ → M := fun q => e.symm (α (e q.1, q.2))
  have hc : ContinuousOn (fun q : M × ℝ => (e q.1, q.2)) (U ×ˢ Set.Ioo (-ε) ε) :=
    (e.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq.1.1)).prodMk
      continuous_snd.continuousOn
  have hd :
    Set.MapsTo (fun q : M × ℝ => (e q.1, q.2)) (U ×ˢ Set.Ioo (-ε) ε)
      (Metric.ball (e p) r ×ˢ Set.Ioo (-ε) ε) :=
    fun _ hq => ⟨hq.1.2, hq.2⟩
  have hFc : ContinuousOn F (U ×ˢ Set.Ioo (-ε) ε) :=
    e.symm.continuousOn.comp (hαc.comp hc hd) (fun q hq => ((hα (e q.1) hq.1.2).2 q.2 hq.2).1)
  refine ⟨U, hU, hpU, ε, hε, F, hFc, ?_⟩
  intro x hx
  refine ⟨?_, ?_⟩
  · change e.symm (α (e x, 0)) = x
    rw [(hα (e x) hx.2).1, e.left_inv hx.1]
  · intro t ht
    have hcurve := (hα (e x) hx.2).2 t ht
    exact (hasMFDerivAt_lift_coordinateCurve hcurve.2 hcurve.1).hasMFDerivWithinAt

/-- Uniform-time integral curves exist on a compact set. -/
theorem FlowConstruction.exists_uniformIntegralCurves {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∃ ε > (0 : ℝ), ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  classical
  choose U hU hp ε hε F hFc hF using fun p : M => exists_manifoldLocalFlow p (hv p)
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover U hU (fun x _ => Set.mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Set.Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (Filter.biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro x
  obtain ⟨p, hps, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  refine ⟨fun t => F p (x, t), (hF p x hx).1, (hF p x hx).2.mono ?_⟩
  intro t ht
  apply Set.mem_iInter₂.mp (hδsub ?_) p hps
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht

/-- A global integral curve exists on a compact manifold. -/
theorem FlowConstruction.exists_globalIntegralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, h⟩ := exists_uniformIntegralCurves hv
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε h x

/-! ### The global flow on a compact manifold -/

/-- The flow of a vector field on a compact manifold. -/
def FlowConstruction.flow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (t : ℝ) (x : M) : M :=
  (exists_globalIntegralCurve hv x).choose t

/-- The flow at time zero is the identity. -/
@[simp]
theorem FlowConstruction.flow_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : flow hv 0 x = x :=
  (exists_globalIntegralCurve hv x).choose_spec.1

/-- The flow in time is an integral curve. -/
theorem FlowConstruction.isMIntegralCurve_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : IsMIntegralCurve (fun t => flow hv t x) v :=
  (exists_globalIntegralCurve hv x).choose_spec.2

/-- The flow satisfies the group law. -/
theorem FlowConstruction.flow_add {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (s t : ℝ) (x : M) : flow hv (s + t) x = flow hv s (flow hv t x) := by
  have h₁ := (isMIntegralCurve_flow hv x).comp_add t
  have h₂ := isMIntegralCurve_flow hv (flow hv t x)
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv h₁ h₂ (t₀ := 0)
      (by simp only [Function.comp_apply, zero_add, flow_zero])
  exact congrFun heq s

/-- The global flow agrees with the local flow. -/
theorem FlowConstruction.flow_eq_local {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {U : Set M} {ε : ℝ} (hε : 0 < ε) {F : M × ℝ → M}
    (hF : ∀ x ∈ U, F (x, 0) = x ∧ IsMIntegralCurveOn (fun t => F (x, t)) v (Set.Ioo (-ε) ε))
    {x : M} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) : flow hv t x = F (x, t) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0) ⟨neg_lt_zero.mpr hε, hε⟩ hv
    ((isMIntegralCurve_flow hv x).isMIntegralCurveOn _) (hF x hx).2
    ((flow_zero hv x).trans (hF x hx).1.symm) ht

/-- The flow is continuous on a compact-time cylinder. -/
theorem FlowConstruction.exists_continuousOn_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (p : M) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧ ∃ ε > (0 : ℝ), ContinuousOn (Function.uncurry (flow hv)) (Set.Ioo (-ε) ε ×ˢ U) := by
  obtain ⟨U, hU, hp, ε, hε, F, hFc, hF⟩ := exists_manifoldLocalFlow p (hv p)
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  have hc : ContinuousOn (fun q : ℝ × M => F (q.2, q.1)) (Set.Ioo (-ε) ε ×ˢ U) :=
    hFc.comp continuous_swap.continuousOn (fun _ hq => ⟨hq.2, hq.1⟩)
  exact hc.congr (fun q hq => flow_eq_local hv hε hF hq.2 hq.1)

/-- The flow is continuous for small time. -/
theorem FlowConstruction.exists_smalltime_continuous {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioo (-ε) ε, Continuous (flow hv t) := by
  classical
  choose U hU hp ε hε hF using exists_continuousOn_flow hv
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover U hU (fun x _ => Set.mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Set.Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (Filter.biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have htall : t ∈ ⋂ p ∈ s, Set.Ioo (-(ε p)) (ε p) :=
    hδsub (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨p, hps, hxp⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  have htp := Set.mem_iInter₂.mp htall p hps
  exact
    ((hF p).continuousAt (prod_mem_nhds (Ioo_mem_nhds htp.1 htp.2) ((hU p).mem_nhds hxp))).comp
      (continuousAt_const.prodMk continuousAt_id)

/-- The flow is continuous in time. -/
theorem FlowConstruction.continuous_flow_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (t : ℝ) : Continuous (flow hv t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_smalltime_continuous hv
  let S : Set ℝ := {s | Continuous (flow hv s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : Dist.dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Set.Ioo (-ε) ε := by
      exact abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => flow hv (u - s) (flow hv s x)) = flow hv u := by
      funext x
      rw [← flow_add, sub_add_cancel]
    change Continuous (flow hv u)
    rw [← heq]
    exact hc
  have hS : IsOpen S :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε)
        (fun u hu h =>
          hs
            (hstep h
              (by
                change Dist.dist u s < ε at hu
                rwa [dist_comm])))
  have hzero : (0 : ℝ) ∈ S := by
    change Continuous (flow hv 0)
    have heq : flow hv 0 = id := funext (flow_zero hv)
    rw [heq]
    exact continuous_id
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, hzero⟩
  change t ∈ S
  rw [hSuniv]
  exact Set.mem_univ t

/-- The flow is jointly continuous. -/
theorem FlowConstruction.continuous_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Continuous (Function.uncurry (flow hv)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨U, hU, hp, ε, hε, hF⟩ := exists_continuousOn_flow hv (flow hv q.1 q.2)
  have hzero :=
    hF.continuousAt (prod_mem_nhds (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε) (hU.mem_nhds hp))
  have hmap : ContinuousAt (fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) q :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      ((continuous_flow_time hv q.1).continuousAt.comp continuousAt_snd)
  have hzero' :
    ContinuousAt (Function.uncurry (flow hv))
      ((fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) q) := by simpa only [sub_self] using hzero
  have hcomp := hzero'.comp (f := fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) hmap
  have heq :
    (fun r : ℝ × M => flow hv (r.1 - q.1) (flow hv q.1 r.2)) = Function.uncurry (flow hv) := by
    funext r
    rw [← flow_add, sub_add_cancel]
    rfl
  exact heq ▸ hcomp

/-! ### The compact flow -/

/-- The compact flow of a field on a compact manifold. -/
def FlowConstruction.compactFlow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Flow ℝ M where
  toFun := flow hv
  cont' := continuous_flow hv
  map_add' := flow_add hv
  map_zero' := flow_zero hv

/-- The compact flow gives integral curves. -/
theorem FlowConstruction.isMIntegralCurve_compactFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : IsMIntegralCurve (fun t => compactFlow hv t x) v :=
  isMIntegralCurve_flow hv x

/-! ### Disjoint Morse block fields -/

attribute [local instance 100] Classical.propDecidable in
/-- A descent field exists on disjoint Morse blocks. -/
theorem MorseCancellation.exists_disjoint_morse_block_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ ManifoldMorse.criticalPoints E f)
    (c : ∀ i, ManifoldMorse.SignedMorseChart (E := E) f (p i)) (R : ι → ℝ)
    (hblock :
      ∀ i,
        Metric.closedBall (0 : (c i).NegativeCoordinates) (R i) ×ˢ
            Metric.closedBall (0 : (c i).PositiveCoordinates) (R i) ⊆
          (c i).splitChart.target)
    (hintervals :
      Pairwise
        (fun i j =>
          Disjoint (Set.Icc (f (p i) - R i ^ 2) (f (p i) + R i ^ 2))
            (Set.Icc (f (p j) - R j ^ 2) (f (p j) + R j ^ 2)))) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              ∀ i (z : (c i).NegativeCoordinates × (c i).PositiveCoordinates),
                ‖z.1‖ < R i →
                  ‖z.2‖ < R i → ∀ᶠ y in 𝓝 ((c i).splitChart.symm z), V y = (c i).descentField y :=
  by
  let K := fun i => morseClosedBlock (c i) (R i)
  have hK (i : ι) : IsClosed (K i) := (isCompact_morseClosedBlock (c i) (R i) (hblock i)).isClosed
  have hKsource (i : ι) : K i ⊆ (c i).splitChart.source :=
    morseClosedBlock_subset_source (c i) (R i) (hblock i)
  have hdisj : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact
      Set.disjoint_left.mp (hintervals hij) (morseClosedBlock_height (c i) (R i) (hblock i) hxi)
        (morseClosedBlock_height (c j) (R j) (hblock j) hxj)
  obtain ⟨V, hV, hzero, hdesc, hmatch⟩ :=
    exists_prescribed_morse_patch_field hf hm p hp c K hK hKsource hdisj
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let F := FlowConstruction.compactFlow hV₁
  refine ⟨V, F, hV, FlowConstruction.isMIntegralCurve_compactFlow hV₁, hzero, hdesc, ?_⟩
  intro i z hn hp
  filter_upwards [morseClosedBlock_mem_nhds (c i) (R i) (hblock i) hn hp] with y hy
  exact hmatch i y hy

/-- A larger closed ball inside an open set exists. -/
theorem MorseCancellation.exists_larger_closedBall_inside_open {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [ProperSpace A] {U : Set A} (hU : IsOpen U) {R B : ℝ} (hR : 0 ≤ R)
    (hRB : R < B) (hsub : Metric.closedBall (0 : A) R ⊆ U) :
    ∃ S, R < S ∧ S < B ∧ Metric.closedBall (0 : A) S ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (ProperSpace.isCompact_closedBall (0 : A) R).exists_cthickening_subset_open hU hsub
  rw [cthickening_closedBall hδ.le hR] at hδU
  obtain ⟨S, hRS, hSm⟩ := exists_between (lt_min (by linarith : R < δ + R) hRB)
  exact
    ⟨S, hRS, hSm.trans_le (min_le_right _ _),
      (Metric.closedBall_subset_closedBall (hSm.le.trans (min_le_left _ _))).trans hδU⟩

attribute [local instance 100] Classical.propDecidable in
/-- A Morse block enlargement inside the chart exists. -/
theorem MorseCancellation.exists_morse_block_enlargement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target) :
    ∃ R,
      2 * r < R ∧
        R < 3 * r ∧
          Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
            c.splitChart.target := by
  have hb :
    Metric.closedBall (0 : c.NegativeCoordinates × c.PositiveCoordinates) (2 * r) ⊆
      c.splitChart.target := by simpa only [closedBall_prod_same, Prod.mk_zero_zero] using hblock
  obtain ⟨R, hR, hR', hsub⟩ :=
    exists_larger_closedBall_inside_open c.splitChart.open_target (by positivity : 0 ≤ 2 * r)
      (by linarith : 2 * r < 3 * r) hb
  refine ⟨R, hR, hR', ?_⟩
  simpa only [closedBall_prod_same, Prod.mk_zero_zero] using hsub

attribute [local instance 100] Classical.propDecidable in
/-- A descent field exists on disjoint surgery blocks. -/
theorem MorseCancellation.exists_disjoint_surgery_block_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ ManifoldMorse.criticalPoints E f)
    (c : ∀ i, ManifoldMorse.SignedMorseChart (E := E) f (p i)) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hblock :
      ∀ i,
        Metric.closedBall (0 : (c i).NegativeCoordinates) (2 * r i) ×ˢ
            Metric.closedBall (0 : (c i).PositiveCoordinates) (2 * r i) ⊆
          (c i).splitChart.target)
    (hintervals :
      Pairwise
        (fun i j =>
          Disjoint (Set.Icc (f (p i) - 9 * r i ^ 2) (f (p i) + 9 * r i ^ 2))
            (Set.Icc (f (p j) - 9 * r j ^ 2) (f (p j) + 9 * r j ^ 2)))) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              ∀ i z,
                z ∈
                    Metric.closedBall (0 : (c i).NegativeCoordinates) (2 * r i) ×ˢ
                      Metric.closedBall (0 : (c i).PositiveCoordinates) (2 * r i) →
                  ∀ᶠ y in 𝓝 ((c i).splitChart.symm z), V y = (c i).descentField y := by
  choose R hR hR' hlarge using fun i => exists_morse_block_enlargement (c i) (hr i) (hblock i)
  have hRpos (i : ι) : 0 < R i := (mul_pos (show (0 : ℝ) < 2 by norm_num) (hr i)).trans (hR i)
  have hsq (i : ι) : R i ^ 2 < 9 * r i ^ 2 := by
    have hh :=
      mul_pos (sub_pos.mpr (hR' i))
        (add_pos (mul_pos (show (0 : ℝ) < 3 by norm_num) (hr i)) (hRpos i))
    nlinarith
  have hsub (i : ι) :
    Set.Icc (f (p i) - R i ^ 2) (f (p i) + R i ^ 2) ⊆
      Set.Icc (f (p i) - 9 * r i ^ 2) (f (p i) + 9 * r i ^ 2) := by
    intro v hv
    constructor <;> linarith [hv.1, hv.2, hsq i]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmatch⟩ :=
    exists_disjoint_morse_block_field hf hm p hp c R hlarge
      (fun i j hij => (hintervals hij).mono (hsub i) (hsub j))
  refine ⟨V, F, hV, hF, hzero, hdesc, ?_⟩
  intro i z hz
  exact
    hmatch i z ((mem_closedBall_zero_iff.mp hz.1).trans_lt (hR i))
      ((mem_closedBall_zero_iff.mp hz.2).trans_lt (hR i))

/-! ### Local diffeomorphisms from invertible derivatives -/

/-- A `C^n` map with invertible derivative is a partial diffeomorphism. -/
theorem exists_partialDiffeomorph_of_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {U : Set E} {x : E} (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hinv : (fderiv ℝ f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ (Φ : E → F) = f := by
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨A, hA⟩ := hinv
  have hfd : HasFDerivAt f (A : E →L[ℝ] F) x := by
    rw [hA]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  let g := hfx.toOpenPartialHomeomorph f hfd (by simp)
  let W := U ∩ interior {y | (fderiv ℝ f y).IsInvertible}
  have hW : IsOpen W := hU.inter isOpen_interior
  have hxW : x ∈ W := by
    refine ⟨hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    have ho : IsOpen {L : E →L[ℝ] F | L.IsInvertible} := ContinuousLinearEquiv.isOpen
    exact (hfx.continuousAt_fderiv (by simp)) (ho.mem_nhds ⟨A, hA⟩)
  let r := g.restrOpen W hW
  have hsource : r.source ⊆ U := fun _ h ↦ h.2.1
  have hto : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ r r.source := (hf.mono hsource).contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r.symm r.target := by
    intro y hy
    have hys := r.map_target hy
    have hiy : (fderiv ℝ f (r.symm y)).IsInvertible :=
      interior_subset (s := {z : E | (fderiv ℝ f z).IsInvertible}) hys.2.2
    obtain ⟨Ay, hAy⟩ := hiy
    have hfy : ContDiffAt ℝ ∞ f (r.symm y) := hf.contDiffAt (hU.mem_nhds hys.2.1)
    have hfdy : HasFDerivAt r (Ay : E →L[ℝ] F) (r.symm y) := by
      change HasFDerivAt f (Ay : E →L[ℝ] F) (r.symm y)
      rw [hAy]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    exact (r.contDiffAt_symm hy hfdy hfy).contMDiffAt.contMDiffWithinAt
  refine
    ⟨{ r.toPartialEquiv with
        open_source := r.open_source
        open_target := r.open_target
        contMDiffOn_toFun := hto
        contMDiffOn_invFun := hsymm },
      ?_, hsource, rfl⟩
  exact ⟨hfx.mem_toOpenPartialHomeomorph_source hfd (by simp), hxW⟩

/-- The tangent-space model equivalence at a point. -/
def tangentModelEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (x : M) : TangentSpace I x ≃L[ℝ] E where
  toFun v := v
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- The model chart as a partial diffeomorphism. -/
noncomputable def modelChartPartialDiffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞
    where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

/-- A map with invertible derivative is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_of_invertible_mvfderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {f : M → F} {x : M} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hinv : (mvfderiv I f x).IsInvertible) : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ f x := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let fc : E → F := f ∘ c.symm
  have hfc : ContDiffOn ℝ ∞ fc c.target := (hf.comp_contMDiffOn c.contMDiffOn_invFun).contDiffOn
  have hc : x ∈ c.source := mem_extChartAt_source x
  have hderiv : mvfderiv I f x = fderiv ℝ fc (c x) := by
    simpa [fc, c, modelChartPartialDiffeomorph, writtenInExtChartAt, extChartAt_self_eq,
      chartAt_self_eq, ModelWithCorners.range_eq_univ] using
      (hf.mdifferentiable (by simp) x).mvfderiv
  have hfcinv : (fderiv ℝ fc (c x)).IsInvertible := by
    obtain ⟨A, hA⟩ := hinv
    refine ⟨(tangentModelEquiv (I := I) x).symm.trans A, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : TangentSpace I x →L[ℝ] F ↦ L v) (hA.trans hderiv)
  obtain ⟨d, hd, _, hdf⟩ :=
    exists_partialDiffeomorph_of_contDiffOn c.open_target (c.map_source' hc) hfc hfcinv
  refine ⟨c.trans d, ⟨hc, hd⟩, ?_⟩
  intro y hy
  change f y = d (c y)
  rw [hdf]
  change f y = f (c.symm (c y))
  exact (congrArg f (c.left_inv' hy.1)).symm
end Mathoverflow1973
