/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.AdaptedDescentField
public import Lib.Geometry.Manifold.Morse.Handle

/-!
# The model descent flow in a Morse chart

On `N × P` the model descent flow `MorseHandle.descentFlow t (u, v) = (eᵗ u, e⁻ᵗ v)` strictly
decreases the quadratic form `-‖u‖² + ‖v‖²` away from the origin and moves the model
sublevel-with-handle `{quadratic ≤ -ρ²} ∪ range (modelMap ρ)` into its interior. If a flow `F` on a
manifold integrates a `C¹` field that agrees, near the relevant points, with the descent field
`c.descentField` of a signed Morse chart `c`, then by uniqueness of integral curves `F` is the
chart image of the model flow for as long as the model orbit stays in the chart
(cf. Milnor, *Lectures on the h-cobordism theorem*, §3, the standard form of a gradient-like
field near a critical point).

## Main results

* `MorseHandle.quadratic_descentFlow_lt`,
  `MorseHandle.descentFlow_mem_interior_lower_union_handle` : the model statements.
* `FlowConstruction.partialChartField_eq_mfderiv_symm`,
  `FlowConstruction.hasMFDerivAt_lift_partialChartCurve` : an integral curve of a field `W` in a
  chart lifts to an integral curve of the pulled-back field.
* `ManifoldMorse.SignedMorseChart.eventually_flow_eq_descentModel`,
  `flow_eqOn_descentModel`, `flow_eq_descentModel_of_mem_uIcc` : the flow agrees with the model
  for small times, on a preconnected set of times containing `0`, and on an interval `uIcc 0 t`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3

## Tags

Morse theory, gradient-like vector field, local model
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-! ### The descent model -/

/-- The quadratic descent flow decreases the height. -/
theorem MorseHandle.quadratic_descentFlow_lt {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {t : ℝ} (ht : 0 < t) {z : N × P}
    (hz : z ≠ 0) : quadratic (descentFlow t z) < quadratic z := by
  have h₁ :=
    (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr
      (norm_fst_le_descentFlow ht.le z)
  have h₂ :=
    (sq_le_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr
      (norm_snd_descentFlow_le ht.le z)
  by_cases hu : z.1 = 0
  · have hv : z.2 ≠ 0 := fun hv => hz (Prod.ext hu hv)
    have hvnorm : ‖(descentFlow t z).2‖ < ‖z.2‖ := by
      rw [norm_descentFlow_snd]
      exact
        mul_lt_of_lt_one_left (norm_pos_iff.mpr hv) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    have hv₂ := (sq_lt_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr hvnorm
    exact add_lt_add_of_le_of_lt (neg_le_neg h₁) hv₂
  · have hunorm : ‖z.1‖ < ‖(descentFlow t z).1‖ := by
      rw [norm_descentFlow_fst]
      exact lt_mul_of_one_lt_left (norm_pos_iff.mpr hu) (Real.one_lt_exp_iff.mpr ht)
    have hu₂ := (sq_lt_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr hunorm
    exact add_lt_add_of_lt_of_le (neg_lt_neg hu₂) h₂

/-- The descent flow enters the lower union's interior. -/
theorem MorseHandle.descentFlow_mem_interior_lower_union_handle {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ t : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) {z : N × P}
    (hz : z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ)) :
    descentFlow t z ∈ interior ({w | quadratic w ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ)) := by
  have hc : Continuous (quadratic (N := N) (P := P)) :=
    (continuous_fst.norm.pow 2).neg.add (continuous_snd.norm.pow 2)
  rw [mem_lower_union_handle_iff hρ] at hz
  rcases hz with hq | hv
  · have hne : z ≠ 0 := by
      intro h
      have hq' : (0 : ℝ) ≤ -(ρ ^ 2) := by simpa [h, quadratic] using hq
      nlinarith [sq_pos_of_pos hρ]
    have hlt : quadratic (descentFlow t z) < -(ρ ^ 2) :=
      (quadratic_descentFlow_lt ht hne).trans_le hq
    apply mem_interior.mpr
    refine ⟨{w | quadratic w < -(ρ ^ 2)}, ?_, isOpen_lt hc continuous_const, hlt⟩
    intro w hw
    exact Or.inl (show quadratic w ≤ -(ρ ^ 2) from le_of_lt hw)
  · have hlt : ‖(descentFlow t z).2‖ < ρ := by
      rw [norm_descentFlow_snd]
      calc
        _ ≤ Real.exp (-t) * ρ := mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
        _ < ρ := mul_lt_of_lt_one_left hρ (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    apply mem_interior.mpr
    refine ⟨{w : N × P | ‖w.2‖ < ρ}, ?_, isOpen_lt continuous_snd.norm continuous_const, hlt⟩
    intro w hw
    exact (mem_lower_union_handle_iff hρ w).mpr (Or.inr hw.le)

/-- The partial chart field is the inverse derivative of the direction. -/
theorem FlowConstruction.partialChartField_eq_mfderiv_symm {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞)
    (W : F → F) {x : M} (hx : x ∈ e.source) :
    partialChartField e W x =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm (e x)
        ((NormedSpace.fromTangentSpace (e x)).symm (W (e x))) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
        ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x))) =
      _
  rw [hi]
  rfl

/-- A partial chart curve lifts to a manifold curve. -/
theorem FlowConstruction.hasMFDerivAt_lift_partialChartCurve {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞)
    (W : F → F) {α : ℝ → F} {t : ℝ} (hα : HasDerivAt α (W (α t)) t) (ht : α t ∈ e.target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (e.symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (partialChartField e W (e.symm (α t)))) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hi := (he.mdifferentiableAt_symm ht).hasMFDerivAt
  have hd := hi.comp t hα.hasFDerivAt.hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (α t))
        ((NormedSpace.fromTangentSpace t a) •
          (NormedSpace.fromTangentSpace (α t)).symm (W (α t))) =
      (NormedSpace.fromTangentSpace t a) • partialChartField e W (e'.symm (α t))
  rw [map_smul, partialChartField_eq_mfderiv_symm e W (e'.map_target ht)]
  rw [show e (e'.symm (α t)) = α t from e'.right_inv ht]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- The flow eventually agrees with the descent model. -/
theorem ManifoldMorse.SignedMorseChart.eventually_flow_eq_descentModel {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M}
    (hx : x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      F t x = c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  let α : ℝ → c.NegativeCoordinates × c.PositiveCoordinates := fun t =>
    MorseHandle.descentFlow t (c.splitChart x)
  let γ : ℝ → M := e.symm ∘ α
  have hα : Continuous α :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : α 0 = e x := MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), α t ∈ e.target :=
    hα.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hγ₀ : γ 0 = x := by
    change e.symm (α 0) = x
    rw [hα₀, e.left_inv hx]
  have hγc : ContinuousAt γ 0 :=
    (e.continuousAt_symm (hα₀ ▸ e.map_source hx)).comp hα.continuousAt
  have hγt : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by simpa only [ContinuousAt, hγ₀] using hγc
  have hγ : IsMIntegralCurveAt γ V 0 := by
    filter_upwards [htarget, hγt.eventually heq] with t ht heqt
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t)))
    rw [heqt]
    exact
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve c.splitChart
        MorseHandle.descent (MorseHandle.hasDerivAt_descentFlow (c.splitChart x) t) ht
  have h₀ : F 0 x = γ 0 := (F.map_zero_apply x).trans hγ₀.symm
  exact
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless (hV.contMDiffAt)
      ((hcurve x).isMIntegralCurveAt 0) hγ h₀

attribute [local instance 100] Classical.propDecidable in
/-- The flow equals the descent model on the block. -/
theorem ManifoldMorse.SignedMorseChart.flow_eqOn_descentModel {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M}
    (hx : x ∈ c.splitChart.source) {S : Set ℝ} (hS : IsPreconnected S) (hzero : 0 ∈ S)
    (htarget : ∀ t ∈ S, MorseHandle.descentFlow t (c.splitChart x) ∈ c.splitChart.target)
    (heq :
      ∀ t ∈ S,
        ∀ᶠ y in 𝓝 (c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x))),
          V y = c.descentField y) :
    Set.EqOn (fun t => F t x)
      (fun t => c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x))) S := by
  let α : ℝ → c.NegativeCoordinates × c.PositiveCoordinates := fun t =>
    MorseHandle.descentFlow t (c.splitChart x)
  let γ : ℝ → M := c.splitChart.symm ∘ α
  have hα : Continuous α :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hγ : ∀ t ∈ S, IsMIntegralCurveAt γ V t := by
    intro t ht
    have hlocal : ∀ᶠ s in 𝓝 t, α s ∈ c.splitChart.target :=
      hα.continuousAt.preimage_mem_nhds (c.splitChart.open_target.mem_nhds (htarget t ht))
    have hc : ContinuousAt c.splitChart.toOpenPartialHomeomorph.symm (α t) :=
      c.splitChart.toOpenPartialHomeomorph.continuousAt_symm (htarget t ht)
    have hγc : ContinuousAt γ t := hc.comp (f := α) hα.continuousAt
    filter_upwards [hlocal, hγc.eventually (heq t ht)] with s hs heqs
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s)))
    rw [heqs]
    exact
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve c.splitChart
        MorseHandle.descent (MorseHandle.hasDerivAt_descentFlow (c.splitChart x) s) hs
  have hγc : Continuous (fun t : S => γ t.val) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hγ t.val t.property).continuousAt).comp continuousAt_subtype_val
  let U : Set S := {t | F t.val x = γ t.val}
  have hclosed : IsClosed U :=
    isClosed_eq (F.continuous continuous_subtype_val continuous_const) hγc
  have hopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal :=
      isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hV.contMDiffAt
        ((hcurve x).isMIntegralCurveAt t.val) (hγ t.val t.property) ht
    exact continuousAt_subtype_val.eventually hlocal
  have hγzero : γ 0 = x := by
    change c.splitChart.symm (MorseHandle.descentFlow 0 (c.splitChart x)) = x
    rw [MorseHandle.descentFlow.map_zero_apply]
    exact c.splitChart.left_inv' hx
  have hnonempty : U.Nonempty := ⟨⟨0, hzero⟩, (F.map_zero_apply x).trans hγzero.symm⟩
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have huniv : U = Set.univ := (show IsClopen U from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro t ht
  have hmem : (⟨t, ht⟩ : S) ∈ U := huniv ▸ Set.mem_univ _
  exact hmem

attribute [local instance 100] Classical.propDecidable in
/-- The flow equals the descent model while in the interval. -/
theorem ManifoldMorse.SignedMorseChart.flow_eq_descentModel_of_mem_uIcc {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M}
    (hx : x ∈ c.splitChart.source) {t : ℝ}
    (htarget :
      ∀ s ∈ Set.uIcc 0 t, MorseHandle.descentFlow s (c.splitChart x) ∈ c.splitChart.target)
    (heq :
      ∀ s ∈ Set.uIcc 0 t,
        ∀ᶠ y in 𝓝 (c.splitChart.symm (MorseHandle.descentFlow s (c.splitChart x))),
          V y = c.descentField y) :
    F t x = c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)) :=
  c.flow_eqOn_descentModel hV F hcurve hx isPreconnected_uIcc Set.left_mem_uIcc htarget heq
    Set.right_mem_uIcc
