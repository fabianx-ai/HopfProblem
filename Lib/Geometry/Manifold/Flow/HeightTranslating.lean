/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment

/-!
# Height-translating flows

Time-changing a gradient-like field by a positive factor so its flow transports between
regular levels: `exists_heightTranslatingFlow`,
`exists_regularSublevelHomeomorph_with_level` (Milnor h-cobordism §4's "hitting a level
exactly").

## Main definitions and results

* `FlowConstruction.exists_heightTranslatingFlow` : the time-changed flow.
* `FlowConstruction.exists_regularSublevelHomeomorph_with_level` : level transport.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §4

## Tags

time change, gradient-like flow, level transport
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

/-! ### Handle ball coordinates -/

/-- The unit ball homeomorphism of a handle chart. -/
def MorseHandle.unitBallHomeomorph (N : Type*) [NormedAddCommGroup N] :
    PuncturedHandle.UnitBall N ≃ₜ UnitDisk N
    where
  toFun z := ⟨z, mem_closedBall_zero_iff.mpr z.property⟩
  invFun z := ⟨z, mem_closedBall_zero_iff.mp z.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

attribute [local instance 100] Classical.propDecidable in
/-- The ball coordinates of a signed Morse chart's handle. -/
def ManifoldMorse.SignedMorseChart.handleBallCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    (PuncturedHandle.UnitBall c.NegativeCoordinates ×
        PuncturedHandle.UnitBall c.PositiveCoordinates) ≃ₜ
      (MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates) :=
  (MorseHandle.unitBallHomeomorph c.NegativeCoordinates).prodCongr
    (MorseHandle.unitBallHomeomorph c.PositiveCoordinates)

attribute [local instance 100] Classical.propDecidable in
/-- The handle map of a signed chart in norm coordinates. -/
def ManifoldMorse.SignedMorseChart.normHandleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(PuncturedHandle.UnitBall c.NegativeCoordinates ×
        PuncturedHandle.UnitBall c.PositiveCoordinates,
      M) :=
  ⟨fun z => c.attachingHandleMap ρ hρ hblock (c.handleBallCoordinates z),
    (c.attachingHandleMap ρ hρ hblock).continuous.comp c.handleBallCoordinates.continuous⟩

attribute [local instance 100] Classical.propDecidable in
/-- The norm handle map's range. -/
theorem ManifoldMorse.SignedMorseChart.range_normHandleMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Set.range (c.normHandleMap ρ hρ hblock) = Set.range (c.attachingHandleMap ρ hρ hblock) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨c.handleBallCoordinates z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨c.handleBallCoordinates.symm z, ?_⟩
    change
      c.attachingHandleMap ρ hρ hblock
          (c.handleBallCoordinates (c.handleBallCoordinates.symm z)) =
        _
    rw [c.handleBallCoordinates.apply_symm_apply]

/-! ### Attaching maps -/

attribute [local instance 100] Classical.propDecidable in
/-- The boundary data of the handle attachment. -/
def ManifoldMorse.SignedMorseChart.attachmentBoundaryData {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) :
    AttachmentBoundaryData c.NegativeCoordinates c.PositiveCoordinates M f (f p - ρ ^ 2)
    where
  handle := c.normHandleMap ρ hρ hblock
  handle_closed :=
    (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).comp
      c.handleBallCoordinates.isClosedEmbedding
  height_continuous := hf
  lower_frontier := hlevel
  lower_face := fun z => by
    constructor
    · intro hz
      exact (c.attachingHandleMap_lower_iff ρ hρ hblock (c.handleBallCoordinates z)).mp hz.le
    · intro hz
      exact c.attachingHandleMap_boundary_height ρ hρ hblock (c.handleBallCoordinates z) hz
  upper_face := fun z => by
    rw [c.range_normHandleMap ρ hρ hblock]
    exact c.attachingHandleMap_mem_frontier_iff hf ρ hρ hblock (c.handleBallCoordinates z)

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map of the signed chart. -/
def ManifoldMorse.SignedMorseChart.attachingCoreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(PuncturedHandle.UnitSphere c.NegativeCoordinates, { y : M // f y = f p - ρ ^ 2 }) :=
  (c.attachingBoundaryMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map computes the attaching point. -/
theorem ManifoldMorse.SignedMorseChart.attachingCoreMap_coe {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    (c.attachingCoreMap ρ hρ hblock u : M) =
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) := by
  change
    c.splitChart.symm
        ((ρ * Real.sqrt (1 + ‖(0 : c.PositiveCoordinates)‖ ^ 2)) • (u : c.NegativeCoordinates),
          ρ • (0 : c.PositiveCoordinates)) =
      _
  simp

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map is smooth into the ambient manifold. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_attachingCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) := by
  have heq :
    Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) :=
    funext (c.attachingCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (Subtype.val :
        PuncturedHandle.UnitSphere c.NegativeCoordinates → c.NegativeCoordinates) :=
    contMDiff_coe_sphere (E := c.NegativeCoordinates) (n := n)
  have hscalar :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : PuncturedHandle.UnitSphere c.NegativeCoordinates => ρ) :=
    contMDiff_const
  have hnegative :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        ρ • (u : c.NegativeCoordinates)) :=
    hscalar.smul hcoe
  have hcoords :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        (ρ • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) :=
    hnegative.prodMk_space contMDiff_const
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro u
  have hh :=
    hblock
      (MorseHandle.modelMap_mem_product hρ
        (⟨(u : c.NegativeCoordinates), Metric.sphere_subset_closedBall u.property⟩,
          (⟨0, by simp⟩ : MorseHandle.UnitDisk c.PositiveCoordinates)))
  simpa [MorseHandle.modelMap] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map is smooth. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (c.attachingCoreMap ρ hρ hblock) := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact
    (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n)
          (c.attachingCoreMap ρ hρ hblock)).mpr
      (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock)

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

/-! ### Forward invariance and entry -/

/-- A locally forward-invariant set is forward invariant. -/
theorem FlowConstruction.forwardInvariant_of_local {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Icc 0 ε, F t x ∈ A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A := by
  intro x hx T hT
  let S : Set ℝ := {t | F t x ∈ A}
  have hS : IsClosed S := hA.preimage (F.continuous continuous_id continuous_const)
  have hzero : (0 : ℝ) ∈ S := by simpa only [S, Set.mem_ofPred_eq, F.map_zero_apply] using hx
  apply (hS.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hzero hT
  intro s hs
  obtain ⟨ε, hε, hstay⟩ := hlocal (F s x) hs.1
  let δ := Min.min ε (T - s) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hs.2.2))
  have hδε : δ ≤ ε :=
    (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans (min_le_left _ _)
  have hδT : δ ≤ T - s :=
    (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans (min_le_right _ _)
  refine ⟨s + δ, ?_, by linarith, by linarith⟩
  change F (s + δ) x ∈ A
  rw [add_comm s δ, F.map_add]
  exact hstay δ ⟨hδ.le, hδε⟩

/-- The interior of a forward-invariant set is forward invariant. -/
theorem FlowConstruction.forwardInvariant_interior {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A) {x : X}
    (hx : x ∈ interior A) {t : ℝ} (ht : 0 ≤ t) : F t x ∈ interior A := by
  apply mem_interior.mpr
  refine ⟨F t '' interior A, ?_, (F.toHomeomorph t).isOpenMap _ isOpen_interior, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hforward y (interior_subset hy) t ht
  · exact ⟨x, hx, rfl⟩

/-- The flow enters the interior of a locally absorbing set. -/
theorem FlowConstruction.interior_entry_of_local {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioc 0 ε, F t x ∈ interior A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A := by
  intro x hx t ht
  obtain ⟨ε, hε, hentry⟩ := hlocal x hx
  let δ := Min.min ε t / 2
  have hδ : 0 < δ := half_pos (lt_min hε ht)
  have hδε : δ ≤ ε := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_left _ _)
  have hδt : δ ≤ t := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_right _ _)
  have hi := forwardInvariant_interior F hforward (hentry δ ⟨hδ, hδε⟩) (sub_nonneg.mpr hδt)
  rw [← F.map_add, sub_add_cancel] at hi
  exact hi

attribute [local instance 100] Classical.propDecidable in
/-- The flow enters the attaching union locally. -/
theorem ManifoldMorse.SignedMorseChart.exists_local_attachingUnion_entry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {x : M} (hx : x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hAx : x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :
    ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioc 0 ε,
        F t x ∈
          interior ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hmodel := (c.mem_attachingUnion_iff_model ρ hρ hblock hx).mp hAx
  have hαc : Continuous (fun t : ℝ => MorseHandle.descentFlow t (c.splitChart x)) :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : MorseHandle.descentFlow 0 (c.splitChart x) = e x :=
    MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), MorseHandle.descentFlow t (c.splitChart x) ∈ e.target :=
    hαc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hFc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ), F t x ∈ e.source :=
    hFc.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds
        (by
          rw [F.map_zero_apply]
          exact hx))
  have heqF := c.eventually_flow_eq_descentModel hV F hcurve hx heq
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.mp ((heqF.and htarget).and hsource)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  have hdist : Dist.dist t (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  obtain ⟨⟨heqt, htar⟩, hsrc⟩ := hεall hdist
  apply c.mem_interior_attachingUnion_of_model ρ hρ hblock hsrc
  have hcoord : c.splitChart (F t x) = MorseHandle.descentFlow t (c.splitChart x) := by
    rw [heqt]
    exact e.right_inv htar
  rw [hcoord]
  exact MorseHandle.descentFlow_mem_interior_lower_union_handle hρ ht.1 hmodel

attribute [local instance 100] Classical.propDecidable in
/-- The attaching union is forward invariant. -/
theorem ManifoldMorse.SignedMorseChart.forwardInvariant_attachingUnion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ,
        0 ≤ t → F t x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) := by
  apply
    FlowConstruction.forwardInvariant_of_local F
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    left
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact
        c.splitChart.toOpenPartialHomeomorph.map_target
          (hblock (MorseHandle.modelMap_mem_product hρ z))
    obtain ⟨ε, hε, hentry⟩ :=
      c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock hxsource (hagreement x hx)
        (Or.inr hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rcases ht.1.eq_or_lt with hzero | hpos
    · rw [← hzero, F.map_zero_apply]
      exact Or.inr hx
    · exact interior_subset (hentry t ⟨hpos, ht.2⟩)

attribute [local instance 100] Classical.propDecidable in
/-- The flow enters the attaching union's interior. -/
theorem ManifoldMorse.SignedMorseChart.interior_entry_attachingUnion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ,
        0 < t →
          F t x ∈
            interior ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  apply
    FlowConstruction.interior_entry_of_local F
      (c.forwardInvariant_attachingUnion hf hV F hcurve hmono ρ hρ hblock hagreement)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    have hlow : f (F t x) < f p - ρ ^ 2 := by
      change f x ≤ f p - ρ ^ 2 at hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1.le
        exact hle.trans_lt hlt
      · exact (hbottom x heq t ht.1).trans_le hx
    apply mem_interior.mpr
    exact
      ⟨{y | f y < f p - ρ ^ 2}, fun y hy => Or.inl (show f y ≤ f p - ρ ^ 2 from le_of_lt hy),
        isOpen_lt hf continuous_const, hlow⟩
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact
        c.splitChart.toOpenPartialHomeomorph.map_target
          (hblock (MorseHandle.modelMap_mem_product hρ z))
    exact
      c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock hxsource (hagreement x hx)
        (Or.inr hx)

/-! ### The entry time -/

/-- The entry time of a point into a set under the flow. -/
def FlowConstruction.entryTime {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (A : Set X)
    (x : X) : ℝ :=
  InfSet.sInf {t : ℝ | 0 ≤ t ∧ F t x ∈ A}

/-- The entry time is nonnegative. -/
theorem FlowConstruction.entryTime_nonneg {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : 0 ≤ entryTime F A x :=
  le_csInf hx (fun _ ht => ht.1)

/-- The entry time is bounded by any hitting time. -/
theorem FlowConstruction.entryTime_le_of_mem {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} {t : ℝ} (ht : 0 ≤ t) (hx : F t x ∈ A) : entryTime F A x ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, hx⟩

/-- The flow at the entry time lies in the closure. -/
theorem FlowConstruction.flow_entryTime_mem {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} (hA : IsClosed A) {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) :
    F (entryTime F A x) x ∈ A := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ F t x ∈ A} :=
    isClosed_Ici.inter (hA.preimage (F.continuous continuous_id continuous_const))
  exact (hclosed.csInf_mem hx ⟨0, fun _ hs => hs.1⟩).2

/-- The entry time is zero exactly on the set. -/
theorem FlowConstruction.entryTime_eq_zero {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} (hx : x ∈ A) : entryTime F A x = 0 := by
  have hhit : F 0 x ∈ A := by simpa only [F.map_zero_apply] using hx
  exact le_antisymm (entryTime_le_of_mem F le_rfl hhit) (entryTime_nonneg F ⟨0, le_rfl, hhit⟩)

/-- The entry time bound characterizes hitting the set. -/
theorem FlowConstruction.entryTime_le_iff {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t) : entryTime F A x ≤ t ↔ F t x ∈ A := by
  constructor
  · intro h
    have hh := hforward _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_nonneg.mpr h)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  · exact entryTime_le_of_mem F ht

/-- Past the entry time the flow lies in the interior. -/
theorem FlowConstruction.flow_mem_interior_of_entryTime_lt {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : entryTime F A x < t) : F t x ∈ interior A := by
  have hh := hentry _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_pos.mpr ht)
  rw [← F.map_add, sub_add_cancel] at hh
  exact hh

/-- The entry time of a frontier hit. -/
theorem FlowConstruction.entryTime_eq_of_flow_mem_frontier {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {x : X} {t : ℝ} (ht : 0 ≤ t)
    (hfront : F t x ∈ frontier A) : entryTime F A x = t := by
  have hmem : F t x ∈ A := by simpa only [hA.closure_eq] using frontier_subset_closure hfront
  apply le_antisymm (entryTime_le_of_mem F ht hmem)
  apply le_of_not_gt
  intro hlt
  exact hfront.2 (flow_mem_interior_of_entryTime_lt F hA hentry ⟨t, ht, hmem⟩ hlt)

/-- The entry time is continuous. -/
theorem FlowConstruction.continuousOn_entryTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {B : Set X}
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : ContinuousOn (entryTime F A) B := by
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hneg : a < 0
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hneg.trans_le (entryTime_nonneg F (hhit y hy))
    · have ha₀ : 0 ≤ a := le_of_not_gt hneg
      have hnot : F a x ∉ A := fun h => not_le_of_gt ha (entryTime_le_of_mem F ha₀ h)
      have hevent : ∀ᶠ y in 𝓝 x, F a y ∉ A :=
        (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
          (hA.isOpen_compl.mem_nhds hnot)
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hevent] with y
        hy hya
      apply lt_of_not_ge
      intro hle
      exact hya ((entryTime_le_iff F hA hforward (hhit y hy) ha₀).mp hle)
  · intro b hb
    obtain ⟨t, hxt, htb⟩ := exists_between hb
    have ht₀ : 0 ≤ t := (entryTime_nonneg F (hhit x hx)).trans hxt.le
    have hi := flow_mem_interior_of_entryTime_lt F hA hentry (hhit x hx) hxt
    have hevent : ∀ᶠ y in 𝓝 x, F t y ∈ interior A :=
      (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hi)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hevent] with y hy
    exact (entryTime_le_of_mem F ht₀ (interior_subset hy)).trans_lt htb

/-! ### The entry retraction -/

/-- The retraction sending a point to its entry point. -/
def FlowConstruction.entryRetraction {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : C(B, A)
    where
  toFun x := ⟨F (entryTime F A x.1) x.1, flow_entryTime_mem F hA (hhit x.1 x.2)⟩
  continuous_toFun :=
    (F.continuous
          (continuousOn_iff_continuous_domRestrict.mp
            (continuousOn_entryTime F hA hforward hentry hhit))
          continuous_subtype_val).subtype_mk
      _

/-- The entry retraction followed by inclusion is the flow to entry. -/
theorem FlowConstruction.entryRetraction_inclusion {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A B : Set X} (hA : IsClosed A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B) (x : A) :
    entryRetraction F hA hforward hentry hhit (ContinuousMap.inclusion hsub x) = x := by
  apply Subtype.ext
  change F (entryTime F A x.1) x.1 = x.1
  rw [entryTime_eq_zero F x.2, F.map_zero_apply]

/-- The deformation retract along the flow to the entry set. -/
def FlowConstruction.entryDeformation {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B)
    (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B) :
    (ContinuousMap.id B).HomotopyRel
      ((ContinuousMap.inclusion hsub).comp (entryRetraction F hA hforward hentry hhit))
      {x : B | x.1 ∈ A}
    where
  toFun
    q :=
    ⟨F (q.1.1 * entryTime F A q.2.1) q.2.1,
      hregion q.2.1 q.2.2 _ (mul_nonneg q.1.2.1 (entryTime_nonneg F (hhit q.2.1 q.2.2)))⟩
  continuous_toFun :=
    (F.continuous
          ((continuous_subtype_val.comp continuous_fst).mul
            ((continuousOn_iff_continuous_domRestrict.mp
                  (continuousOn_entryTime F hA hforward hentry hhit)).comp
              continuous_snd))
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change F ((0 : ℝ) * entryTime F A x.1) x.1 = x.1
    rw [MulZeroClass.zero_mul, F.map_zero_apply]
  map_one_left
    x := by
    apply Subtype.ext
    change F ((1 : ℝ) * entryTime F A x.1) x.1 = F (entryTime F A x.1) x.1
    rw [one_mul]
  prop' u x
    hx := by
    apply Subtype.ext
    change F (u.1 * entryTime F A x.1) x.1 = x.1
    rw [entryTime_eq_zero F (A := A) (show x.1 ∈ A from hx), MulZeroClass.mul_zero,
      F.map_zero_apply]

/-- The entry set is a deformation retract of the domain. -/
def FlowConstruction.entryHomotopyEquiv {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B)
    (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B) : A ≃ₕ B
    where
  toFun := ContinuousMap.inclusion hsub
  invFun := entryRetraction F hA hforward hentry hhit
  left_inv := by
    have heq :
      (entryRetraction F hA hforward hentry hhit).comp (ContinuousMap.inclusion hsub) =
        ContinuousMap.id A := by
      apply ContinuousMap.ext
      intro x
      exact entryRetraction_inclusion F hA hforward hentry hhit hsub x
    rw [heq]
  right_inv := ⟨(entryDeformation F hA hforward hentry hhit hsub hregion).toHomotopy.symm⟩

/-! ### Regular band flows -/

/-- A function along an integral curve differentiates to the field derivative. -/
theorem FlowConstruction.hasDerivAt_comp_integralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (v (γ t))) t := by
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • v (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (v (γ t))
  exact map_smul _ _ _

/-- A regular band field exists between two regular levels. -/
theorem FlowConstruction.exists_regularBandField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ),
      ContDiff ℝ ∞ φ ∧
        IsOpen W ∧
          Set.Icc a b ⊆ W ∧
            Set.EqOn φ (fun _ => 1) W ∧
              ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
                ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                    (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                  ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = φ (f x) := by
  let B := f '' ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Set.Icc a b ⊆ Bᶜ := by
    intro y hy
    rintro ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hφB, W, hW, hAW, -, hφW⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ ∘ f) := hφ.contMDiff.comp hf
  have hsupp : tsupport (φ ∘ f) ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hxφ := tsupport_comp_subset_preimage φ hf.continuous hx
    exact hφB hxφ ⟨x, hcrit, rfl⟩
  obtain ⟨V, hV, hVφ⟩ := exists_prescribedDerivativeField hf hχ hsupp
  exact ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩

/-- A regular band flow exists between two regular levels. -/
theorem FlowConstruction.exists_regularBandFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ) (F : Flow ℝ M),
      ContDiff ℝ ∞ φ ∧
        IsOpen W ∧
          Set.Icc a b ⊆ W ∧
            Set.EqOn φ (fun _ => 1) W ∧
              ∀ x t, HasDerivAt (fun s => f (F s x)) (φ (f (F t x))) t := by
  obtain ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩ := exists_regularBandField hf hband
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  refine ⟨φ, W, compactFlow hV₁, hφ, hW, hAW, hφW, ?_⟩
  intro x t
  have hd := hasDerivAt_comp_integralCurve hf (isMIntegralCurve_compactFlow hV₁ x) t
  rw [hVφ] at hd
  exact hd

/-- The flow fixes points where the field vanishes. -/
theorem FlowConstruction.flow_fixed_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hx : V x = 0)
    (t : ℝ) : F t x = x := by
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve x) (isMIntegralCurve_const hx)
      (t₀ := 0) (F.map_zero_apply x)
  exact congrFun heq t

/-- The flow preserves the regular locus. -/
theorem FlowConstruction.flow_preserves_regular {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f) (t : ℝ) :
    F t x ∉ ManifoldMorse.criticalPoints E f := by
  intro hy
  have hfix := flow_fixed_of_zero hV F hcurve (hzero (F t x) hy) (-t)
  have hinv : F (-t) (F t x) = x := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have hxy : x = F t x := hinv.symm.trans hfix
  exact hx (hxy.symm ▸ hy)

/-- The height is antitone along the descent flow. -/
theorem FlowConstruction.antitone_flow_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (x : M) : Antitone (fun t => f (F t x)) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
  intro t
  change mvfderiv 𝓘(ℝ, E) f (F t x) (V (F t x)) ≤ 0
  by_cases ht : F t x ∈ ManifoldMorse.criticalPoints E f
  · rw [hzero (F t x) ht, map_zero]
  · exact (hdesc (F t x) ht).le

/-- The height is strictly antitone along a nonvanishing descent flow. -/
theorem FlowConstruction.strictAnti_flow_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hx : x ∉ ManifoldMorse.criticalPoints E f) : StrictAnti (fun t => f (F t x)) :=
  strictAnti_of_hasDerivAt_neg (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
    (fun t => hdesc (F t x) (flow_preserves_regular hV F hcurve hzero hx t))

/-- An adapted descent flow exists on a regular region. -/
theorem FlowConstruction.exists_adaptedDescentFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [FiniteDimensional ℝ E] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ p ∈ ManifoldMorse.criticalPoints E f,
                  ∃ c : ManifoldMorse.SignedMorseChart (E := E) f p,
                    ∀ᶠ x in 𝓝 p, V x = c.descentField x) ∧
                (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ t, F t x = x) ∧
                  (∀ x,
                      x ∉ ManifoldMorse.criticalPoints E f →
                        StrictAnti (fun t => f (F t x))) ∧
                    ∀ x, Antitone (fun t => f (F t x)) := by
  obtain ⟨V, hV, hzero, hdesc, hcharts⟩ := ManifoldMorse.exists_adaptedDescentField hf hm
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  let F := compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V := isMIntegralCurve_compactFlow hV₁ x
  exact
    ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, fun x hx t =>
      flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t, fun x hx =>
      strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx, fun x =>
      antitone_flow_height hf F hcurve hzero hdesc x⟩

/-- The field derivative of the height is continuous. -/
theorem FlowConstruction.continuous_mvfderiv_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.continuous_tangentMap (by simp)).comp hV.continuous
  have hp := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp ht
  convert hp.snd using 1
  rfl

/-! ### Uniform absorption -/

/-- A uniform negative descent speed exists on a compact regular set. -/
theorem FlowConstruction.exists_uniform_negative_speed {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ δ > (0 : ℝ), ∀ x ∈ K, mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
  by_cases hne : K.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_mvfderiv_field hf hV).continuousOn
    refine ⟨-mvfderiv 𝓘(ℝ, E) f p (V p), neg_pos.mpr (hdesc p (hreg hp)), ?_⟩
    intro x hx
    have hle : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f p (V p) := hmax hx
    simpa only [neg_neg] using hle
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- A uniform residence bound in a regular band exists. -/
theorem FlowConstruction.exists_uniform_residence_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ T > (0 : ℝ), ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ K := by
  by_cases hne : K.Nonempty
  · obtain ⟨δ, hδ, hspeed⟩ := exists_uniform_negative_speed hf hV hdesc hK hreg
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf.continuous.continuousOn
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hf.continuous.continuousOn
    let T := (f q - f p + 1) / δ
    have hpq : f p ≤ f q := hmax hp
    have hgap : 0 < f q - f p + 1 := by linarith
    have hT : 0 < T := div_pos hgap hδ
    have hδT : δ * T = f q - f p + 1 := by
      dsimp [T]
      field_simp [hδ.ne']
    refine ⟨T, hT, ?_⟩
    intro γ hγ
    by_contra! hstay
    have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
      hasDerivAt_comp_integralCurve hf hγ t
    have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
    have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
    have hlast : T ∈ Set.Icc 0 T := ⟨hT.le, le_rfl⟩
    have hbound :=
      (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
        hdiff.differentiableOn
        (fun t ht => by
          rw [(hd t).deriv]
          exact hspeed (γ t) (hstay t (interior_subset ht)))
        0 hzero T hlast hT.le
    simp only [Function.comp_apply, sub_zero, neg_mul] at hbound
    rw [hδT] at hbound
    have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
    have hhi : f (γ 0) ≤ f q := hmax (hstay 0 hzero)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro γ _
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩

/-- A uniform entry time into critical neighborhoods exists. -/
theorem FlowConstruction.exists_uniform_criticalNeighborhood_entry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {U : Set M} (hU : IsOpen U)
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ U) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) < a ∨ F t x ∈ U := by
  let K := f ⁻¹' Set.Icc a b ∩ Uᶜ
  have hK : IsCompact K :=
    ((isClosed_Icc.preimage hf.continuous).inter hU.isClosed_compl).isCompact
  have hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    exact hx.2 (hcover x hcrit hx.1)
  obtain ⟨T, hT, hexit⟩ := exists_uniform_residence_bound hf hV hdesc hK hreg
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hout⟩ := hexit (fun s => F s x) (hcurve x)
  have hupper : f (F t x) ≤ b := by
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  refine ⟨t, ht, ?_⟩
  by_cases hlow : f (F t x) < a
  · exact Or.inl hlow
  · right
    by_contra hnot
    exact hout ⟨⟨le_of_not_gt hlow, hupper⟩, hnot⟩

/-- A uniform entry time into an absorbing set exists. -/
theorem FlowConstruction.exists_uniform_absorbing_entry {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M}
    (hlower : {x | f x ≤ a} ⊆ A)
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Set.Icc 0 T, F t x ∈ A := by
  obtain ⟨T, hT, hentry⟩ :=
    exists_uniform_criticalNeighborhood_entry hf hV hdesc F hcurve hmono isOpen_interior hcover
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hlow | hint⟩ := hentry x hx
  · exact ⟨t, ht, hlower (show f (F t x) ≤ a from le_of_lt hlow)⟩
  · exact ⟨t, ht, interior_subset hint⟩

/-- An absorbing sublevel is a deformation retract. -/
theorem FlowConstruction.exists_absorbingSublevelHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) :
    ∃ e : A ≃ₕ { x : M // f x ≤ b }, ∀ x, (e x).1 = x.1 := by
  obtain ⟨T, _, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hfinite : ∀ x ∈ {x | f x ≤ b}, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A := by
    intro x hx
    obtain ⟨t, ht, hm⟩ := hhit x hx
    exact ⟨t, ht.1, hm⟩
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hle.trans hx
  exact ⟨entryHomotopyEquiv F hA hforward hentry hfinite hupper hregion, fun _ => rfl⟩

attribute [local instance 100] Classical.propDecidable in
/-- The attaching union is a deformation retract of the sublevel. -/
theorem ManifoldMorse.SignedMorseChart.exists_attachingUnionHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₕ
        { x : M // f x ≤ f p + ρ ^ 2 },
      ∀ x, (e x).1 = x.1 := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x := by
    intro x hx t ht
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp : x = p := hband x hcrit ⟨hx.ge, by rw [hx]; linarith [sq_nonneg ρ]⟩
      rw [hxp] at hx
      nlinarith [sq_pos_of_pos hρ]
    simpa only [F.map_zero_apply] using
      FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  apply
    FlowConstruction.exists_absorbingSublevelHomotopyEquiv hf hV hdesc F hcurve hmono
      ((isClosed_le hf.continuous continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      Set.subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock) (a := f p - ρ ^ 2)
  · intro x hcrit hx
    have hxp := hband x hcrit hx
    subst x
    exact
      interior_mono Set.subset_union_right (c.mem_interior_range_attachingHandleMap ρ hρ hblock)
  · exact
      c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
  · exact
      c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
        hbottom

/-- The entry time of a flowed point shifts by the flow time. -/
theorem FlowConstruction.entryTime_flow_of_le {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ}
    (ht : 0 ≤ t) (hle : t ≤ entryTime F A x) : entryTime F A (F t x) = entryTime F A x - t := by
  have hhit : F (entryTime F A x - t) (F t x) ∈ A := by
    rw [← F.map_add, sub_add_cancel]
    exact flow_entryTime_mem F hA hx
  have hy : ∃ u : ℝ, 0 ≤ u ∧ F u (F t x) ∈ A := ⟨_, sub_nonneg.mpr hle, hhit⟩
  apply le_antisymm (entryTime_le_of_mem F (sub_nonneg.mpr hle) hhit)
  have hh := flow_entryTime_mem F hA hy
  rw [← F.map_add] at hh
  have hb := entryTime_le_of_mem F (add_nonneg (entryTime_nonneg F hy) ht) hh
  linarith

/-- An interior hit bounds the entry time. -/
theorem FlowConstruction.entryTime_lt_of_flow_mem_interior {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} {x : X} {t : ℝ} (ht : 0 < t) (hx : F t x ∈ interior A) :
    entryTime F A x < t := by
  have he : ∀ᶠ s in 𝓝 t, 0 < s ∧ F s x ∈ interior A :=
    (eventually_gt_nhds ht).and
      ((F.continuous continuous_id continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hx))
  obtain ⟨s, hst, hs⟩ := he.exists_lt
  exact (entryTime_le_of_mem F hs.1.le (interior_subset hs.2)).trans_lt hst

/-- The entry time adds under a positive flow. -/
theorem FlowConstruction.entryTime_eq_add_of_flow_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t)
    (hpos : 0 < entryTime F A (F t x)) : entryTime F A x = t + entryTime F A (F t x) := by
  have hle : t ≤ entryTime F A x := by
    by_contra h
    have hh := (entryTime_le_iff F hA hforward hx ht).mp (le_of_not_ge h)
    rw [entryTime_eq_zero F hh] at hpos
    exact lt_irrefl _ hpos
  rw [entryTime_flow_of_le F hA hx ht hle]
  ring

/-! ### Flow collar data -/

/-- Data for a flow collar: a core, an inner set, and timing bounds. -/
structure FlowConstruction.FlowCollarData {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (A B : Set X) where
  time : ℝ
  time_pos : 0 < time
  closed_outer : IsClosed B
  closed_inner : IsClosed A
  inner_subset : A ⊆ B
  forward_outer : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B
  forward_inner : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A
  strict_outer : ∀ x ∈ B, ∀ t : ℝ, 0 < t → F t x ∈ interior B
  strict_inner : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A
  core_inside : ∀ x ∈ B, F time x ∈ interior A

/-- The core of the flow collar. -/
def FlowConstruction.FlowCollarData.core {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) : Set X :=
  (F (-d.time)) ⁻¹' B

/-- The collar core is closed. -/
theorem FlowConstruction.FlowCollarData.closed_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    IsClosed d.core :=
  d.closed_outer.preimage (F.continuous continuous_const continuous_id)

/-- The collar core is forward invariant. -/
theorem FlowConstruction.FlowCollarData.forward_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    ∀ x ∈ d.core, ∀ t : ℝ, 0 ≤ t → F t x ∈ d.core := by
  intro x hx t ht
  change F (-d.time) (F t x) ∈ B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.forward_outer _ hx t ht

/-- The collar core is strictly absorbing. -/
theorem FlowConstruction.FlowCollarData.strict_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    ∀ x ∈ d.core, ∀ t : ℝ, 0 < t → F t x ∈ interior d.core := by
  intro x hx t ht
  apply preimage_interior_subset_interior_preimage (F.continuous continuous_const continuous_id)
  change F (-d.time) (F t x) ∈ interior B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.strict_outer _ hx t ht

/-- The flow at the duration lands in the core. -/
theorem FlowConstruction.FlowCollarData.flow_time_mem_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : F d.time x ∈ d.core := by
  change F (-d.time) (F d.time x) ∈ B
  simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hx

/-- Every point's flow hits the core. -/
theorem FlowConstruction.FlowCollarData.hits_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ d.core :=
  ⟨d.time, d.time_pos.le, d.flow_time_mem_core hx⟩

/-- Every point's flow hits the inner set. -/
theorem FlowConstruction.FlowCollarData.hits_inner {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A :=
  ⟨d.time, d.time_pos.le, interior_subset (d.core_inside x hx)⟩

/-- The collar duration: the entry time into the inner set. -/
def FlowConstruction.FlowCollarData.duration {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  FlowConstruction.entryTime F d.core x.1

/-- The collar duration is nonnegative. -/
theorem FlowConstruction.FlowCollarData.duration_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.duration x :=
  FlowConstruction.entryTime_nonneg F (d.hits_core x.2)

/-- The collar duration is bounded. -/
theorem FlowConstruction.FlowCollarData.duration_le {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x ≤ d.time :=
  FlowConstruction.entryTime_le_of_mem F d.time_pos.le (d.flow_time_mem_core x.2)

/-- The collar duration is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_duration {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.duration :=
  continuousOn_iff_continuous_domRestrict.mp
    (FlowConstruction.continuousOn_entryTime F d.closed_core d.forward_core d.strict_core
      (fun _ hx => d.hits_core hx))

/-- The collar origin: the entry point in the inner set. -/
def FlowConstruction.FlowCollarData.origin {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : B :=
  ⟨F (d.duration x - d.time) x.1,
    by
    have h := FlowConstruction.flow_entryTime_mem F d.closed_core (d.hits_core x.2)
    change F (-d.time) (F (d.duration x) x.1) ∈ B at h
    simpa only [← F.map_add, sub_eq_add_neg, add_comm] using h⟩

/-- The collar origin is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_origin {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.origin :=
  (F.continuous (d.continuous_duration.sub continuous_const) continuous_subtype_val).subtype_mk _

/-- A point is the flow of its origin for its duration. -/
theorem FlowConstruction.FlowCollarData.origin_reconstruct {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    F (d.time - d.duration x) (d.origin x).1 = x.1 := by
  change F (d.time - d.duration x) (F (d.duration x - d.time) x.1) = x.1
  rw [← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]

/-- The collar delay before reaching the core. -/
def FlowConstruction.FlowCollarData.delay {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  FlowConstruction.entryTime F A (d.origin x).1

/-- The collar delay is nonnegative. -/
theorem FlowConstruction.FlowCollarData.delay_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.delay x :=
  FlowConstruction.entryTime_nonneg F (d.hits_inner (d.origin x).2)

/-- The collar delay is bounded. -/
theorem FlowConstruction.FlowCollarData.delay_lt {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.delay x < d.time :=
  FlowConstruction.entryTime_lt_of_flow_mem_interior F d.time_pos
    (d.core_inside _ (d.origin x).2)

/-- The collar delay is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_delay {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.delay :=
  (continuousOn_iff_continuous_domRestrict.mp
        (FlowConstruction.continuousOn_entryTime F d.closed_inner d.forward_inner
          d.strict_inner (fun _ hx => d.hits_inner hx))).comp
    d.continuous_origin

/-- The rescaling factor of the collar time. -/
def FlowConstruction.FlowCollarData.factor {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  (d.time - d.delay x) / d.time

/-- The rescaling factor is positive. -/
theorem FlowConstruction.FlowCollarData.factor_pos {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 < d.factor x :=
  div_pos (sub_pos.mpr (d.delay_lt x)) d.time_pos

/-- The rescaling factor is at most one. -/
theorem FlowConstruction.FlowCollarData.factor_le_one {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.factor x ≤ 1 := by
  apply (div_le_one d.time_pos).mpr
  linarith [d.delay_nonneg x]

/-- The rescaled time factor identity. -/
theorem FlowConstruction.FlowCollarData.time_mul_factor {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.time * d.factor x = d.time - d.delay x := by
  dsimp [factor]
  field_simp [d.time_pos.ne']

/-- The rescaling factor is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_factor {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.factor :=
  (continuous_const.sub d.continuous_delay).div_const _

/-- The duration is bounded by the retained time. -/
theorem FlowConstruction.FlowCollarData.duration_le_retained {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) (hx : x.1 ∈ A) :
    d.duration x ≤ d.time * d.factor x := by
  have hhit : F (d.time - d.duration x) (d.origin x).1 ∈ A := by rwa [d.origin_reconstruct]
  have h := FlowConstruction.entryTime_le_of_mem F (sub_nonneg.mpr (d.duration_le x)) hhit
  change d.delay x ≤ d.time - d.duration x at h
  rw [d.time_mul_factor]
  linarith

/-- The collar shift of a point. -/
def FlowConstruction.FlowCollarData.shift {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  d.duration x * (1 - d.factor x)

/-- The collar shift is nonnegative. -/
theorem FlowConstruction.FlowCollarData.shift_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.shift x :=
  mul_nonneg (d.duration_nonneg x) (sub_nonneg.mpr (d.factor_le_one x))

/-- The collar shift is bounded by the duration. -/
theorem FlowConstruction.FlowCollarData.shift_le_duration {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.shift x ≤ d.duration x := by
  dsimp [shift]
  nlinarith [mul_nonneg (d.duration_nonneg x) (d.factor_pos x).le]

/-- The collar shift is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_shift {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.shift :=
  d.continuous_duration.mul (continuous_const.sub d.continuous_factor)

/-! ### The collar rescaling -/

/-- The rescaling homeomorphism candidate of the collar. -/
def FlowConstruction.FlowCollarData.rescale {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) : C(B, B)
    where
  toFun x := ⟨F (d.shift x) x.1, d.forward_outer x.1 x.2 _ (d.shift_nonneg x)⟩
  continuous_toFun := (F.continuous d.continuous_shift continuous_subtype_val).subtype_mk _

/-- The rescaling computes from the origin. -/
theorem FlowConstruction.FlowCollarData.rescale_from_origin {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).1 = F (d.time - d.duration x * d.factor x) (d.origin x).1 := by
  change F (d.shift x) x.1 = _
  conv_lhs => rw [← d.origin_reconstruct x]
  rw [← F.map_add]
  congr 1
  dsimp [shift]
  ring

/-- The rescaling lands in the inner set. -/
theorem FlowConstruction.FlowCollarData.rescale_mem_inner {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).1 ∈ A := by
  rw [d.rescale_from_origin]
  have hh : d.delay x ≤ d.time - d.duration x * d.factor x := by
    have h := mul_le_mul_of_nonneg_right (d.duration_le x) (d.factor_pos x).le
    rw [d.time_mul_factor] at h
    linarith
  exact
    (FlowConstruction.entryTime_le_iff F d.closed_inner d.forward_inner
          (d.hits_inner (d.origin x).2) ((d.delay_nonneg x).trans hh)).mp
      hh

/-- The duration of a rescaled point. -/
theorem FlowConstruction.FlowCollarData.duration_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration (d.rescale x) = d.duration x * d.factor x := by
  change FlowConstruction.entryTime F d.core (F (d.shift x) x.1) = _
  rw [FlowConstruction.entryTime_flow_of_le F d.closed_core (d.hits_core x.2)
      (d.shift_nonneg x) (d.shift_le_duration x)]
  change d.duration x - d.shift x = _
  dsimp [shift]
  ring

/-- The origin of a rescaled point. -/
theorem FlowConstruction.FlowCollarData.origin_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.origin (d.rescale x) = d.origin x := by
  apply Subtype.ext
  change F (d.duration (d.rescale x) - d.time) (F (d.shift x) x.1) = F (d.duration x - d.time) x.1
  rw [d.duration_rescale, ← F.map_add]
  congr 1
  dsimp [shift]
  ring

/-- The factor of a rescaled point. -/
theorem FlowConstruction.FlowCollarData.factor_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.factor (d.rescale x) = d.factor x := by
  unfold factor delay
  rw [d.origin_rescale]

/-- The rescaling is injective. -/
theorem FlowConstruction.FlowCollarData.rescale_injective {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Function.Injective d.rescale := by
  intro x y h
  have hfactor : d.factor x = d.factor y := by rw [← d.factor_rescale x, ← d.factor_rescale y, h]
  have hdur : d.duration x = d.duration y := by
    have he := congrArg d.duration h
    rw [d.duration_rescale, d.duration_rescale, hfactor] at he
    exact mul_right_cancel₀ (d.factor_pos y).ne' he
  have horigin : d.origin x = d.origin y := by rw [← d.origin_rescale x, ← d.origin_rescale y, h]
  apply Subtype.ext
  rw [← d.origin_reconstruct x, ← d.origin_reconstruct y, hdur, horigin]

/-- A zero-duration point is fixed by the rescaling. -/
theorem FlowConstruction.FlowCollarData.rescale_eq_self_of_duration_eq_zero {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) (hx : d.duration x = 0) :
    d.rescale x = x := by
  apply Subtype.ext
  change F (d.shift x) x.1 = x.1
  simp only [shift, hx, MulZeroClass.zero_mul, F.map_zero_apply]

/-- Every point is a rescale of a core point. -/
theorem FlowConstruction.FlowCollarData.exists_rescale_eq {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (y : B)
    (hy : y.1 ∈ A) : ∃ x : B, d.rescale x = y := by
  by_cases hs : d.duration y = 0
  · exact ⟨y, d.rescale_eq_self_of_duration_eq_zero y hs⟩
  have hspos : 0 < d.duration y := lt_of_le_of_ne (d.duration_nonneg y) (Ne.symm hs)
  let r := d.duration y / d.factor y
  have hr₀ : 0 ≤ r := (div_pos hspos (d.factor_pos y)).le
  have hrT : r ≤ d.time := (div_le_iff₀ (d.factor_pos y)).mpr (d.duration_le_retained y hy)
  have hr : r * d.factor y = d.duration y := div_mul_cancel₀ _ (d.factor_pos y).ne'
  have hsr : d.duration y ≤ r := by
    have hh := mul_le_mul_of_nonneg_left (d.factor_le_one y) hr₀
    rwa [mul_one, hr] at hh
  let x : B :=
    ⟨F (d.time - r) (d.origin y).1, d.forward_outer _ (d.origin y).2 _ (sub_nonneg.mpr hrT)⟩
  have hxy : F (r - d.duration y) x.1 = y.1 := by
    change F (r - d.duration y) (F (d.time - r) (d.origin y).1) = y.1
    rw [← F.map_add]
    convert d.origin_reconstruct y using 2
    ring
  have hdx : d.duration x = r := by
    have hh :=
      FlowConstruction.entryTime_eq_add_of_flow_pos F d.closed_core d.forward_core
        (d.hits_core x.2) (sub_nonneg.mpr hsr)
        (show 0 < FlowConstruction.entryTime F d.core (F (r - d.duration y) x.1) by
          rw [hxy]; exact hspos)
    rw [hxy] at hh
    change d.duration x = r - d.duration y + d.duration y at hh
    linarith
  have hox : d.origin x = d.origin y := by
    apply Subtype.ext
    change F (d.duration x - d.time) (F (d.time - r) (d.origin y).1) = _
    rw [hdx, ← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]
  have hfx : d.factor x = d.factor y := by
    unfold factor delay
    rw [hox]
  refine ⟨x, Subtype.ext ?_⟩
  rw [d.rescale_from_origin, hdx, hfx, hox, hr, d.origin_reconstruct]

/-! ### The collar homeomorphism -/

/-- The inner map of the collar homeomorphism. -/
def FlowConstruction.FlowCollarData.innerMap {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) : C(B, A)
    where
  toFun x := ⟨(d.rescale x).1, d.rescale_mem_inner x⟩
  continuous_toFun := (continuous_subtype_val.comp d.rescale.continuous).subtype_mk _

/-- The inner map is bijective. -/
theorem FlowConstruction.FlowCollarData.innerMap_bijective {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Function.Bijective d.innerMap := by
  constructor
  · intro x y h
    apply d.rescale_injective
    exact Subtype.ext (congrArg (fun z : A => (z : X)) h)
  · intro y
    obtain ⟨x, hx⟩ := d.exists_rescale_eq ⟨y.1, d.inner_subset y.2⟩ y.2
    exact ⟨x, Subtype.ext (congrArg (fun z : B => (z : X)) hx)⟩

/-- The flow collar homeomorphism. -/
def FlowConstruction.FlowCollarData.homeomorph {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) [T2Space X]
    [CompactSpace B] : B ≃ₜ A :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective d.innerMap d.innerMap_bijective)
    d.innerMap.continuous

/-- The interior is characterized by the duration-time inequality. -/
theorem FlowConstruction.FlowCollarData.duration_lt_time_iff_interior {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x < d.time ↔ (x : X) ∈ interior B := by
  constructor
  · intro hlt
    have hi :=
      d.strict_outer (d.origin x).val (d.origin x).property (d.time - d.duration x)
        (sub_pos.mpr hlt)
    rwa [d.origin_reconstruct] at hi
  · intro hi
    have hcore : F d.time x.val ∈ interior d.core := by
      apply
        preimage_interior_subset_interior_preimage (F.continuous continuous_const continuous_id)
      change F (-d.time) (F d.time x.val) ∈ interior B
      simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hi
    exact FlowConstruction.entryTime_lt_of_flow_mem_interior F d.time_pos hcore

/-- The frontier is characterized by the duration-time equality. -/
theorem FlowConstruction.FlowCollarData.duration_eq_time_iff_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x = d.time ↔ (x : X) ∈ frontier B := by
  rw [frontier, d.closed_outer.closure_eq]
  constructor
  · intro heq
    refine ⟨x.property, ?_⟩
    intro hi
    have hlt := (d.duration_lt_time_iff_interior x).mpr hi
    exact (ne_of_lt hlt) heq
  · intro hx
    apply le_antisymm (d.duration_le x)
    exact le_of_not_gt (fun hlt => hx.2 ((d.duration_lt_time_iff_interior x).mp hlt))

/-- The rescaling preserves the interior. -/
theorem FlowConstruction.FlowCollarData.rescale_mem_interior_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).val ∈ interior A ↔ x.val ∈ interior B := by
  suffices h : (d.rescale x).val ∈ interior A ↔ d.duration x < d.time from
    h.trans (d.duration_lt_time_iff_interior x)
  constructor
  · intro hi
    by_contra hnot
    have heq : d.duration x = d.time := le_antisymm (d.duration_le x) (le_of_not_gt hnot)
    have horigin : (d.origin x).val = x.val := by
      change F (d.duration x - d.time) x.val = x.val
      rw [heq, sub_self, F.map_zero_apply]
    have hentry : F (d.delay x) (d.origin x).val ∈ interior A := by
      rw [d.rescale_from_origin, heq, d.time_mul_factor, sub_sub_cancel] at hi
      exact hi
    by_cases hpos : 0 < d.delay x
    · have hlt := FlowConstruction.entryTime_lt_of_flow_mem_interior F hpos hentry
      exact (lt_irrefl (d.delay x)) hlt
    · have hzero : d.delay x = 0 := le_antisymm (le_of_not_gt hpos) (d.delay_nonneg x)
      rw [hzero, F.map_zero_apply, horigin] at hentry
      have hB := interior_mono d.inner_subset hentry
      exact hnot ((d.duration_lt_time_iff_interior x).mpr hB)
  · intro hlt
    rw [d.rescale_from_origin]
    have hmul := mul_lt_mul_of_pos_right hlt (d.factor_pos x)
    rw [d.time_mul_factor] at hmul
    have hdelay : d.delay x < d.time - d.duration x * d.factor x := by linarith
    exact
      FlowConstruction.flow_mem_interior_of_entryTime_lt F d.closed_inner d.strict_inner
        (d.hits_inner (d.origin x).property) hdelay

/-- The inner map preserves the frontier. -/
theorem FlowConstruction.FlowCollarData.innerMap_mem_frontier_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.innerMap x).val ∈ frontier A ↔ x.val ∈ frontier B := by
  change (d.rescale x).val ∈ frontier A ↔ x.val ∈ frontier B
  rw [frontier, frontier, d.closed_inner.closure_eq, d.closed_outer.closure_eq]
  constructor
  · intro hx
    exact ⟨x.property, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mpr hi)⟩
  · intro hx
    exact ⟨d.rescale_mem_inner x, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mp hi)⟩

/-- The collar homeomorphism preserves the frontier. -/
theorem FlowConstruction.FlowCollarData.homeomorph_mem_frontier_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B) :
    (d.homeomorph x).val ∈ frontier A ↔ x.val ∈ frontier B :=
  d.innerMap_mem_frontier_iff x

/-- The collar homeomorphism computes the flow to the entry time. -/
theorem FlowConstruction.FlowCollarData.homeomorph_eq_flow_entryTime {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hx : x.val ∈ frontier B) :
    (d.homeomorph x).val = F (FlowConstruction.entryTime F A x.val) x.val := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hx
  have ho : (d.origin x).val = x.val := by
    change F (d.duration x - d.time) x.val = x.val
    rw [ht, sub_self, F.map_zero_apply]
  change (d.rescale x).val = _
  rw [d.rescale_from_origin, ht, d.time_mul_factor, sub_sub_cancel]
  change F (FlowConstruction.entryTime F A (d.origin x).val) (d.origin x).val = _
  rw [ho]

/-- The collar homeomorphism on the frontier is the flow. -/
theorem FlowConstruction.FlowCollarData.homeomorph_eq_flow_of_mem_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hx : x.val ∈ frontier B) {t : ℝ} (ht : 0 ≤ t) (hfront : F t x.val ∈ frontier A) :
    (d.homeomorph x).val = F t x.val := by
  rw [d.homeomorph_eq_flow_entryTime x hx,
    FlowConstruction.entryTime_eq_of_flow_mem_frontier F d.closed_inner d.strict_inner ht
      hfront]

/-- The collar homeomorphism inverse on the frontier is the flow. -/
theorem FlowConstruction.FlowCollarData.homeomorph_symm_eq_flow_of_mem_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (y : A)
    (hy : y.val ∈ frontier A) {t : ℝ} (ht : t ≤ 0) (hfront : F t y.val ∈ frontier B) :
    (d.homeomorph.symm y).val = F t y.val := by
  have hmem : F t y.val ∈ B := by
    simpa only [d.closed_outer.closure_eq] using frontier_subset_closure hfront
  let x : B := ⟨F t y.val, hmem⟩
  have hreturn : F (-t) x.val = y.val := by
    change F (-t) (F t y.val) = y.val
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have heq : d.homeomorph x = y := by
    apply Subtype.ext
    rw [d.homeomorph_eq_flow_of_mem_frontier x hfront (neg_nonneg.mpr ht) (hreturn ▸ hy), hreturn]
  have hinv := congrArg d.homeomorph.symm heq
  rw [d.homeomorph.symm_apply_apply] at hinv
  exact congrArg (fun z : B => z.val) hinv.symm

/-- The rescaling fixes the inner frontier. -/
theorem FlowConstruction.FlowCollarData.rescale_eq_self_of_mem_inner_frontier_outer
    {X : Type*} [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) (hxA : x.val ∈ A)
    (hxB : x.val ∈ frontier B) : d.rescale x = x := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hxB
  have hret := d.duration_le_retained x hxA
  rw [ht] at hret
  have hfac : d.factor x = 1 := by nlinarith [d.factor_le_one x, d.time_pos]
  apply Subtype.ext
  change F (d.shift x) x.val = x.val
  simp only [shift, hfac, sub_self, MulZeroClass.mul_zero, F.map_zero_apply]

/-- The collar homeomorphism fixes the common frontier. -/
theorem FlowConstruction.FlowCollarData.homeomorph_fixed_on_common_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hxA : x.val ∈ A) (hxB : x.val ∈ frontier B) : (d.homeomorph x).val = x.val :=
  congrArg (fun y : B => y.val) (d.rescale_eq_self_of_mem_inner_frontier_outer x hxA hxB)

/-- An absorbing sublevel homeomorphism with boundary orbit control exists. -/
theorem FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    ∃ e : { x : M // f x ≤ b } ≃ₜ A,
      (∀ x, (e x).val ∈ frontier A ↔ x.val ∈ frontier {y : M | f y ≤ b}) ∧
        (∀ x, x.val ∈ A → x.val ∈ frontier {y : M | f y ≤ b} → (e x).val = x.val) ∧
          (∀ y,
            y.val ∈ frontier A →
              ∀ t : ℝ,
                t ≤ 0 → F t y.val ∈ frontier {x : M | f x ≤ b} → (e.symm y).val = F t y.val) := by
  obtain ⟨T, hT, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hh.trans hx
  have hstrict : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 < t → F t x ∈ interior {x | f x ≤ b} := by
    intro x hx t ht
    change f x ≤ b at hx
    apply
      interior_maximal
        (show {x | f x < b} ⊆ {x | f x ≤ b} from fun x (hy : f x < b) =>
          (show f x ≤ b from hy.le))
        (isOpen_lt hf.continuous continuous_const)
    rcases lt_or_eq_of_le hx with hlt | heq
    · have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.le
      exact hh.trans_lt hlt
    · exact htop x heq t ht
  let d : FlowCollarData F A {x | f x ≤ b} :=
    { time := T + 1
      time_pos := by linarith
      closed_outer := isClosed_le hf.continuous continuous_const
      closed_inner := hA
      inner_subset := hupper
      forward_outer := hregion
      forward_inner := hforward
      strict_outer := hstrict
      strict_inner := hentry
      core_inside := by
        intro x hx
        obtain ⟨t, ht, hmem⟩ := hhit x hx
        have hh := hentry _ hmem (T + 1 - t) (by linarith [ht.2])
        rwa [← F.map_add, sub_add_cancel] at hh }
  have : CompactSpace ↥({x : M | f x ≤ b}) :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact
    ⟨d.homeomorph, d.homeomorph_mem_frontier_iff, d.homeomorph_fixed_on_common_frontier,
      fun y hy _ ht hfront => d.homeomorph_symm_eq_flow_of_mem_frontier y hy ht hfront⟩

/-- The frontier of a strict-flow sublevel is the level set. -/
theorem FlowConstruction.frontier_sublevel_eq_of_strict_flow {X : Type*}
    [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) (F : Flow ℝ X)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {b : ℝ}
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    frontier {x | f x ≤ b} = {x | f x = b} := by
  have hclosed : IsClosed {x | f x ≤ b} := isClosed_le hf continuous_const
  ext x
  rw [frontier, hclosed.closure_eq]
  constructor
  · rintro ⟨hx, hnot⟩
    apply le_antisymm hx
    by_contra hn
    have hlt : f x < b := lt_of_not_ge hn
    exact
      hnot (interior_maximal (fun y (hy : f y < b) => hy.le) (isOpen_lt hf continuous_const) hlt)
  · intro hx
    refine ⟨(show f x ≤ b from hx.le), ?_⟩
    intro hi
    have he : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ b} := by
      have hcont : ContinuousAt (fun t : ℝ => F t x) 0 :=
        (F.continuous continuous_id continuous_const).continuousAt
      apply hcont.preimage_mem_nhds
      simpa only [F.map_zero_apply] using isOpen_interior.mem_nhds hi
    obtain ⟨s, hs, hsB⟩ := he.exists_lt
    have hy : F s x ∈ {y | f y ≤ b} := interior_subset hsB
    have hxy : f x ≤ f (F s x) := by
      have hh := hmono (F s x) (show (0 : ℝ) ≤ -s by linarith)
      simpa only [F.map_zero_apply, ← F.map_add, neg_add_cancel] using hh
    have hyeq : f (F s x) = b := le_antisymm hy (hx ▸ hxy)
    have hstrict := htop (F s x) hyeq (-s) (by linarith)
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hx] at hstrict
    exact lt_irrefl b hstrict
end Mathoverflow1973
