/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.Cubic
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Flows of the cubic model

The flow machinery attached to the cubic model of `Morse.Cubic`: strict
descent into sublevel sets and level basins, the signed level time,
height-translating flows, the cubic flow cylinder, fiberwise
diffeomorphisms, the suspended flow, supported isotopies, suspension
coordinates and the local field replacement, plus the declarations of the
later cancellation subjects that the rearrangement modules need before
`Morse.Rearrangement` (native Morse index, quadratic germs, omega limits).

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Thm 4.1.

## Tags

morse-theory, cancellation, gradient-like-flow, suspension
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

/-! ### Strict descent and level basins -/

/-- The basin of a level set under the flow. -/
def FlowCancellation.levelBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ)
    (c : ℝ) : Set X :=
  {x | ∃ t : ℝ, f (F t x) = c}

/-! ### The signed level time -/

/-- The signed time at which the flow crosses the level. -/
def FlowCancellation.signedLevelTime {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c : ℝ) (x : X) : ℝ := by
  classical exact if h : x ∈ levelBasin F f c then h.choose else 0

/-- The signed level time hits the level. -/
theorem FlowCancellation.signedLevelTime_hits {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {x : X} (hx : x ∈ levelBasin F f c) :
    f (F (signedLevelTime F f c x) x) = c := by
  rw [signedLevelTime, dif_pos hx]
  exact hx.choose_spec

/-- Basin membership is characterized by hitting the level. -/
theorem FlowCancellation.levelBasin_flow_iff {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c s : ℝ) (x : X) :
    F s x ∈ levelBasin F f c ↔ x ∈ levelBasin F f c := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t + s, by simpa only [F.map_add] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ?_⟩
    simpa only [← F.map_add, sub_add_cancel] using ht

/-- The signed level time of a level point. -/
theorem FlowCancellation.signedLevelTime_eq_of_level {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} {t : ℝ} (ht : f (F t x) = c) :
    signedLevelTime F f c x = t :=
  flow_level_time_unique F hf hD hder hboundary x (signedLevelTime_hits F f c ⟨t, ht⟩) ht

/-- The signed level time on the level is zero. -/
theorem FlowCancellation.signedLevelTime_eq_zero {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : signedLevelTime F f c x = 0 :=
  signedLevelTime_eq_of_level F hf hD hder hboundary (by simpa only [F.map_zero_apply] using hx)

/-- The signed level time shifts under the flow. -/
theorem FlowCancellation.signedLevelTime_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : x ∈ levelBasin F f c) (s : ℝ) :
    signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  apply signedLevelTime_eq_of_level F hf hD hder hboundary
  rw [← F.map_add, sub_add_cancel]
  exact signedLevelTime_hits F f c hx

/-! ### Height-translating flows -/

/-- An enlarged interval containing a compact interval exists. -/
theorem FlowConstruction.exists_enlarged_interval {a b : ℝ} (hab : a ≤ b) {W : Set ℝ}
    (hW : IsOpen W) (hIW : Set.Icc a b ⊆ W) : ∃ l u : ℝ, l < a ∧ b < u ∧ Set.Ioo l u ⊆ W := by
  obtain ⟨l, r, hla, hL⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hW.mem_nhds (hIW ⟨le_rfl, hab⟩))
  obtain ⟨s, u, hbu, hR⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hW.mem_nhds (hIW ⟨hab, le_rfl⟩))
  refine ⟨l, u, hla.1, hbu.2, ?_⟩
  intro y hy
  by_cases hya : y < a
  · exact hL ⟨hy.1, hya.trans hla.2⟩
  by_cases hby : b < y
  · exact hR ⟨hbu.1.trans hby, hy.2⟩
  exact hIW ⟨le_of_not_gt hya, le_of_not_gt hby⟩

/-- The scalar height translation of a product field. -/
theorem FlowConstruction.scalar_height_translation {φ γ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {W : Set ℝ} (hW : IsOpen W) {a b c t : ℝ} (hIW : Set.Icc a b ⊆ W)
    (hφW : Set.EqOn φ (fun _ => 1) W) (hγ : ∀ s, HasDerivAt γ (φ (γ s)) s) (hγ₀ : γ 0 = c)
    (hc : c ∈ Set.Icc a b) (ht : c + t ∈ Set.Icc a b) : γ t = c + t := by
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_enlarged_interval (hc.1.trans hc.2) hW hIW
  let V : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun x => (NormedSpace.fromTangentSpace x).symm (φ x)
  have hV :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (hφ.of_le (by simp))
  have hactual : IsMIntegralCurveOn γ V (Set.Ioo (l - c) (u - c)) := by
    intro s hs
    exact (hγ s).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hlinear : IsMIntegralCurveOn (fun s => c + s) V (Set.Ioo (l - c) (u - c)) := by
    intro s hs
    have hcs : c + s ∈ W := hlu ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd : HasDerivAt (fun r => c + r) (φ (c + s)) s := by
      rw [hφW hcs]
      exact (hasDerivAt_id s).const_add c
    exact hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hzero : (0 : ℝ) ∈ Set.Ioo (l - c) (u - c) := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have htime : t ∈ Set.Ioo (l - c) (u - c) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hV hactual hlinear
      (by simpa only [add_zero] using hγ₀) htime

/-- A global flow satisfies `f (F t x) = f x + t` whenever both `f x` and `f x + t` lie in the given regular band. -/
theorem FlowConstruction.exists_heightTranslatingFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ F : Flow ℝ M, ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t := by
  obtain ⟨φ, W, F, hφ, hW, hIW, hφW, hF⟩ := exists_regularBandFlow hf hband
  refine ⟨F, ?_⟩
  intro x t hx ht
  exact scalar_height_translation hφ hW hIW hφW (hF x) (by simp only [Flow.map_zero_apply]) hx ht

/-! ### Basins of the adapted windows -/

attribute [local instance 100] Classical.propDecidable in
/-- The attaching basin of the adapted windows. -/
theorem AdaptedWindows.attaching_basin_iff {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f) (x : (S.data p).LowerLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val) ↔
      x ∈ Set.range (S.data p).surgery.attachingSphere := by
  let d := S.data p
  have hh :=
    MorseCancellation.native_attaching_core_basin_iff d.chart hf S.smooth S.flow S.integral d.radius
      d.radius_pos d.block (S.model_germ p) (fun y hy => S.descent y (d.lower_regular y hy))
      x.property
  rw [d.attaching_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

attribute [local instance 100] Classical.propDecidable in
/-- The belt basin of the adapted windows. -/
theorem AdaptedWindows.belt_basin_iff {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f) (x : (S.data p).UpperLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val) ↔
      x ∈ Set.range (S.data p).surgery.beltSphere := by
  let d := S.data p
  have hh :=
    MorseCancellation.native_belt_core_basin_iff d.chart hf S.smooth S.flow S.integral d.radius
      d.radius_pos d.block (S.model_germ p) (fun y hy => S.descent y (d.upper_regular y hy))
      x.property
  rw [d.belt_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

attribute [local instance 100] Classical.propDecidable in
/-- The model germ at the critical point. -/
theorem AdaptedWindows.critical_model_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, S.field y = (S.data p).chart.descentField y := by
  let d := S.data p
  have hcenter :
    d.chart.splitChart.symm (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) =
      p.val := by
    rw [← d.chart.splitChart_center]
    exact d.chart.splitChart.left_inv' d.chart.splitChart_mem_source
  have hg :=
    S.model_germ p (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos)),
        Metric.mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos))⟩
  rw [hcenter] at hg
  exact hg

/-! ### The cubic flow cylinder -/

/-- The flow cylinder coordinates of the cubic model. -/
def MorseCancellation.cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (p : (Fin m → ℝ) × ℝ) :
    Model m :=
  (cubicAxisParameter a p.2, fun i => Real.exp (-σ i * p.2) * p.1 i)

/-- The inverse of the cubic flow cylinder. -/
def MorseCancellation.cubicFlowCylinderInverse {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (p : Model m) :
    (Fin m → ℝ) × ℝ :=
  (fun i => Real.exp (σ i * cubicAxisClock a p.1) * p.2 i, cubicAxisClock a p.1)

/-- The cylinder inverse left-inverts the cylinder. -/
theorem MorseCancellation.cubicFlowCylinder_left_inv {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (p : (Fin m → ℝ) × ℝ) : cubicFlowCylinderInverse σ a (cubicFlowCylinder σ a p) = p := by
  apply Prod.ext
  · funext i
    change
      Real.exp (σ i * cubicAxisClock a (cubicAxisParameter a p.2)) *
          (Real.exp (-σ i * p.2) * p.1 i) =
        p.1 i
    rw [cubicAxisClock_parameter ha, ← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel,
      Real.exp_zero, one_mul]
  · exact cubicAxisClock_parameter ha p.2

/-- The cylinder inverse right-inverts the cylinder. -/
theorem MorseCancellation.cubicFlowCylinder_right_inv {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {p : Model m} (hp : p.1 ∈ Set.Ioo (-a) a) :
    cubicFlowCylinder σ a (cubicFlowCylinderInverse σ a p) = p := by
  apply Prod.ext
  · exact cubicAxisParameter_clock ha hp
  · funext i
    change
      Real.exp (-σ i * cubicAxisClock a p.1) * (Real.exp (σ i * cubicAxisClock a p.1) * p.2 i) =
        p.2 i
    rw [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]

/-- The cubic flow cylinder is smooth. -/
theorem MorseCancellation.contDiff_cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    ContDiff ℝ ∞ (cubicFlowCylinder σ a) := by
  apply ((contDiff_cubicAxisParameter a).comp contDiff_snd).prodMk
  apply contDiff_pi.mpr
  intro i
  fun_prop

/-- The cylinder inverse is smooth. -/
theorem MorseCancellation.contDiffOn_cubicFlowCylinderInverse {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) : ContDiffOn ℝ ∞ (cubicFlowCylinderInverse σ a) (Set.Ioo (-a) a ×ˢ Set.univ) := by
  have ht :
    ContDiffOn ℝ ∞ (fun p : Model m => cubicAxisClock a p.1) (Set.Ioo (-a) a ×ˢ Set.univ) :=
    (contDiffOn_cubicAxisClock ha).comp contDiffOn_fst (fun _ hp => hp.1)
  apply ContDiffOn.prodMk ?_ ht
  apply contDiffOn_pi.mpr
  intro i
  exact
    (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul ht)).mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn)

/-- The flow cylinder as a chart. -/
def MorseCancellation.cubicFlowCylinderChart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, Model m) ((Fin m → ℝ) × ℝ) (Model m) ∞
    where
  toFun := cubicFlowCylinder σ a
  invFun := cubicFlowCylinderInverse σ a
  source := Set.univ
  target := Set.Ioo (-a) a ×ˢ Set.univ
  map_source' p _ := ⟨cubicAxisParameter_mem ha p.2, Set.mem_univ _⟩
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := cubicFlowCylinder_left_inv σ ha p
  right_inv' _ hp := cubicFlowCylinder_right_inv σ ha hp.1
  open_source := isOpen_univ
  open_target := isOpen_Ioo.prod isOpen_univ
  contMDiffOn_toFun := (contDiff_cubicFlowCylinder σ a).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiffOn_cubicFlowCylinderInverse σ ha).contMDiffOn

/-- The cylinder's time derivative is the field. -/
theorem MorseCancellation.hasDerivAt_cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ)
    (t : ℝ) :
    HasDerivAt (fun s => cubicFlowCylinder σ a (z, s))
      (cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t))) t := by
  have hz :
    HasDerivAt (fun s => fun i => Real.exp (-σ i * s) * z i)
      (fun i => -σ i * (Real.exp (-σ i * t) * z i)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hd :=
      ((Real.hasDerivAt_exp (-σ i * t)).comp t ((hasDerivAt_id t).const_mul (-σ i))).mul_const
        (z i)
    convert! hd using 1
    first
    | rfl
    | ring
  have hd := (hasDerivAt_cubicAxisParameter a t).prodMk hz
  have he :
    cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t)) =
      (a ^ 2 - cubicAxisParameter a t ^ 2, fun i => -σ i * (Real.exp (-σ i * t) * z i)) := by
    apply Prod.ext
    · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
      ring
    · rfl
  rw [he]
  exact hd

/-- The cylinder on the axis. -/
theorem MorseCancellation.cubicFlowCylinder_axis {m : ℕ} (σ : Fin m → ℝ) (a t : ℝ) :
    cubicFlowCylinder σ a (0, t) = cubicModelOrbit a t := by
  simp only [cubicFlowCylinder, cubicModelOrbit, Pi.zero_apply, MulZeroClass.mul_zero]
  rfl

/-- The cylinder at time zero. -/
theorem MorseCancellation.cubicFlowCylinder_zero_time {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ) :
    cubicFlowCylinder σ a (z, 0) = (0, z) := by
  simp only [cubicFlowCylinder, cubicAxisParameter, MulZeroClass.mul_zero, Real.tanh_zero,
    Real.exp_zero, one_mul]

/-- The cubic axis parameter is monotone. -/
theorem MorseCancellation.monotone_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    Monotone (cubicAxisParameter a) := by
  intro s t hst
  exact
    mul_le_mul_of_nonneg_left (strictMono_tanh.monotone (mul_le_mul_of_nonneg_left hst ha.le))
      ha.le

/-- The cylinder's transverse norm is bounded by the maximum. -/
theorem MorseCancellation.cubicFlowCylinder_transverse_norm_le_max {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    (z : Fin m → ℝ) {s t u : ℝ} (ht : t ∈ Set.Icc s u) :
    ‖(cubicFlowCylinder σ a (z, t)).2‖ ≤
      Max.max ‖(cubicFlowCylinder σ a (z, s)).2‖ ‖(cubicFlowCylinder σ a (z, u)).2‖ := by
  let Z (r : ℝ) : Fin m → ℝ := (cubicFlowCylinder σ a (z, r)).2
  have hcoord (r : ℝ) (i : Fin m) : ‖Z r i‖ = Real.exp (-σ i * r) * ‖z i‖ := by
    change ‖Real.exp (-σ i * r) * z i‖ = _
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg (Z s)))).mpr
  intro i
  change ‖Z t i‖ ≤ Max.max ‖Z s‖ ‖Z u‖
  by_cases hi : 0 ≤ σ i
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * s) * ‖z i‖ :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hi)))
          (norm_nonneg _))
      _ = ‖Z s i‖ := (hcoord s i).symm
      _ ≤ ‖Z s‖ := (norm_le_pi_norm (Z s) i)
      _ ≤ Max.max ‖Z s‖ ‖Z u‖ := le_max_left _ _
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * u) * ‖z i‖ :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left ht.2 (neg_nonneg.mpr (le_of_not_ge hi))))
          (norm_nonneg _))
      _ = ‖Z u i‖ := (hcoord u i).symm
      _ ≤ ‖Z u‖ := (norm_le_pi_norm (Z u) i)
      _ ≤ Max.max ‖Z s‖ ‖Z u‖ := le_max_right _ _

/-- The cylinder stays in the axis ball. -/
theorem MorseCancellation.cubicFlowCylinder_stays_axis_ball {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {s t u c r : ℝ} (ht : t ∈ Set.Icc s u)
    (hs : cubicFlowCylinder σ a (z, s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hu : cubicFlowCylinder σ a (z, u) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hs' : |cubicAxisParameter a s - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, s)).2‖ ≤ r := by
    simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hs
  have hu' : |cubicAxisParameter a u - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, u)).2‖ ≤ r := by
    simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hu
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right]
  constructor
  · change |cubicAxisParameter a t - c| ≤ r
    apply abs_le.mpr
    have hst := monotone_cubicAxisParameter ha ht.1
    have htu := monotone_cubicAxisParameter ha ht.2
    constructor <;> linarith [(abs_le.mp hs'.1).1, (abs_le.mp hu'.1).2]
  · exact (cubicFlowCylinder_transverse_norm_le_max σ a z ht).trans (max_le hs'.2 hu'.2)

/-! ### Fiberwise diffeomorphisms -/

/-- A fiberwise diffeomorphism retaining the parameter. -/
def FiberwiseDiffeomorph.retainParameter {X P : Type*} (F : X × P → X) (p : X × P) :
    X × P :=
  (F p, p.2)

/-- The parameter-retaining map is smooth. -/
theorem FiberwiseDiffeomorph.contMDiff_retainParameter {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {F : X × P → X} (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) :
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) :=
  hF.prodMk contMDiff_snd

/-- The parameter-retaining map is bijective. -/
theorem FiberwiseDiffeomorph.bijective_retainParameter {X P : Type*} {F : X × P → X}
    (hF : ∀ s, Function.Bijective (fun x => F (x, s))) : Function.Bijective (retainParameter F) :=
  by
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    have hst : s = t := congrArg Prod.snd heq
    subst t
    exact Prod.ext ((hF s).1 (congrArg Prod.fst heq)) rfl
  · rintro ⟨y, s⟩
    obtain ⟨x, hx⟩ := (hF s).2 y
    exact ⟨(x, s), Prod.ext hx rfl⟩

/-- The retaining map's derivative. -/
theorem FiberwiseDiffeomorph.mfderiv_retainParameter_apply {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {F : X × P → X} (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) (p : X × P) (v : D × P) :
    mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p v =
      (mfderiv I I (fun x => F (x, p.2)) p.1 v.1 +
          mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2 v.2,
        v.2) := by
  change mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (fun z => (F z, z.2)) p v = _
  rw [mfderiv_prodMk (hF.mdifferentiable (by simp) p) mdifferentiableAt_snd, mfderiv_snd]
  change ((mfderiv (I.prod 𝓘(ℝ, P)) I F p) v, v.2) = _
  exact Prod.ext (mfderiv_prod_eq_add_apply (v := v) (hF.mdifferentiable (by simp) p)) rfl

/-- The retaining map's derivative is invertible. -/
theorem FiberwiseDiffeomorph.isInvertible_mfderiv_retainParameter {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ D] [FiniteDimensional ℝ P] {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) (p : X × P) :
    (mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p).IsInvertible := by
  let A : D →L[ℝ] D := mfderiv I I (fun x => F (x, p.2)) p.1
  let B : P →L[ℝ] D := mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2
  have hA : Function.Bijective A := by
    obtain ⟨d, hd⟩ := hslice p.2
    have heq : (fun x => F (x, p.2)) = d := funext (fun x => (hd x).symm)
    change Function.Bijective (mfderiv I I (fun x => F (x, p.2)) p.1)
    rw [heq]
    exact (d.mfderivToContinuousLinearEquiv (by simp) p.1).bijective
  let L : (D × P) →L[ℝ] (D × P) := mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p
  have hL (v : D × P) : L v = (A v.1 + B v.2, v.2) := mfderiv_retainParameter_apply hF p v
  have hbij : Function.Bijective L := by
    constructor
    · intro u v huv
      have hs : u.2 = v.2 := by simpa only [hL] using congrArg Prod.snd huv
      have hx : A u.1 + B u.2 = A v.1 + B v.2 := by simpa only [hL] using congrArg Prod.fst huv
      rw [hs] at hx
      exact Prod.ext (hA.1 (add_right_cancel hx)) hs
    · intro v
      obtain ⟨x, hx⟩ := hA.2 (v.1 - B v.2)
      refine ⟨(x, v.2), ?_⟩
      rw [hL, hx, sub_add_cancel]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

/-- The fiberwise diffeomorphism. -/
def FiberwiseDiffeomorph.diffeomorph {D H X P : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace H]
    {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ P] [I.Boundaryless] [IsManifold I ∞ X] {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) :
    Diffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (X × P) (X × P) ∞ := by
  have hlocal : IsLocalDiffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) := by
    intro p
    exact
      isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ p)
        (contMDiff_retainParameter hF).contMDiffOn
        (isInvertible_mfderiv_retainParameter hF hslice p)
  apply hlocal.diffeomorphOfBijective
  apply bijective_retainParameter
  intro s
  obtain ⟨d, hd⟩ := hslice s
  have heq : (fun x => F (x, s)) = d := funext (fun x => (hd x).symm)
  rw [heq]
  exact d.bijective

/-- The product of a partial chart with a vector direction. -/
def PartialChart.vectorProduct (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Diffeomorph 𝓘(ℝ, E × F) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (E × F) (E × F) ∞
    where
  toEquiv := Equiv.refl (E × F)
  contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd

/-- The product of two partial charts. -/
def PartialChart.prod {E₁ E₂ F₁ F₂ H₁ H₂ G₁ G₂ X₁ X₂ Y₁ Y₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace H₁]
    [TopologicalSpace H₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {J₁ : ModelWithCorners ℝ F₁ G₁} {J₂ : ModelWithCorners ℝ F₂ G₂} [TopologicalSpace X₁]
    [ChartedSpace H₁ X₁] [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [TopologicalSpace Y₁]
    [ChartedSpace G₁ Y₁] [TopologicalSpace Y₂] [ChartedSpace G₂ Y₂]
    (Φ : PartialDiffeomorph I₁ J₁ X₁ Y₁ ∞) (Ψ : PartialDiffeomorph I₂ J₂ X₂ Y₂ ∞) :
    PartialDiffeomorph (I₁.prod I₂) (J₁.prod J₂) (X₁ × X₂) (Y₁ × Y₂) ∞
    where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.prodMap Ψ.contMDiffOn_toFun
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.prodMap Ψ.contMDiffOn_invFun

/-! ### The suspended flow -/

/-- An isotopy suspends to a diffeomorphism. -/
theorem FlowSuspension.exists_isotopy_suspension_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A : ℝ × E → E}
    (hA : ContDiff ℝ ∞ A)
    (hslice : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (t, x)) :
    ∃ Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞, ∀ p, Ψ p = (A (p.2, p.1), p.2) :=
  by
  have hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun p : E × ℝ => A (p.2, p.1)) :=
    hA.contMDiff.comp (contMDiff_snd.prodMk_space contMDiff_fst)
  let D := FiberwiseDiffeomorph.diffeomorph hF hslice
  let V := PartialChart.vectorProduct E ℝ
  exact ⟨(V.trans D).trans V.symm, fun p => rfl⟩

/-- The suspended flow on the product cylinder. -/
def FlowSuspension.suspensionFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) : Flow ℝ (E × ℝ)
    where
  toFun t p := Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)
  cont' := by
    apply Ψ.continuous.comp
    exact
      (Ψ.symm.continuous.comp continuous_snd).fst.prodMk
        ((Ψ.symm.continuous.comp continuous_snd).snd.add continuous_fst)
  map_zero' p := by simp only [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  map_add' s t
    p := by
    simp only [Ψ.symm_apply_apply]
    congr 1
    apply Prod.ext
    · rfl
    · ring

/-- The suspended flow computes in the chart. -/
theorem FlowSuspension.suspensionFlow_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (t : ℝ)
    (p : E × ℝ) : suspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

/-- The suspended flow's height component. -/
theorem FlowSuspension.suspensionFlow_height {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (t : ℝ) (p : E × ℝ) : (suspensionFlow Ψ t p).2 = p.2 + t := by
  have hinv : (Ψ.symm p).2 = p.2 := by
    have hh := hheight (Ψ.symm p)
    rw [Ψ.apply_symm_apply] at hh
    exact hh.symm
  change (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)).2 = _
  rw [hheight, hinv]

/-- The suspended flow's endpoint. -/
theorem FlowSuspension.suspensionFlow_endpoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : ℝ × E → E} (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (hA0 : ∀ x, A (0, x) = x) (x : E) :
    suspensionFlow Ψ 1 (x, 0) = (A (1, x), 1) := by
  have hstart : Ψ (x, (0 : ℝ)) = (x, 0) := by rw [hΨ, hA0]
  rw [← hstart, suspensionFlow_chart, zero_add, hΨ]

/-- The suspended vector field. -/
def FlowSuspension.suspensionField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) : E × ℝ :=
  fderiv ℝ Ψ (Ψ.symm p) (0, 1)

/-- The suspended field is smooth. -/
theorem FlowSuspension.contDiff_suspensionField {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) :
    ContDiff ℝ ∞ (suspensionField Ψ) := by
  have hΨ : ContDiff ℝ ∞ (Ψ : (E × ℝ) → E × ℝ) := Ψ.contMDiff.contDiff
  have hΨinv : ContDiff ℝ ∞ (Ψ.symm : (E × ℝ) → E × ℝ) := Ψ.symm.contMDiff.contDiff
  exact ((hΨ.fderiv_right (by simp)).comp hΨinv).clm_apply contDiff_const

/-- The suspended flow solves the suspended field. -/
theorem FlowSuspension.hasDerivAt_suspensionFlow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ)
    (t : ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ (suspensionFlow Ψ t p)) t := by
  have hb : HasDerivAt (fun s : ℝ => ((Ψ.symm p).1, (Ψ.symm p).2 + s)) (0, 1) t :=
    (hasDerivAt_const t (Ψ.symm p).1).prodMk ((hasDerivAt_id t).const_add (Ψ.symm p).2)
  have hd :=
    (Ψ.contMDiff.contDiff.differentiable (by simp)
          ((Ψ.symm p).1, (Ψ.symm p).2 + t)).hasFDerivAt.comp_hasDerivAt
      t hb
  change
    HasDerivAt (fun s => Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + s))
      (fderiv ℝ Ψ (Ψ.symm (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t))) (0, 1)) t
  rw [Ψ.symm_apply_apply]
  exact hd

/-- The suspended flow's derivative at zero. -/
theorem FlowSuspension.hasDerivAt_suspensionFlow_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ p) 0 := by
  simpa only [(suspensionFlow Ψ).map_zero_apply] using hasDerivAt_suspensionFlow Ψ p 0

/-- The suspended field's height component is one. -/
theorem FlowSuspension.suspensionField_height {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : E × ℝ) : (suspensionField Ψ p).2 = 1 := by
  have hd : HasDerivAt (fun t => (suspensionFlow Ψ t p).2) (suspensionField Ψ p).2 0 :=
    (hasDerivAt_suspensionFlow_zero Ψ p).snd
  have heq : (fun t => (suspensionFlow Ψ t p).2) = fun t => p.2 + t :=
    funext (fun t => suspensionFlow_height Ψ hheight t p)
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_id (0 : ℝ)).const_add p.2)

/-- The suspended field is vertical where the isotopy is stationary. -/
theorem FlowSuspension.suspensionField_eq_vertical_of_stationary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (p : E × ℝ)
    (hstationary : ∀ᶠ s in 𝓝 p.2, ∀ x, A (s, x) = A (p.2, x)) : suspensionField Ψ p = (0, 1) := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have hqheight : q.2 = p.2 := by
    have hh := congrArg Prod.snd hq
    rw [hΨ] at hh
    exact hh
  have hqfirst : A (p.2, q.1) = p.1 := by
    have hh := congrArg Prod.fst hq
    rw [hΨ] at hh
    change A (q.2, q.1) = p.1 at hh
    rwa [hqheight] at hh
  have ht : Filter.Tendsto (fun t : ℝ => p.2 + t) (𝓝 0) (𝓝 p.2) := by
    have hc : Continuous (fun t : ℝ => p.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq : (fun t => suspensionFlow Ψ t p) =ᶠ[𝓝 0] (fun t => (p.1, p.2 + t)) := by
    filter_upwards [ht.eventually hstationary] with t hts
    change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
    rw [hΨ, hqheight, hts q.1, hqfirst]
  have hv : HasDerivAt (fun t : ℝ => (p.1, p.2 + t)) (0, 1) 0 :=
    (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2)
  exact ((hasDerivAt_suspensionFlow_zero Ψ p).congr_of_eventuallyEq heq.symm).unique hv

/-- The suspended flow is vertical off the support. -/
theorem FlowSuspension.suspensionFlow_vertical_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    {p : E × ℝ} (hp : p.1 ∉ K) (t : ℝ) : suspensionFlow Ψ t p = (p.1, p.2 + t) := by
  have hΨp : Ψ p = p := by rw [hΨ, hfix _ _ hp]
  have hinv : Ψ.symm p = p := by
    have hh := Ψ.symm_apply_apply p
    rwa [hΨp] at hh
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = _
  rw [hinv, hΨ, hfix _ _ hp]

/-- The suspended field is vertical off the support. -/
theorem FlowSuspension.suspensionField_eq_vertical_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    {p : E × ℝ} (hp : p.1 ∉ K) : suspensionField Ψ p = (0, 1) := by
  have heq : (fun t => suspensionFlow Ψ t p) = fun t => (p.1, p.2 + t) :=
    funext (fun t => suspensionFlow_vertical_off_support Ψ hΨ hfix hp t)
  have hd := hasDerivAt_suspensionFlow_zero Ψ p
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2))

/-- The suspended field minus the vertical field has compact support. -/
theorem FlowSuspension.hasCompactSupport_suspensionField_sub_vertical {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hK : IsCompact K)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {a b : ℝ}
    (hstationary : ∀ s ∉ Set.Icc a b, ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x)) :
    HasCompactSupport (fun p => suspensionField Ψ p - (0, 1)) := by
  apply
    HasCompactSupport.intro (hK.prod (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc a b)))
  intro p hp
  have hv : suspensionField Ψ p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Set.Icc a b := fun h => hp ⟨hx, h⟩
      exact suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary _ ht)
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  rw [hv, sub_self]

/-! ### Supported isotopies -/

/-- The extended family of diffeomorphisms is smooth. -/
theorem SupportedDiffeomorph.contMDiff_extendFamily {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    (hsource : ∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun p : ℝ × Y => extendMap Φ (fun x => A (p.1, x)) p.2) := by
  intro p
  by_cases hp : p.2 ∈ Φ.target
  · have hback :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource p.1 (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

/-- The extended family is smooth at a point. -/
theorem SupportedDiffeomorph.contMDiffAt_extendFamily {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : P × X → X} (hA : ContMDiff (𝓘(ℝ, P).prod I) I ∞ A) {K : Set X} (hK : IsCompact K)
    (hKΦ : K ⊆ Φ.source) (hfix : ∀ t x, x ∉ K → A (t, x) = x) {p : P × Y}
    (hsource : Set.MapsTo (fun x => A (p.1, x)) Φ.source Φ.source) :
    ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ (fun q : P × Y => extendMap Φ (fun x => A (q.1, x)) q.2) p :=
  by
  by_cases hp : p.2 ∈ Φ.target
  · have hback :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

/-- The bump family of supported diffeomorphisms. -/
def SupportedDiffeomorph.bumpFamily {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (p : E × M) : M :=
  extendMap Φ (fun x => x + β x • p.1) p.2

/-- The bump family at parameter zero is the identity. -/
theorem SupportedDiffeomorph.bumpFamily_zero {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (y : M) : bumpFamily Φ β (0, y) = y := by
  have heq : (fun x : E => x + β x • (0 : E)) = id := by funext x; simp
  change extendMap Φ (fun x => x + β x • (0 : E)) y = y
  rw [heq]
  exact extendMap_id Φ y

/-- The bump family computes in the chart. -/
theorem SupportedDiffeomorph.bumpFamily_chart {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E) {x : E} (hx : x ∈ Φ.source) :
    bumpFamily Φ β (a, Φ x) = Φ (x + β x • a) :=
  extendMap_chart Φ _ hx

/-- The bump family lands in the target. -/
theorem SupportedDiffeomorph.bumpFamily_mem_target {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E)
    (hsource : Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source) {y : M} (hy : y ∈ Φ.target) :
    bumpFamily Φ β (a, y) ∈ Φ.target :=
  extendMap_mem_target Φ hsource hy

/-- The bump family in coordinates. -/
theorem SupportedDiffeomorph.bumpFamily_coordinates {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E)
    (hsource : Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source) {y : M} (hy : y ∈ Φ.target) :
    Φ.symm (bumpFamily Φ β (a, y)) = Φ.symm y + β (Φ.symm y) • a := by
  change Φ.symm (extendMap Φ (fun x => x + β x • a) y) = _
  rw [extendMap_of_mem Φ _ hy]
  exact Φ.left_inv' (hsource (Φ.map_target' hy))

/-- The bump family is fixed outside the support. -/
theorem SupportedDiffeomorph.bumpFamily_fixed_outside {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E) {y : M}
    (hy : y ∉ Φ '' tsupport β) : bumpFamily Φ β (a, y) = y := by
  apply extendMap_eq_of_notMem_image Φ (K := tsupport β) _ hy
  intro x hx
  have hzero : β x = 0 := by
    by_contra hn
    exact hx (subset_tsupport β hn)
  simp only [hzero, zero_smul, add_zero]

/-- A radius for the ambient bump family exists. -/
theorem SupportedDiffeomorph.exists_radius_ambient_bumpFamily {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) [FiniteDimensional ℝ E] [T2Space M] {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        (∀ a : E, ‖a‖ < ε → ∃ D : Diffeomorph J J M M ∞, ∀ y, D y = bumpFamily Φ β (a, y)) ∧
          (∀ p : E × M, ‖p.1‖ < ε → ContMDiffAt (𝓘(ℝ, E).prod J) J ∞ (bumpFamily Φ β) p) ∧
            ∀ a : E, ‖a‖ < ε → Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source := by
  obtain ⟨ε, hε, hsmall⟩ := SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let A : E × E → E := fun p => p.2 + β p.2 • p.1
  have hA : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hβ.contMDiff.comp contMDiff_snd).smul contMDiff_fst)
  have hfix : ∀ a x, x ∉ tsupport β → A (a, x) = x := by
    intro a x hx
    have hzero : β x = 0 := by
      by_contra hn
      exact hx (subset_tsupport β hn)
    simp only [A, hzero, zero_smul, add_zero]
  have hsource (a : E) (ha : ‖a‖ < ε) : Set.MapsTo (fun x => A (a, x)) Φ.source Φ.source := by
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    have heq : (fun x => A (a, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  refine ⟨ε, hε, ?_, ?_, hsource⟩
  · intro a ha
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ d y = extendMap Φ (fun x => x + β x • a) y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext hd)
  · intro p hp
    exact contMDiffAt_extendFamily Φ hA hcompact.isCompact hsupport hfix (hsource p.1 hp)

/-- The bump family eventually maps a compact set into an open set. -/
theorem SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) [FiniteDimensional ℝ E] [T2Space M] {X : Type*}
    [TopologicalSpace X] {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) {f : X → M} (hf : Continuous f) {C : Set X}
    (hC : IsCompact C) {O : Set M} (hO : IsOpen O) (hmap : Set.MapsTo f C O) :
    ∀ᶠ a in 𝓝 (0 : E), Set.MapsTo (fun x => bumpFamily Φ β (a, f x)) C O := by
  obtain ⟨δ, hδ, -, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  apply hC.eventually_forall_of_forall_eventually
  intro x hx
  have hpair : ContinuousAt (fun p : E × X => (p.1, f p.2)) (0, x) :=
    (continuous_fst.prodMk (hf.comp continuous_snd)).continuousAt
  have hbase : ContinuousAt (bumpFamily Φ β) (0, f x) :=
    (hsmooth (0, f x) (by simpa only [norm_zero] using hδ)).continuousAt
  have hfamily : ContinuousAt (fun p : E × X => bumpFamily Φ β (p.1, f p.2)) (0, x) :=
    ContinuousAt.comp (g := bumpFamily Φ β) (f := fun p : E × X => (p.1, f p.2)) hbase hpair
  apply hfamily.preimage_mem_nhds
  apply hO.mem_nhds
  rw [bumpFamily_zero]
  exact hmap hx

/-- A small supported bump isotopy exists. -/
theorem SupportedDiffeomorph.exists_small_supported_bump_isotopy {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ Φ '' tsupport β → A (t, y) = y) ∧
                      ∀ x ∈ Φ.source, A (1, Φ x) = Φ (x + β x • a) := by
  obtain ⟨ε, hε, hsmall⟩ := SmallPerturbation.exists_radius_bumpTranslation hs hcompact
  refine ⟨ε, hε, ?_⟩
  intro a ha
  let B : ℝ × E → E := fun p => p.2 + β p.2 • (Real.smoothTransition p.1 • a)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ B :=
    contMDiff_snd.add
      ((hs.contMDiff.comp contMDiff_snd).smul ((hθ.comp contMDiff_fst).smul contMDiff_const))
  have hmodel :
    ∀ t : ℝ,
      ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ x, d x = B (t, x)) ∧ ∀ x ∉ tsupport β, d x = x := by
    intro t
    have hnorm : ‖Real.smoothTransition t • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact mul_le_of_le_one_left (norm_nonneg a) (Real.smoothTransition.le_one t)
    exact hsmall (Real.smoothTransition t • a) (hnorm.trans_lt ha)
  have hfix : ∀ t x, x ∉ tsupport β → B (t, x) = x := by
    intro t x hx
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    exact (hd x).symm.trans (hdfix x hx)
  have hsource : ∀ t, Set.MapsTo (fun x => B (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    have heq : (fun x => B (t, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  let A : ℝ × M → M := fun p => extendMap Φ (fun x => B (p.1, x)) p.2
  refine ⟨A, contMDiff_extendFamily Φ hB hcompact.isCompact hsupport hfix hsource, ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun x => B (0, x)) = id := by
      funext x
      simp only [B, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero, id_eq]
    change extendMap Φ (fun x => B (0, x)) y = y
    rw [hzero]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ (fun x => B (t, x)) y = extendMap Φ d y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext (fun x => (hd x).symm))
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro x hx
    change extendMap Φ (fun y => B (1, y)) (Φ x) = _
    rw [extendMap_chart Φ (fun y => B (1, y)) hx]
    simp only [B, Real.smoothTransition.one, one_smul]

/-- A diffeomorphism isotopic to the identity through supported diffeomorphisms. -/
def SupportedDiffeomorph.IsotopicToIdentity {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (e : Diffeomorph J J M M ∞) : Prop :=
  ∃ A : ℝ × M → M,
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
      (∀ y, A (0, y) = y) ∧
        (∀ y, A (1, y) = e y) ∧ ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y

/-- The identity is isotopic to itself. -/
theorem SupportedDiffeomorph.isotopicToIdentity_refl {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] : IsotopicToIdentity (Diffeomorph.refl J M ∞) := by
  refine ⟨Prod.snd, contMDiff_snd, fun _ => rfl, fun _ => rfl, ?_⟩
  exact fun _ => ⟨Diffeomorph.refl J M ∞, fun _ => rfl⟩

/-- Isotopy to the identity is transitive. -/
theorem SupportedDiffeomorph.IsotopicToIdentity.trans {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e d : Diffeomorph J J M M ∞}
    (he : SupportedDiffeomorph.IsotopicToIdentity e)
    (hd : SupportedDiffeomorph.IsotopicToIdentity d) :
    SupportedDiffeomorph.IsotopicToIdentity (e.trans d) := by
  obtain ⟨A, hA, hA₀, hA₁, hAd⟩ := he
  obtain ⟨B, hB, hB₀, hB₁, hBd⟩ := hd
  refine ⟨fun p => B (p.1, A p), hB.comp (contMDiff_fst.prodMk hA), ?_, ?_, ?_⟩
  · intro y
    change B (0, A (0, y)) = y
    rw [hA₀, hB₀]
  · intro y
    change B (1, A (1, y)) = d (e y)
    rw [hA₁, hB₁]
  · intro t
    obtain ⟨e', he'⟩ := hAd t
    obtain ⟨d', hd'⟩ := hBd t
    refine ⟨e'.trans d', ?_⟩
    intro y
    change B (t, A (t, y)) = d' (e' y)
    rw [he', hd']

/-- A radius on which the bump family is an isotopy exists. -/
theorem SupportedDiffeomorph.exists_radius_bumpFamily_isotopy {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∀ e : Diffeomorph J J M M ∞,
              (∀ y, e y = bumpFamily Φ β (a, y)) → IsotopicToIdentity e := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  refine ⟨A, hA, hzero, ?_, hdiff⟩
  intro y
  rw [he]
  by_cases hy : y ∈ Φ.target
  · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
    have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
    rw [hpoint] at hh
    change A (1, y) = extendMap Φ (fun x => x + β x • a) y
    rw [extendMap_of_mem Φ _ hy]
    exact hh
  · have hnot : y ∉ Φ '' tsupport β := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hsupport hx))
    rw [hfix 1 y hnot, bumpFamily_fixed_outside Φ β a hnot]

/-- A supported isotopy fixed on a prescribed set. -/
structure SupportedDiffeomorph.SupportedRelativeIsotopy {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (e : Diffeomorph J J M M ∞) (K S : Set M) where
  family : ℝ × M → M
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ x, family (0, x) = x
  one : ∀ x, family (1, x) = e x
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ x, d x = family (t, x)
  fixedOutside : ∀ t x, x ∉ K → family (t, x) = x
  fixedOn : ∀ t x, x ∈ S → family (t, x) = x

/-- A supported relative isotopy's endpoint is isotopic to the identity. -/
theorem SupportedDiffeomorph.SupportedRelativeIsotopy.isotopicToIdentity {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S) :
    SupportedDiffeomorph.IsotopicToIdentity e := by
  refine ⟨A.family, A.smooth, A.zero, A.one, ?_⟩
  intro t
  obtain ⟨d, hd⟩ := A.slices t
  exact ⟨d, fun x => (hd x).symm⟩

/-- The isotopy endpoint is fixed outside the support. -/
theorem SupportedDiffeomorph.SupportedRelativeIsotopy.endpoint_fixed_outside {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S) (x : M) (hx : x ∉ K) :
    e x = x :=
  (A.one x).symm.trans (A.fixedOutside 1 x hx)

/-- The isotopy endpoint is fixed on the prescribed set. -/
theorem SupportedDiffeomorph.SupportedRelativeIsotopy.endpoint_fixed_on {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S) (x : M) (hx : x ∈ S) :
    e x = x :=
  (A.one x).symm.trans (A.fixedOn 1 x hx)

/-! ### Suspension coordinates -/

/-- Coordinates for the suspended flow. -/
structure FlowSuspension.SuspensionCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E) (W : (E × ℝ) → E × ℝ)
    (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = suspensionField chart
  flow_eq : F = suspensionFlow chart
  height : ∀ p, (chart p).2 = p.2
  base_iff : ∀ U : Set E, K ⊆ U → ∀ p, (chart p).1 ∈ U ↔ p.1 ∈ U
  lower : ∀ p, p.2 ≤ 0 → chart p = p
  upper : ∀ p, 1 ≤ p.2 → chart p = (D p.1, p.2)

/-- A compactly supported isotopy suspends. -/
theorem FlowSuspension.exists_compact_isotopy_suspension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {K S : Set E} (hK : IsCompact K)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)),
      ContDiff ℝ ∞ W ∧
        (∀ p, (W p).2 = 1) ∧
          HasCompactSupport (fun p => W p - (0, 1)) ∧
            tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) ∧
              (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
                (∀ x, F 1 (x, 0) = (D x, 1)) ∧
                  (∀ t p, (F t p).2 = p.2 + t) ∧
                    (∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
                      (∀ x ∈ S, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
                        Nonempty (SuspensionCoordinates D K W F) := by
  let τ : ℝ → ℝ := fun s => Real.smoothTransition (3 * s - 1)
  have hτ : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hτlower (s : ℝ) (hs : s ≤ 1 / 3) : τ s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hτupper (s : ℝ) (hs : 2 / 3 ≤ s) : τ s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  let A : ℝ × E → E := fun p => I.family (τ p.1, p.2)
  have hInorm : ContDiff ℝ ∞ I.family :=
    (I.smooth.comp (PartialChart.vectorProduct ℝ E).contMDiff).contDiff
  have hA : ContDiff ℝ ∞ A := hInorm.comp ((hτ.comp contDiff_fst).prodMk contDiff_snd)
  have hslice (s : ℝ) : ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (s, x) :=
    I.slices (τ s)
  have hA0 (x : E) : A (0, x) = x := by
    change I.family (τ 0, x) = x
    rw [hτlower 0 (by norm_num)]
    exact I.zero x
  have hA1 (x : E) : A (1, x) = D x := by
    change I.family (τ 1, x) = D x
    rw [hτupper 1 (by norm_num)]
    exact I.one x
  have hfix (s : ℝ) (x : E) (hx : x ∉ K) : A (s, x) = x := I.fixedOutside (τ s) x hx
  have hstationary (s : ℝ) (hs : s ∉ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x) := by
    by_cases hlo : s < 1 / 3
    · filter_upwards [eventually_lt_nhds hlo] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτlower r hr.le, hτlower s hlo.le]
    · have hhi : 2 / 3 < s := lt_of_not_ge (fun h => hs ⟨le_of_not_gt hlo, h⟩)
      filter_upwards [eventually_gt_nhds hhi] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτupper r hr.le, hτupper s hhi.le]
  obtain ⟨Ψ, hΨ⟩ := exists_isotopy_suspension_diffeomorph hA hslice
  let W := suspensionField Ψ
  let F := suspensionFlow Ψ
  have hvertical (p : E × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) : W p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · exact
        suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary p.2 (fun h => hp ⟨hx, h⟩))
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  have hsupp : tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_Icc)
    intro p hp
    by_contra hout
    apply hp
    change W p - (0, 1) = 0
    rw [hvertical p hout, sub_self]
  have hcoords : SuspensionCoordinates D K W F := by
    refine ⟨Ψ, rfl, rfl, fun p => by rw [hΨ], ?_, ?_, ?_⟩
    · intro U hKU p
      have hfixU (z : E × ℝ) (hz : z ∉ U ×ˢ Set.univ) : Ψ z = z := by
        have hn : z.1 ∉ K := fun h => hz ⟨hKU h, Set.mem_univ _⟩
        rw [hΨ, hfix z.2 z.1 hn]
      have hmaps := SupportedDiffeomorph.mapsTo_of_fixed_outside Ψ.toEquiv hfixU
      have hmapsInv :=
        SupportedDiffeomorph.mapsTo_of_fixed_outside Ψ.symm.toEquiv
          (SupportedDiffeomorph.inverse_fixed_outside Ψ.toEquiv hfixU)
      constructor
      · intro hp
        have hh := hmapsInv ⟨hp, Set.mem_univ (Ψ p).2⟩
        have hh' : (Ψ.symm (Ψ p)).1 ∈ U := hh.1
        simpa only [Ψ.symm_apply_apply] using hh'
      · intro hp
        exact (hmaps ⟨hp, Set.mem_univ p.2⟩).1
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = p
      rw [hτlower p.2 (by linarith), I.zero]
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = (D p.1, p.2)
      rw [hτupper p.2 (by linarith), I.one]
  refine
    ⟨W, F, contDiff_suspensionField Ψ, suspensionField_height Ψ (fun p => by rw [hΨ]),
      hasCompactSupport_suspensionField_sub_vertical Ψ hΨ hK hfix hstationary, hsupp,
      hasDerivAt_suspensionFlow Ψ, ?_, suspensionFlow_height Ψ (fun p => by rw [hΨ]), ?_, ?_,
      ⟨hcoords⟩⟩
  · intro x
    exact
      (suspensionFlow_endpoint Ψ hΨ hA0 x).trans (congrArg (fun y : E => (y, (1 : ℝ))) (hA1 x))
  · intro x hx s t
    exact suspensionFlow_vertical_off_support Ψ hΨ hfix (p := (x, s)) hx t
  · intro x hx s t
    have hΨfix (r : ℝ) : Ψ (x, r) = (x, r) := by
      rw [hΨ]
      change (I.family (τ r, x), r) = (x, r)
      rw [I.fixedOn (τ r) x hx]
    change suspensionFlow Ψ t (x, s) = (x, s + t)
    rw [← hΨfix s, suspensionFlow_chart, hΨfix]

/-! ### Local field replacement -/

/-- A vector field replaced by a model on a chart. -/
def LocalFieldReplacement.replace {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : M) : TangentSpace 𝓘(ℝ, E) x := by
  classical exact if x ∈ Φ.target then W x else V x

/-- The field replacement computes the model inside the chart. -/
theorem LocalFieldReplacement.replace_of_mem {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) {x : M} (hx : x ∈ Φ.target) :
    replace Φ V W x = W x := by simp [replace, hx]

/-- The field replacement is the original off the chart. -/
theorem LocalFieldReplacement.replace_of_notMem {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) {x : M} (hx : x ∉ Φ.target) :
    replace Φ V W x = V x := by simp [replace, hx]

/-- A smooth field replacement exists. -/
theorem LocalFieldReplacement.exists_smooth_field_replacement {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞) [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
        Φ.target)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∈ Φ.target, x ∉ Φ '' K → W x = V x) (hreg : ∀ x ∈ Φ.target, W x ≠ 0) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Φ.target, V' x = W x) ∧
          (∀ x, V' x = 0 ↔ V x = 0 ∧ x ∉ Φ.target) ∧ ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let V' := replace Φ V W
  have hclosed : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  have hoff (x : M) (hx : x ∉ Φ '' K) : ∀ᶠ y in 𝓝 x, V' y = V y := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    by_cases hyt : y ∈ Φ.target
    · exact (replace_of_mem Φ V W hyt).trans (hfix y hyt hy)
    · exact replace_of_notMem Φ V W hyt
  have hsmooth :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    intro x
    by_cases hx : x ∈ Φ.target
    · apply (hW.contMDiffAt (Φ.open_target.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hx] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) (replace_of_mem Φ V W hy)
    · have hnot : x ∉ Φ '' K := by
        rintro ⟨p, hp, rfl⟩
        exact hx (Φ.map_source' (hKΦ hp))
      apply hV.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [hoff x hnot] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) hy
  refine ⟨V', hsmooth, fun x hx => replace_of_mem Φ V W hx, ?_, hoff⟩
  intro x
  by_cases hx : x ∈ Φ.target
  · rw [show V' x = W x from replace_of_mem Φ V W hx]
    simp only [hreg x hx, hx, not_true_eq_false, and_false]
  · rw [show V' x = V x from replace_of_notMem Φ V W hx]
    simp only [hx, not_false_eq_true, and_true]

/-- A compactly supported smooth cutoff exists. -/
theorem exists_compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : E → ℝ,
      ContDiff ℝ ∞ η ∧
        HasCompactSupport η ∧
          tsupport η ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, η x = 1) ∧ ∀ x, η x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKL (n := ⊤)
  have hsupp : tsupport (η : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx (hηzero x hxL)
  exact
    ⟨η, η.contMDiff.contDiff, HasCompactSupport.intro hL hηzero, hsupp.trans hLU, hηone, hηrange⟩

/-! ### The cancelled descent field -/

/-- The native flow's segment endpoints. -/
theorem FlowSuspension.native_flow_segment_endpoints {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hγcont : ContinuousOn γ (Set.Icc a b))
    (hγ : IsMIntegralCurveOn γ V (Set.Ioo a b)) : F (b - a) (γ a) = γ b := by
  let c := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by constructor <;> dsimp [c] <;> linarith
  have hη : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have hh := (hcurve (γ c)).comp_add (-c)
    simpa only [sub_eq_add_neg, Function.comp_def] using hh
  have heq : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ (hη.isMIntegralCurveOn _)
      (by simp)
  have heqclosed : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Icc a b) :=
    heq.of_subset_closure hγcont hη.continuous.continuousOn Set.Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have ha := heqclosed (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
  have hb := heqclosed (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩)
  change γ a = F (a - c) (γ c) at ha
  change γ b = F (b - c) (γ c) at hb
  rw [ha, ← F.map_add, show b - a + (a - c) = b - c by ring, ← hb]

/-! ### Basin-preserving endpoint clocks -/

/-- The forward flow-time limit characterization. -/
theorem MorseCancellation.flow_time_atTop_limit_iff {M : Type*} [TopologicalSpace M] (F : Flow ℝ M)
    (d : ℝ) (x p : M) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atTop (𝓝 p) ↔
      Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) := by
  have hshift {x p : M} (d : ℝ) (h : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atTop (𝓝 p) := by
    simpa only [Function.comp_def, id_eq, F.map_add] using
      h.comp (Filter.tendsto_atTop_add_const_right Filter.atTop d Filter.tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

/-- The backward flow-time limit characterization. -/
theorem MorseCancellation.flow_time_atBot_limit_iff {M : Type*} [TopologicalSpace M] (F : Flow ℝ M)
    (d : ℝ) (x p : M) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atBot (𝓝 p) ↔
      Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  have hshift {x p : M} (d : ℝ) (h : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atBot (𝓝 p) := by
    simpa only [Function.comp_def, id_eq, F.map_add] using
      h.comp (Filter.tendsto_atBot_add_const_right Filter.atBot d Filter.tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

/-! ### Nowhere-dense critical pieces -/

attribute [local instance 100] Classical.propDecidable in
/-- A Morse coordinate neighborhood. -/
theorem MorseCancellation.morse_coordinate_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source ∧ ‖(c.splitChart x).1‖ < a ∧ ‖(c.splitChart x).2‖ < b := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hn : ‖(c.splitChart p).1‖ < a := by
    simpa only [c.splitChart_center, Prod.fst_zero, norm_zero] using ha
  have hp : ‖(c.splitChart p).2‖ < b := by
    simpa only [c.splitChart_center, Prod.snd_zero, norm_zero] using hb
  have hs : ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hna : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).1‖ < a := hc.fst.norm (eventually_lt_nhds hn)
  have hpb : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).2‖ < b := hc.snd.norm (eventually_lt_nhds hp)
  exact hs.and (hna.and hpb)

/-! ### Quadratic germs and surviving critical points -/

/-- The derivative of a quadratic germ. -/
theorem MorseCancellation.quadratic_germ_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (Q : QuadraticForm ℝ A)
    (R : QuadraticForm ℝ B) (hR : Continuous R) {F : A → B} {L : A →L[ℝ] B}
    (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0) (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) (v : A) :
    R (L v) = Q v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hcurve : HasDerivAt (fun t : ℝ => F (t • v)) (L v) 0 :=
    hF.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ • F (t • v)) (𝓝[≠] 0) (𝓝 (L v)) := by
    simpa only [zero_add, zero_smul, hF0, sub_zero] using hcurve.tendsto_slope_zero
  have hpath : Filter.Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 (0 : A)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => R (t⁻¹ • F (t • v))) =ᶠ[𝓝[≠] 0] fun _ => Q v := by
    filter_upwards [hquad.comp_tendsto hpath, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    change R (F (t • v)) = Q (t • v) at ht
    rw [R.map_smul, ht, Q.map_smul]
    simp only [smul_eq_mul]
    field_simp
  exact
    tendsto_nhds_unique (hR.continuousAt.tendsto.comp hslope)
      ((Filter.tendsto_congr' heq).mpr tendsto_const_nhds)

/-- Bijective derivative gives equivalent quadratic germs. -/
theorem MorseCancellation.equivalent_quadratic_germs_of_bijective_derivative {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : QuadraticForm ℝ A) (R : QuadraticForm ℝ B) (hR : Continuous R) {F : A → B}
    {L : A →L[ℝ] B} (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0) (hL : Function.Bijective L)
    (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) : Q.Equivalent R := by
  let e := LinearEquiv.ofBijective L.toLinearMap hL
  exact ⟨{ e with map_app' := quadratic_germ_derivative Q R hR hF hF0 hquad }⟩

/-- Signed Morse charts of equivalent germs are equivalent. -/
theorem MorseCancellation.signed_morse_chart_quadratic_equivalent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : ManifoldMorse.SignedMorseChart (E := E) f p) :
    (QuadraticMap.weightedSumSquares ℝ c.weights).Equivalent
      (QuadraticMap.weightedSumSquares ℝ d.weights) := by
  let Z := Fin (Module.finrank ℝ E) → ℝ
  let Q : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ c.weights
  let R : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ d.weights
  have hQ (z : Z) : Q z = ∑ i, c.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) c.weights z)
  have hR (z : Z) : R z = ∑ i, d.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) d.weights z)
  have hRcont : Continuous R := by
    change Continuous (fun z : Z => R z)
    simp_rw [hR]
    fun_prop
  let P := c.chart.symm.trans d.chart
  have hc0 : c.chart.symm (0 : Z) = p := by
    rw [← c.center]
    exact c.chart.left_inv' c.mem_source
  have h0 : (0 : Z) ∈ P.source := by
    refine ⟨?_, ?_⟩
    · rw [← c.center]
      exact c.chart.map_source' c.mem_source
    · change c.chart.symm (0 : Z) ∈ d.chart.source
      rw [hc0]
      exact d.mem_source
  have hP0 : P (0 : Z) = 0 := by
    change d.chart (c.chart.symm (0 : Z)) = 0
    rw [hc0, d.center]
  have hdiff := (P.mdifferentiableAt (by simp) h0).differentiableAt
  have hbij : Function.Bijective (fderiv ℝ P (0 : Z)) := by
    have hh := PartialChart.bijective_mfderiv P h0
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hquad : (fun z => R (P z)) =ᶠ[𝓝 (0 : Z)] Q := by
    filter_upwards [P.open_source.mem_nhds h0] with z hz
    have hzs : z ∈ c.chart.target ∧ c.chart.symm z ∈ d.chart.source := hz
    rw [hR, hQ]
    change (∑ i, d.weights i * (d.chart (c.chart.symm z) i) ^ 2) = ∑ i, c.weights i * (z i) ^ 2
    linarith [c.inverse_equation z hzs.1, d.equation (c.chart.symm z) hzs.2]
  exact
    equivalent_quadratic_germs_of_bijective_derivative Q R hRcont hdiff.hasFDerivAt hP0 hbij hquad

attribute [local instance 100] Classical.propDecidable in
/-- The negative cardinality is chart independent. -/
theorem MorseCancellation.signed_morse_chart_negative_card_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : ManifoldMorse.SignedMorseChart (E := E) f p) :
    Fintype.card { i // c.weights i = -1 } = Fintype.card { i // d.weights i = -1 } := by
  have hs := (signed_morse_chart_quadratic_equivalent c d).sigNeg_eq
  rw [QuadraticForm.sigNeg_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares] at hs
  have hc : {i | c.weights i < 0} = {i | c.weights i = -1} := by
    ext i
    rcases c.signs i with h | h <;> norm_num [h]
  have hd : {i | d.weights i < 0} = {i | d.weights i = -1} := by
    ext i
    rcases d.signs i with h | h <;> norm_num [h]
  rw [hc, hd] at hs
  calc
    Fintype.card { i // c.weights i = -1 } = {i | c.weights i = -1}.ncard :=
      Set.fintypeCard_eq_ncard _
    _ = {i | d.weights i = -1}.ncard := hs
    _ = Fintype.card { i // d.weights i = -1 } := (Set.fintypeCard_eq_ncard _).symm

attribute [local instance 100] Classical.propDecidable in
/-- The negative rank is chart independent. -/
theorem MorseCancellation.signed_morse_chart_negative_finrank_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    MorseHandle.NegativeSpace, finrank_euclideanSpace] using
    signed_morse_chart_negative_card_eq c d

/-! ### The native Morse index -/

attribute [local instance 100] Classical.propDecidable in
/-- The native Morse index of a critical point. -/
def MorseCancellation.nativeMorseIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : ℕ :=
  if h : Nonempty (ManifoldMorse.SignedMorseChart (E := E) f p) then
    Module.finrank ℝ (Classical.choice h).NegativeCoordinates
  else 0

attribute [local instance 100] Classical.propDecidable in
/-- The native index equals the chart's negative rank. -/
theorem MorseCancellation.nativeMorseIndex_eq_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E f p = Module.finrank ℝ c.NegativeCoordinates := by
  unfold nativeMorseIndex
  rw [dif_pos ⟨c⟩]
  exact signed_morse_chart_negative_finrank_eq _ c

/-! ### Omega limits and connections -/

/-- Points in the omega limit have equal height. -/
theorem FlowCancellation.height_eq_of_mem_omegaLimit {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {κ : Filter ℝ} {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) {y : X}
    (hy : y ∈ omegaLimit κ F { x }) : f y = l := by
  have hc : MapClusterPt y κ (fun t => F t x) :=
    (mem_omegaLimit_singleton_iff_mapClusterPt κ F x y).mp hy
  have hh := hc.continuousAt_comp hf.continuousAt
  have hl : Filter.map (f ∘ (fun t => F t x)) κ ≤ 𝓝 l := hlim
  exact eq_of_nhds_neBot (hh.clusterPt.mono hl)

/-- The omega limit lies below a strict height bound. -/
theorem FlowCancellation.omegaLimit_subset_of_strict_height {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {κ : Filter ℝ}
    (hshift : ∀ t : ℝ, Filter.Tendsto (t + ·) κ κ) {S : Set X}
    (hstrict : ∀ y ∉ S, f (F 1 y) < f y) {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) : omegaLimit κ F { x } ⊆ S := by
  intro y hy
  by_contra hnot
  have hy' : F 1 y ∈ omegaLimit κ F { x } := (F.isInvariant_omegaLimit κ { x } hshift) 1 hy
  have h0 := height_eq_of_mem_omegaLimit F hf hlim hy
  have h1 := height_eq_of_mem_omegaLimit F hf hlim hy'
  have hs := hstrict y hnot
  rw [h0, h1] at hs
  exact lt_irrefl _ hs

/-- A flow limit exists given injective exceptional height. -/
theorem FlowCancellation.exists_flow_limit_of_injective_exceptional_height {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {κ : Filter ℝ} [Filter.NeBot κ] (hshift : ∀ t : ℝ, Filter.Tendsto (t + ·) κ κ) {S : Set X}
    (hstrict : ∀ y ∉ S, f (F 1 y) < f y) (hinj : Set.InjOn f S) {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) :
    ∃ p ∈ S, f p = l ∧ Filter.Tendsto (fun t : ℝ => F t x) κ (𝓝 p) := by
  have hsub := omegaLimit_subset_of_strict_height F hf hshift hstrict hlim
  obtain ⟨p, hp⟩ := nonempty_omegaLimit κ F { x } (Set.singleton_nonempty x)
  have hpl := height_eq_of_mem_omegaLimit F hf hlim hp
  have hsingle : omegaLimit κ F { x } ⊆ { p } := by
    intro y hy
    exact hinj (hsub hy) (hsub hp) ((height_eq_of_mem_omegaLimit F hf hlim hy).trans hpl.symm)
  refine ⟨p, hsub hp, hpl, ?_⟩
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  have hωV : omegaLimit κ F { x } ⊆ V := hsingle.trans (Set.singleton_subset_iff.mpr hpV)
  have hEv := eventually_mapsTo_of_isOpen_of_omegaLimit_subset κ F { x } hV hωV
  filter_upwards [hEv] with t ht
  exact hVU (ht (Set.mem_singleton x))

/-- A strict descent flow has critical endpoints. -/
theorem FlowCancellation.exists_strict_descent_flow_endpoints {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {S : Set X} (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) (x : X) :
    ∃ p ∈ S,
      ∃ q ∈ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 q) ∧
            (x ∉ S → f q < f x ∧ f x < f p) := by
  have hrange : Set.range (fun t : ℝ => f (F t x)) ⊆ Set.range f := by
    rintro y ⟨t, rfl⟩
    exact ⟨F t x, rfl⟩
  have hbelow : BddBelow (Set.range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddBelow.mono hrange
  have habove : BddAbove (Set.range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddAbove.mono hrange
  have htop := tendsto_atTop_ciInf (hmono x) hbelow
  have hbot := tendsto_atBot_ciSup (hmono x) habove
  have hshiftTop (t : ℝ) : Filter.Tendsto (t + ·) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - t)] with s hs
    linarith
  have hshiftBot (t : ℝ) : Filter.Tendsto (t + ·) Filter.atBot Filter.atBot := by
    apply Filter.tendsto_atBot.mpr
    intro b
    filter_upwards [Filter.eventually_le_atBot (b - t)] with s hs
    linarith
  have hstep (y : X) (hy : y ∉ S) : f (F 1 y) < f y := by
    have hh := hstrict y hy (show (0 : ℝ) < 1 by norm_num)
    simpa only [F.map_zero_apply] using hh
  obtain ⟨p, hp, hfp, hplim⟩ :=
    exists_flow_limit_of_injective_exceptional_height F hf hshiftBot hstep hinj hbot
  obtain ⟨q, hq, hfq, hqlim⟩ :=
    exists_flow_limit_of_injective_exceptional_height F hf hshiftTop hstep hinj htop
  refine ⟨p, hp, q, hq, hplim, hqlim, ?_⟩
  intro hx
  have hlow : f q ≤ f (F 1 x) := by
    rw [hfq]
    exact ciInf_le hbelow 1
  have hhigh : f (F (-1) x) ≤ f p := by
    rw [hfp]
    exact le_ciSup habove (-1)
  have hdec : f (F 1 x) < f x := hstep x hx
  have hinc : f x < f (F (-1) x) := by
    have hh := hstrict x hx (show (-1 : ℝ) < 0 by norm_num)
    simpa only [F.map_zero_apply] using hh
  exact ⟨hlow.trans_lt hdec, hinc.trans_le hhigh⟩

/-- A native descent trajectory has critical endpoints. -/
theorem FlowCancellation.exists_native_descent_endpoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) (x : M) :
    ∃ p ∈ ManifoldMorse.criticalPoints E f,
      ∃ q ∈ ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 q) ∧
            (x ∉ ManifoldMorse.criticalPoints E f → f q < f x ∧ f x < f p) := by
  exact
    exists_strict_descent_flow_endpoints F hf.continuous hinj
      (FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
      (fun x hx =>
        FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc
          hx)
      x

/-! ### Minimum basins -/

/-- The minimum forward basin is open. -/
theorem AdaptedWindows.isOpen_minimum_forward_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hindex : MorseCancellation.nativeMorseIndex E f p = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  have hi : Module.finrank ℝ c.NegativeCoordinates = 0 :=
    (MorseCancellation.nativeMorseIndex_eq_chart c).symm.trans hindex
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hi
  obtain ⟨r, hr, -, hbasin⟩ :=
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have hnear : ∀ᶠ y in 𝓝 p.val, Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val) := by
    filter_upwards [MorseCancellation.morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => S.flow t y) := S.flow.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (MorseCancellation.flow_time_atTop_limit_iff S.flow t y p.val).mp hy
