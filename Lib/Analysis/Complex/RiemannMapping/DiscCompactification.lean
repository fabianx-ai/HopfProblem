/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# Extending a homeomorphism onto the disc to the closure (Carathéodory)

Let `X` be a compact Hausdorff space, `D ⊆ X` dense, and `e : D ≃ₜ 𝔻` a homeomorphism onto the open
unit disc. If at every point `x ∉ D` the map `e` has a limit `w` with `‖w‖ = 1` and the inverse of `e`
tends to `x` at `w` (`RiemannBoundary.DiscBoundaryLimits`), then the continuous extension of `e` is a
homeomorphism `X ≃ₜ closedBall 0 1` (`RiemannBoundary.closedDiscHomeomorph`). The file also gives
a criterion for the limit of the inverse at a boundary point through a local conformal boundary
chart (`RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart`) and the resulting
injectivity on boundary points.

This is the topological part of Carathéodory's extension theorem (Pommerenke, *Boundary Behaviour
of Conformal Maps*, Thm 2.6; cf. Ahlfors, *Complex Analysis*, Ch. 6 §1.3).
-/

open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff Interval NNReal UniformConvergence Uniformity

noncomputable section

/-- The inverse of `e : D ≃ₜ 𝔻` as a map `ℂ → X`, with the value `e.symm 0` off the open disc. -/
def RiemannBoundary.discHomeomorphInverse {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : ℂ) : X := by
  classical
    exact
    if hz : z ∈ Metric.ball (0 : ℂ) 1 then (e.symm ⟨z, hz⟩ : X) else (e.symm ⟨0, by simp⟩ : X)

/-- On the open disc, `discHomeomorphInverse e` computes `e.symm`. -/
theorem RiemannBoundary.discHomeomorphInverse_of_mem {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discHomeomorphInverse e z = (e.symm ⟨z, hz⟩ : X) := by
  simp only [discHomeomorphInverse, dif_pos hz]

/-- Let `f` restrict to `e : D ≃ₜ 𝔻`, let `H` have a nonzero strict derivative at `0`, and let `φ :
ℂ → X` be continuous at `0` with `φ z ∈ D` and `f (φ z) = H z` whenever `‖H z‖ < 1`, for `z` near
`0`. Then the inverse of `e` tends to `φ 0` at `H 0` within the open disc. -/
theorem RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart {X : Type*}
    [TopologicalSpace X] {D : Set X} (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ : ℂ → X} {H : ℂ → ℂ} {d : ℂ} (hφ : ContinuousAt φ 0)
    (hH : HasStrictDerivAt H d 0) (hd : d ≠ 0)
    (hcoord : ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 → φ z ∈ D ∧ f (φ z) = H z) :
    Filter.Tendsto (discHomeomorphInverse e) (𝓝[Metric.ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) := by
  let k := hH.localInverse H d 0 hd
  have hk0 : k (H 0) = 0 := hH.eventually_left_inverse hd |>.self_of_nhds
  have hk : Filter.Tendsto k (𝓝 (H 0)) (𝓝 (0 : ℂ)) := by
    have ht : Filter.Tendsto k (𝓝 (H 0)) (𝓝 (k (H 0))) :=
      (hH.to_localInverse hd).hasDerivAt.continuousAt.tendsto
    rwa [hk0] at ht
  have ht : Filter.Tendsto (φ ∘ k) (𝓝[Metric.ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) :=
    (hφ.tendsto.comp hk).mono_left nhdsWithin_le_nhds
  have heq : discHomeomorphInverse e =ᶠ[𝓝[Metric.ball (0 : ℂ) 1] (H 0)] φ ∘ k := by
    have hright : ∀ᶠ y in 𝓝[Metric.ball (0 : ℂ) 1] (H 0), H (k y) = y :=
      (hH.eventually_right_inverse hd).filter_mono nhdsWithin_le_nhds
    have hparam :
      ∀ᶠ y in 𝓝[Metric.ball (0 : ℂ) 1] (H 0),
        ‖H (k y)‖ < 1 → φ (k y) ∈ D ∧ f (φ (k y)) = H (k y) :=
      (hk.eventually hcoord).filter_mono nhdsWithin_le_nhds
    filter_upwards [hright, hparam, self_mem_nhdsWithin] with y hy hcy hyD
    have hyn : ‖y‖ < 1 := by simpa using hyD
    obtain ⟨hmem, hval⟩ := hcy (by simpa only [hy] using hyn)
    have himage : e ⟨φ (k y), hmem⟩ = ⟨y, hyD⟩ := by
      apply Subtype.ext
      exact (he ⟨φ (k y), hmem⟩).symm.trans (hval.trans hy)
    rw [discHomeomorphInverse_of_mem e hyD]
    change (e.symm ⟨y, hyD⟩ : X) = φ (k y)
    have hinv : e.symm ⟨y, hyD⟩ = ⟨φ (k y), hmem⟩ := by rw [← himage, e.symm_apply_apply]
    exact congrArg Subtype.val hinv
  exact ht.congr' heq.symm

/-- A point of the unit circle lies in the closure of the open unit disc. -/
theorem RiemannBoundary.unitCircle_mem_closure_unitBall {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ closure (Metric.ball (0 : ℂ) 1) := by
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  simpa only [Metric.mem_closedBall, dist_zero_right, hw] using le_rfl (a := (1 : ℝ))

/-- Two boundary charts `φ`, `ψ` as in `tendsto_discHomeomorphInverse_of_boundary_chart`, for `F`
and `G` with `‖F 0‖ = 1` and `F 0 = G 0`, satisfy `φ 0 = ψ 0` (`X` Hausdorff). -/
theorem RiemannBoundary.boundary_points_eq_of_equal_disc_values {X : Type*} [TopologicalSpace X]
    {D : Set X} [T2Space X] (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ ψ : ℂ → X} {F G : ℂ → ℂ} {dF dG : ℂ}
    (hφ : ContinuousAt φ 0) (hψ : ContinuousAt ψ 0) (hF : HasStrictDerivAt F dF 0) (hdF : dF ≠ 0)
    (hG : HasStrictDerivAt G dG 0) (hdG : dG ≠ 0)
    (hcoordF : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < 1 → φ z ∈ D ∧ f (φ z) = F z)
    (hcoordG : ∀ᶠ z in 𝓝 (0 : ℂ), ‖G z‖ < 1 → ψ z ∈ D ∧ f (ψ z) = G z) (hcircle : ‖F 0‖ = 1)
    (hvalue : F 0 = G 0) : φ 0 = ψ 0 := by
  have : Filter.NeBot (𝓝[Metric.ball (0 : ℂ) 1] (F 0)) :=
    (mem_closure_iff_nhdsWithin_neBot).mp (unitCircle_mem_closure_unitBall hcircle)
  have htF := tendsto_discHomeomorphInverse_of_boundary_chart e he hφ hF hdF hcoordF
  have htG := tendsto_discHomeomorphInverse_of_boundary_chart e he hψ hG hdG hcoordG
  rw [← hvalue] at htG
  exact tendsto_nhds_unique htF htG

/-- The extension by continuity (`Dense.extend`) of `e : D ≃ₜ 𝔻` from the dense set `D` to `X`. -/
def RiemannBoundary.discCompactificationMap {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) : X → ℂ :=
  hD.extend (fun z : D => (e z : ℂ))

/-- The compactification map computes the disc coordinate. -/
theorem RiemannBoundary.discCompactificationMap_coe {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : D) :
    discCompactificationMap hD e z = (e z : ℂ) :=
  hD.extend_eq (continuous_subtype_val.comp e.continuous) z

/-- At every `x ∉ D`, `e` has a limit `w` with `‖w‖ = 1`, and the inverse of `e` tends to `x` at `w`
within the open disc. -/
def RiemannBoundary.DiscBoundaryLimits {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) : Prop :=
  ∀ x ∉ D,
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto (fun z : D => (e z : ℂ)) (Filter.comap Subtype.val (𝓝 x)) (𝓝 w) ∧
          Filter.Tendsto (discHomeomorphInverse e) (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 x)

/-- The compactification map is continuous. -/
theorem RiemannBoundary.discCompactificationMap_continuous {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Continuous (discCompactificationMap hD e) := by
  apply hD.continuous_extend
  intro x
  by_cases hx : x ∈ D
  · refine ⟨(e ⟨x, hx⟩ : ℂ), ?_⟩
    rw [← hD.isDenseInducing_val.nhds_eq_comap ⟨x, hx⟩]
    exact (continuous_subtype_val.comp e.continuous).continuousAt
  · obtain ⟨w, _, hw, _⟩ := hb x hx
    exact ⟨w, hw⟩

/-- The compactification map on a boundary point is the limit. -/
theorem RiemannBoundary.discCompactificationMap_boundary {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e)
    {x : X} (hx : x ∉ D) :
    ‖discCompactificationMap hD e x‖ = 1 ∧
      Filter.Tendsto (discHomeomorphInverse e)
        (𝓝[Metric.ball (0 : ℂ) 1] (discCompactificationMap hD e x)) (𝓝 x) := by
  obtain ⟨w, hw, ht, hi⟩ := hb x hx
  have he : discCompactificationMap hD e x = w := hD.extend_eq_of_tendsto ht
  rw [he]
  exact ⟨hw, hi⟩

/-- The compactification map has norm at most one. -/
theorem RiemannBoundary.discCompactificationMap_norm_le {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e)
    (x : X) : ‖discCompactificationMap hD e x‖ ≤ 1 := by
  by_cases hx : x ∈ D
  · rw [discCompactificationMap_coe hD e ⟨x, hx⟩]
    exact
      (show ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 by
          simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property).le
  · exact ((discCompactificationMap_boundary hD e hb hx).1).le

/-- The compactification map is injective. -/
theorem RiemannBoundary.discCompactificationMap_injective {X : Type*} [TopologicalSpace X]
    {D : Set X} [T2Space X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1)
    (hb : DiscBoundaryLimits e) : Function.Injective (discCompactificationMap hD e) := by
  intro x y hxy
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · apply congrArg Subtype.val (e.injective ?_ : (⟨x, hx⟩ : D) = ⟨y, hy⟩)
      apply Subtype.ext
      simpa only [discCompactificationMap_coe hD e ⟨x, hx⟩,
        discCompactificationMap_coe hD e ⟨y, hy⟩] using hxy
    · have hn := (discCompactificationMap_boundary hD e hb hy).1
      rw [← hxy, discCompactificationMap_coe hD e ⟨x, hx⟩] at hn
      have hlt : ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property
      exact (hlt.ne hn).elim
  · by_cases hy : y ∈ D
    · have hn := (discCompactificationMap_boundary hD e hb hx).1
      rw [hxy, discCompactificationMap_coe hD e ⟨y, hy⟩] at hn
      have hlt : ‖(e ⟨y, hy⟩ : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨y, hy⟩).property
      exact (hlt.ne hn).elim
    · obtain ⟨hn, ht⟩ := discCompactificationMap_boundary hD e hb hx
      have hu := (discCompactificationMap_boundary hD e hb hy).2
      rw [← hxy] at hu
      have : Filter.NeBot (𝓝[Metric.ball (0 : ℂ) 1] (discCompactificationMap hD e x)) :=
        mem_closure_iff_nhdsWithin_neBot.mp (unitCircle_mem_closure_unitBall hn)
      exact tendsto_nhds_unique ht hu

/-- The compactification map has range the closed disc. -/
theorem RiemannBoundary.discCompactificationMap_range {X : Type*} [TopologicalSpace X] {D : Set X}
    [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Set.range (discCompactificationMap hD e) = Metric.closedBall (0 : ℂ) 1 := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    simpa using discCompactificationMap_norm_le hD e hb x
  · have hclosed : IsClosed (Set.range (discCompactificationMap hD e)) :=
      (isCompact_range (discCompactificationMap_continuous hD e hb)).isClosed
    have hdisc : Metric.ball (0 : ℂ) 1 ⊆ Set.range (discCompactificationMap hD e) := by
      intro y hy
      refine ⟨(e.symm ⟨y, hy⟩ : X), ?_⟩
      rw [discCompactificationMap_coe, e.apply_symm_apply]
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact closure_minimal hdisc hclosed

/-- Carathéodory extension: for `X` compact Hausdorff, `D` dense and `DiscBoundaryLimits e`, the map
`e` extends to a homeomorphism `X ≃ₜ closedBall 0 1`. -/
def RiemannBoundary.closedDiscHomeomorph {X : Type*} [TopologicalSpace X] {D : Set X} [T2Space X]
    [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    X ≃ₜ Metric.closedBall (0 : ℂ) 1 := by
  let F : X → Metric.closedBall (0 : ℂ) 1 := fun x =>
    ⟨discCompactificationMap hD e x, by simpa using discCompactificationMap_norm_le hD e hb x⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      exact discCompactificationMap_injective hD e hb (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : ℂ) ∈ Set.range (discCompactificationMap hD e) := by
        rw [discCompactificationMap_range hD e hb]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hF)
      ((discCompactificationMap_continuous hD e hb).subtype_mk _)

/-- The closed-disc homeomorphism computes the compactification map. -/
theorem RiemannBoundary.closedDiscHomeomorph_coe {X : Type*} [TopologicalSpace X] {D : Set X}
    [T2Space X] [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1)
    (hb : DiscBoundaryLimits e) (z : D) : (closedDiscHomeomorph hD e hb z : ℂ) = (e z : ℂ) :=
  discCompactificationMap_coe hD e z
