/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.CubicFlow

/-!
# Endpoint slices of the cubic model along an actual orbit

Let `V` be a descent field on a manifold `M` and `Φ : Model m → M` a chart in which `V` is the
cubic model field `nativeCubicDescent σ Φ (-(a ^ 2))`, i.e. `(x, z) ↦ (x ^ 2 - a ^ 2, -σ_i z_i)`;
its axis orbit runs from the critical point `Φ (-a, 0)` to `Φ (a, 0)` and its integral curves are
the cylinder coordinates `cubicFlowCylinder σ a`.

* `native_cubic_flow_between_box_points`, `exists_cubic_slice_in_axis_ball`,
  `exists_native_cubic_endpoint_flow_coordinates`: the flow `F` of `V` is computed by
  `cubicFlowCylinder` as long as the cylinder point stays in a box inside `Φ.source`.
* `exists_endpoint_slice_on_actual_orbit`: an orbit converging to a cubic endpoint along the axis
  meets a slice `Φ (cubicFlowCylinder σ a (0, T)) = F τ x`.
* `exists_clock_normalized_cubic_endpoint`, `exists_basin_preserving_endpoint_clock`: composing
  the chart with a flow time `F d` (`SmoothODE.flow_shifted_chart_source`) makes the axis clock
  agree with the orbit's own time, without changing the forward and backward basins.
* `partialChartField_zero_iff`: a chart field vanishes exactly where its model vanishes.

This is the step of the proof of the first cancellation theorem in which coordinates around the
two critical points are aligned with the connecting trajectory
(cf. Milnor, *Lectures on the h-cobordism theorem*, §5, proof of Theorem 5.4).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### The cancelled descent field -/

/-- The partial chart field vanishes exactly at the critical point. -/
theorem MorseCancellation.partialChartField_zero_iff {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (W : D → D) {x : M}
    (hx : x ∈ Φ.target) :
    FlowConstruction.partialChartField Φ.symm W x = 0 ↔ W (Φ.symm x) = 0 := by
  rw [FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W hx]
  have hl : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ Φ (Φ.symm x) :=
    ⟨Φ, Φ.map_target' hx, fun _ _ => rfl⟩
  let A := hl.mfderivToContinuousLinearEquiv (by simp)
  let B : D ≃L[ℝ] TangentSpace 𝓘(ℝ, D) (Φ.symm x) :=
    (NormedSpace.fromTangentSpace (Φ.symm x)).symm
  change A (B (W (Φ.symm x))) = 0 ↔ W (Φ.symm x) = 0
  constructor
  · intro h
    have hb : B (W (Φ.symm x)) = 0 := A.injective (h.trans (map_zero A).symm)
    exact B.injective (hb.trans (map_zero B).symm)
  · intro h
    rw [h, map_zero, map_zero]

/-! ### Endpoint slices on actual orbits -/

/-- The native cubic flow between two box points. -/
theorem MorseCancellation.native_cubic_flow_between_box_points {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c r : ℝ}
    (hbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source) (z : Fin m → ℝ) {s t : ℝ}
    (hs : cubicFlowCylinder σ a (z, s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (ht : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    F (t - s) (Φ (cubicFlowCylinder σ a (z, s))) = Φ (cubicFlowCylinder σ a (z, t)) := by
  let γ : ℝ → M := fun u => Φ (cubicFlowCylinder σ a (z, u))
  have hforward {u v : ℝ} (huv : u < v)
    (hu : cubicFlowCylinder σ a (z, u) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hv : cubicFlowCylinder σ a (z, v) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    F (v - u) (γ u) = γ v := by
    have hstay (w : ℝ) (hw : w ∈ Set.Icc u v) : cubicFlowCylinder σ a (z, w) ∈ Φ.source :=
      hbox (cubicFlowCylinder_stays_axis_ball σ ha z hw hu hv)
    have hcont : ContinuousOn γ (Set.Icc u v) :=
      Φ.contMDiffOn_toFun.continuousOn.comp
        (((contDiff_cubicFlowCylinder σ a).continuous.comp
            (continuous_const.prodMk continuous_id)).continuousOn)
        hstay
    have hcurve : IsMIntegralCurveOn γ V (Set.Ioo u v) := by
      intro w hw
      have hp := hstay w ⟨hw.1.le, hw.2.le⟩
      have hd :=
        FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
          (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicFlowCylinder σ a z w) hp
      have hd' :
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ w
          ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeCubicDescent σ Φ (-(a ^ 2)) (γ w))) :=
        hd
      rw [← hmodel (γ w) (Φ.map_source' hp)] at hd'
      exact hd'.hasMFDerivWithinAt
    exact FlowSuspension.native_flow_segment_endpoints hV F hF huv hcont hcurve
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hforward hst hs ht
  · subst t
    rw [sub_self, F.map_zero_apply]
  · have hh := congrArg (F (t - s)) (hforward hts ht hs)
    rw [← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply] at hh
    exact hh.symm

/-- A cubic slice inside the axis ball exists. -/
theorem MorseCancellation.exists_cubic_slice_in_axis_ball {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {c r : ℝ} (hc : c ∈ Set.Icc (-a) a) (hr : 0 < r) :
    ∃ (T δ : ℝ),
      0 < δ ∧
        ∀ z : Fin m → ℝ,
          ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r := by
  have hcl : c ∈ closure (Set.Ioo (-a) a) := by
    rw [closure_Ioo (by linarith : -a ≠ a)]
    exact hc
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp hcl r hr
  let T := cubicAxisClock a s
  have hpoint : cubicFlowCylinder σ a (0, T) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hnear : cubicFlowCylinder σ a (0, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r := by
    rw [hpoint, Metric.mem_ball, Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ Dist.dist s c)]
    simpa only [dist_comm] using hdist
  have hcont : Continuous (fun z : Fin m → ℝ => cubicFlowCylinder σ a (z, T)) :=
    (contDiff_cubicFlowCylinder σ a).continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      (hcont.continuousAt (Metric.isOpen_ball.mem_nhds hnear))
  refine ⟨T, δ, hδ, ?_⟩
  intro z hz
  exact hδsub (mem_closedBall_zero_iff.mpr hz)

/-- Native cubic endpoint flow coordinates exist. -/
theorem MorseCancellation.exists_native_cubic_endpoint_flow_coordinates {m : ℕ} {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) :
    ∃ (r δ T : ℝ),
      0 < r ∧
        0 < δ ∧
          Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
            (∀ z : Fin m → ℝ,
                ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
              ∀ p ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r,
                p.1 ∈ Set.Ioo (-a) a →
                  ‖(cubicFlowCylinderInverse σ a p).1‖ ≤ δ →
                    Φ p =
                      F (cubicAxisClock a p.1 - T)
                        (Φ (cubicFlowCylinder σ a ((cubicFlowCylinderInverse σ a p).1, T))) := by
  obtain ⟨r, hr, hbox⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds hcΦ)
  obtain ⟨T, δ, hδ, hslice⟩ := exists_cubic_slice_in_axis_ball σ ha hc hr
  refine ⟨r, δ, T, hr, hδ, hbox, hslice, ?_⟩
  intro p hp hpa hpδ
  let z := (cubicFlowCylinderInverse σ a p).1
  have hinit := Metric.ball_subset_closedBall (hslice z hpδ)
  have hpoint : cubicFlowCylinder σ a (z, cubicAxisClock a p.1) = p :=
    cubicFlowCylinder_right_inv σ ha hpa
  have hfinish :
    cubicFlowCylinder σ a (z, cubicAxisClock a p.1) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    hpoint.symm ▸ hp
  have hh := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox z hinit hfinish
  rw [hpoint] at hh
  exact hh.symm

/-- An endpoint slice on the actual orbit exists. -/
theorem MorseCancellation.exists_endpoint_slice_on_actual_orbit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ} [Filter.NeBot l]
    (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (r δ T τ : ℝ),
      0 < r ∧
        0 < δ ∧
          Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
            (∀ z : Fin m → ℝ,
                ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
              Φ (cubicFlowCylinder σ a (0, T)) = F τ x := by
  obtain ⟨r, δ, T, hr, hδ, hbox, hslice, _⟩ :=
    exists_native_cubic_endpoint_flow_coordinates σ ha Φ hV hmodel F hF hc hcΦ
  have hcont := Φ.toOpenPartialHomeomorph.symm.continuousAt (Φ.map_source' hcΦ)
  have hcoord : Filter.Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (c, (0 : Fin m → ℝ))) := by
    have hh : Filter.Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (Φ.symm (Φ (c, 0)))) :=
      hcont.tendsto.comp hlim
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    rwa [hinv] at hh
  have hnear : ∀ᶠ t in l, Φ.symm (F t x) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hcoord.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨t, htnear, s, hs, hsΦ, hsorbit⟩ := (hnear.and htail).exists
  have hinv : Φ.symm (F t x) = (s, (0 : Fin m → ℝ)) := by
    rw [← hsorbit]
    exact Φ.left_inv' hsΦ
  rw [hinv] at htnear
  have hpoint : cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hstart :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    hpoint.symm ▸ Metric.ball_subset_closedBall htnear
  have hfinish : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hflow := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox 0 hstart hfinish
  rw [hpoint, hsorbit, ← F.map_add] at hflow
  exact ⟨r, δ, T, T - cubicAxisClock a s + t, hr, hδ, hbox, hslice, hflow.symm⟩

/-- The flow-shifted chart source. -/
theorem SmoothODE.flow_shifted_chart_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞) (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) :
    (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).source = Φ.source := by
  ext p
  change p ∈ Φ.source ∧ Φ p ∈ Set.univ ↔ p ∈ Φ.source
  simp

/-- A clock-normalized cubic endpoint exists. -/
theorem MorseCancellation.exists_clock_normalized_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcrit : c ^ 2 = a ^ 2) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (r δ T : ℝ),
      Ψ.source = Φ.source ∧
        Ψ (c, 0) = Φ (c, 0) ∧
          0 < r ∧
            0 < δ ∧
              Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
                (∀ z : Fin m → ℝ,
                    ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
                  (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
                    (∀ t : ℝ,
                        cubicFlowCylinder σ a (0, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
                          Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
                      ∃ d : ℝ, ∀ z : Model m, Ψ z = F d (Φ z) := by
  have hV₁ := hV.of_le (by simp : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω))
  obtain ⟨r, δ, T, τ, hr, hδ, hbox, hslice, hcenter⟩ :=
    exists_endpoint_slice_on_actual_orbit σ ha Φ hV₁ hmodel F hF hc hcΦ x hlim htail
  have hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t) := fun t =>
    (SmoothODE.contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)
  let Ψ := Φ.trans (SmoothODE.nativeFlowTimeDiffeomorph F hs (T - τ)).toPartialDiffeomorph
  have hsource : Ψ.source = Φ.source := SmoothODE.flow_shifted_chart_source Φ F hs (T - τ)
  have hΨmodel : ∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y := by
    intro y hy
    exact
      SmoothODE.partialChartField_flow_shift Φ F hs hF (cubicDescent σ (-(a ^ 2))) hmodel
        (T - τ) hy
  have hzero : V (Φ (c, 0)) = 0 := by
    rw [hmodel _ (Φ.map_source' hcΦ)]
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    have hw : cubicDescent σ (-(a ^ 2)) (Φ.symm (Φ (c, 0))) = 0 := by
      rw [hinv]
      ext i <;> simp [cubicDescent, hcrit]
    unfold nativeCubicDescent FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, hw, map_zero, map_zero]
  have hvalue : Ψ (c, 0) = Φ (c, 0) :=
    FlowConstruction.flow_fixed_of_zero hV₁ F hF hzero (T - τ)
  have hΨbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source := hsource.symm ▸ hbox
  have hbase : Ψ (cubicFlowCylinder σ a (0, T)) = F T x := by
    change F (T - τ) (Φ (cubicFlowCylinder σ a (0, T))) = F T x
    rw [hcenter, ← F.map_add, sub_add_cancel]
  refine ⟨Ψ, r, δ, T, hsource, hvalue, hr, hδ, hΨbox, hslice, hΨmodel, ?_, T - τ, fun _ => rfl⟩
  intro t ht
  have hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hh := native_cubic_flow_between_box_points σ ha Ψ hV₁ hΨmodel F hF hΨbox 0 hstart ht
  rw [hbase, ← F.map_add, sub_add_cancel] at hh
  exact hh.symm

/-! ### Basin-preserving endpoint clocks -/

/-- A basin-preserving endpoint clock exists. -/
theorem MorseCancellation.exists_basin_preserving_endpoint_clock {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcrit : c ^ 2 = a ^ 2) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (r δ T : ℝ),
      Ψ.source = Φ.source ∧
        Ψ (c, 0) = Φ (c, 0) ∧
          0 < r ∧
            0 < δ ∧
              Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
                (∀ z : Fin m → ℝ,
                    ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
                  (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
                    (∀ t : ℝ,
                        cubicFlowCylinder σ a (0, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
                          Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
                      ∀ z : Model m,
                        ∀ p : M,
                          (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atTop (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p)) ∧
                            (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atBot (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 p)) := by
  obtain ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, d, hmap⟩ :=
    exists_clock_normalized_cubic_endpoint σ ha Φ hV hmodel F hF hc hcrit hcΦ x hlim htail
  refine ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, ?_⟩
  intro z p
  rw [hmap]
  exact ⟨flow_time_atTop_limit_iff F d (Φ z) p, flow_time_atBot_limit_iff F d (Φ z) p⟩

end
