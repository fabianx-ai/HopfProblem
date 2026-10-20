/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints
import Lib.Geometry.Manifold.Morse.Connection.FieldChartGluing
import Lib.Geometry.Manifold.Morse.Connection.PhaseCylinder
import Lib.Geometry.Manifold.Morse.Connection.SignEnumerations
import Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts

/-!
# The cubic field chart along a unique connecting orbit

## Main result

`MorseCancellation.exists_full_cubic_chart_from_corrected_cylinder`: let `V` be a descent
field with cubic charts `Φq`, `Φp : Model m → M` (sign vector `σ`) at the two critical points
`Φq (-a, 0)` and `Φp (a, 0)`, `A` a vertical flow-box chart of the connecting orbit, and `Ξ` a
corrected cylinder chart of a field `W` (with `W = V` near the two critical points) matching
`Φq` for `t ≤ -1` and `Φp` for `t ≥ 2` up to phases `v₀`, `v₁` and a linear block change
`(L₁, L₂)`. Then there is a chart `Φ : Model m → M` containing the closed axis
`[-a, a] × {0}` in which `W` is the cubic model field `nativeCubicDescent σ Φ (-(a ^ 2))`, with
`Φ (-a, 0)`, `Φ (a, 0)` the two critical points.

## Ingredients

* `native_endpoint_phase_through_box`, `matched_cubic_time_formulas`: propagating the phase
  matching along the flow inside the endpoint boxes;
* `signed_split_transverse_rate`, `signed_split_transverse_exponential`,
  `signed_block_change_cubic_cylinder`, `exists_signed_block_changed_cubic_chart`: a linear
  block change `(P, S)` of the transverse coordinates is absorbed into the cubic chart;
* `exists_native_regular_cubic_field_chart`,
  `exists_regular_cubic_chart_of_native_vertical_field`: the regular part of the cubic model
  is a flow box, `Ψ (cubicFlowCylinder σ a p) = Φ p`;
* `exists_cubic_spatial_overlap_germ`, `cubicFlowCylinder_forward_stays_box`,
  `cubicFlowCylinder_backward_stays_box`, `strictMono_cubicAxisParameter`,
  `tendsto_cubicFlowCylinder_axis_atTop`, `tendsto_cubicFlowCylinder_axis_atBot`,
  `cubicFlowCylinder_zero_clock`, `incoming_axis_segment_in_box`,
  `outgoing_axis_segment_in_box`, `exists_matched_full_cubic_field_chart`: gluing the two
  endpoint charts with the middle flow box along the axis;
* `cubicFlowCylinder_transverse_zero_iff`, `incoming_cubic_slice_basin`,
  `outgoing_cubic_slice_basin`: the basins of the slices in split coordinates.

This is the step of the proof of the first cancellation theorem that puts the gradient-like
field near the single trajectory into a model form
(Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4 and its proof in §5).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Matched cubic time formulas -/

/-- The native endpoint phase through the box. -/
theorem MorseCancellation.native_endpoint_phase_through_box {E Z M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΦmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (hAmodel :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c r : ℝ}
    (hbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source) (z : Fin m → ℝ) {q : Z}
    (hq : q ∈ U) {T v : ℝ}
    (hstart : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hmatch : Φ (cubicFlowCylinder σ a (z, T)) = A (q, T + v)) :
    ∀ t : ℝ,
      cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
        Φ (cubicFlowCylinder σ a (z, t)) = A (q, t + v) := by
  intro t ht
  calc
    Φ (cubicFlowCylinder σ a (z, t)) = F (t - T) (Φ (cubicFlowCylinder σ a (z, T))) :=
      (native_cubic_flow_between_box_points σ ha Φ hV hΦmodel F hF hbox z hstart ht).symm
    _ = F (t - T) (A (q, T + v)) := (congrArg (F (t - T)) hmatch)
    _ = A (q, (T + v) + (t - T)) :=
      (FlowSuspension.native_vertical_cylinder_flow A hAsource hV hAmodel F hF q hq (T + v)
        (t - T))
    _ = A (q, t + v) := congrArg (fun s : ℝ => A (q, s)) (by ring)

/-- The matched cubic time formulas. -/
theorem MorseCancellation.matched_cubic_time_formulas {E Z B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, B) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (e : (Fin m → ℝ) ≃L[ℝ] E)
    (L : E ≃L[ℝ] E) (Q P : E → Z) (v₀ v₁ : E → ℝ) {Oq Op : Set E} (hOq : IsOpen Oq)
    (hOp : IsOpen Op) (h0q : (0 : E) ∈ Oq) (h0p : (0 : E) ∈ Op) (hQU : ∀ u ∈ Oq, Q u ∈ U)
    (hPU : ∀ u ∈ Op, P u ∈ U) {Rq Rp Tq Tp : ℝ}
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Oq, cubicFlowCylinder σ a (e.symm u, Tq) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ Op, cubicFlowCylinder σ a (e.symm u, Tp) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq : ∀ u ∈ Oq, Φq (cubicFlowCylinder σ a (e.symm u, Tq)) = A (Q u, Tq + v₀ u))
    (hphasep : ∀ u ∈ Op, Φp (cubicFlowCylinder σ a (e.symm u, Tp)) = A (P u, Tp + v₁ u))
    (Ψq Ψp Φm : Model m → M) (Ξ : E × ℝ → M) (hnewq : ∀ p, Ψq p = Φq p)
    (hnewp :
      ∀ z t, Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)))
    (hmid : ∀ z t, Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t)) {rq rp : ℝ}
    (hcontrolq :
      Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hcontrolp :
      ∀ z t,
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
          cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hleft : ∀ᶠ u in 𝓝 (0 : E), ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright : ∀ᶠ u in 𝓝 (0 : E), ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L u), t + v₁ (L u))) :
    (∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          t ≤ -1 →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
              Ψq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) ∧
      (∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          2 ≤ t →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
              Ψp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) := by
  have he : Filter.Tendsto e (𝓝 (0 : Fin m → ℝ)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using e.continuous.tendsto 0
  have heL : Filter.Tendsto (fun z : Fin m → ℝ => L (e z)) (𝓝 0) (𝓝 (0 : E)) := by
    have hh : Filter.Tendsto L (𝓝 (0 : E)) (𝓝 (0 : E)) := by
      simpa only [map_zero] using L.continuous.tendsto 0
    exact hh.comp he
  constructor
  · filter_upwards [he.eventually hleft, he.eventually (hOq.mem_nhds h0q)] with z hformula hz
    intro t ht hp
    have hstart : cubicFlowCylinder σ a (z, Tq) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq := by
      simpa only [e.symm_apply_apply] using hsliceq (e z) hz
    have hphase : Φq (cubicFlowCylinder σ a (z, Tq)) = A (Q (e z), Tq + v₀ (e z)) := by
      simpa only [e.symm_apply_apply] using hphaseq (e z) hz
    calc
      Ψq (cubicFlowCylinder σ a (z, t)) = Φq (cubicFlowCylinder σ a (z, t)) := hnewq _
      _ = A (Q (e z), t + v₀ (e z)) :=
        (native_endpoint_phase_through_box σ ha Φq A hAsource hV hqfield hAfield F hF hboxq z
          (hQU (e z) hz) hstart hphase t (hcontrolq hp))
      _ = Ξ (e z, t) := (hformula t ht).symm
      _ = Φm (cubicFlowCylinder σ a (z, t)) := (hmid z t).symm
  · filter_upwards [he.eventually hright, heL.eventually (hOp.mem_nhds h0p)] with z hformula hz
    intro t ht hp
    calc
      Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) :=
        hnewp z t
      _ = A (P (L (e z)), t + v₁ (L (e z))) :=
        (native_endpoint_phase_through_box σ ha Φp A hAsource hV hpfield hAfield F hF hboxp
          (e.symm (L (e z))) (hPU (L (e z)) hz) (hslicep (L (e z)) hz) (hphasep (L (e z)) hz) t
          (hcontrolp z t hp))
      _ = Ξ (e z, t) := (hformula t ht).symm
      _ = Φm (cubicFlowCylinder σ a (z, t)) := (hmid z t).symm

/-! ### Field chart gluing -/

attribute [local instance 100] Classical.propDecidable in
/-- The signed split transverse rate. -/
theorem MorseCancellation.signed_split_transverse_rate {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (z : Fin m → ℝ) :
    MorseHandle.splitCoordinates σ (fun i => σ i * z i) =
      ((-1 : ℝ) • (MorseHandle.splitCoordinates σ z).1,
        (1 : ℝ) • (MorseHandle.splitCoordinates σ z).2) := by
  apply Prod.ext
  · ext i
    change σ i.1 * z i.1 = (-1 : ℝ) * z i.1
    simp [i.2]
  · ext i
    change σ i.1 * z i.1 = (1 : ℝ) * z i.1
    simp [(hσ i.1).resolve_left i.2]

attribute [local instance 100] Classical.propDecidable in
/-- The signed split transverse exponential. -/
theorem MorseCancellation.signed_split_transverse_exponential {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (t : ℝ) (z : Fin m → ℝ) :
    MorseHandle.splitCoordinates σ (fun i => Real.exp (-σ i * t) * z i) =
      (Real.exp t • (MorseHandle.splitCoordinates σ z).1,
        Real.exp (-t) • (MorseHandle.splitCoordinates σ z).2) := by
  apply Prod.ext
  · ext i
    change Real.exp (-σ i.1 * t) * z i.1 = Real.exp t * z i.1
    simp [i.2]
  · ext i
    change Real.exp (-σ i.1 * t) * z i.1 = Real.exp (-t) * z i.1
    simp [(hσ i.1).resolve_left i.2]

attribute [local instance 100] Classical.propDecidable in
/-- The signed block change of the cubic cylinder. -/
theorem MorseCancellation.signed_block_change_cubic_cylinder {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (P : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (S : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ) (a t : ℝ)
    (z : Fin m → ℝ) :
    transverseFieldChange (splitTransverseChange (MorseHandle.splitCoordinates σ) P S)
        (cubicFlowCylinder σ a (z, t)) =
      cubicFlowCylinder σ a
        (splitTransverseChange (MorseHandle.splitCoordinates σ) P S z, t) := by
  apply Prod.ext
  · rfl
  · exact
      splitTransverseChange_commutes (fun i => Real.exp (-σ i * t))
        (MorseHandle.splitCoordinates σ) (Real.exp t) (Real.exp (-t))
        (signed_split_transverse_exponential σ hσ t) P S z

attribute [local instance 100] Classical.propDecidable in
/-- A signed block-changed cubic chart exists. -/
theorem MorseCancellation.exists_signed_block_changed_cubic_chart {m : ℕ} {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (P : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (S : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (τ : ℝ)
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ τ y) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        (∀ s : ℝ, ((s, (0 : Fin m → ℝ)) ∈ Ψ.source ↔ (s, 0) ∈ Φ.source)) ∧
          (∀ s : ℝ, Ψ (s, 0) = Φ (s, 0)) ∧
            (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ τ y) ∧
              ∀ (a t : ℝ)
                (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
                Ψ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, t)) =
                  Φ
                    (cubicFlowCylinder σ a
                      ((MorseHandle.splitCoordinates σ).symm (P u.1, S u.2), t)) := by
  let T := splitTransverseChange (MorseHandle.splitCoordinates σ) P S
  let D := transverseFieldChange T
  let Ψ := D.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have htarget : Ψ.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (Set.univ : Set (Model m))) ↔ y ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hDaxis (s : ℝ) : D (s, 0) = (s, 0) := by
    change (s, T 0) = (s, 0)
    rw [map_zero]
  have hpush (p : Model m) (_ : p ∈ D.toDiffeomorph.toPartialDiffeomorph.source) :
    fderiv ℝ D.toDiffeomorph.toPartialDiffeomorph p (cubicDescent σ τ p) =
      cubicDescent σ τ (D p) := by
    change fderiv ℝ D p (cubicDescent σ τ p) = _
    rw [D.fderiv]
    exact
      transverseFieldChange_cubicDescent σ T
        (splitTransverseChange_commutes σ (MorseHandle.splitCoordinates σ) (-1) 1
          (signed_split_transverse_rate σ hσ) P S)
        τ p
  refine ⟨Ψ, htarget, ?_, ?_, ?_, ?_⟩
  · intro s
    change ((s, (0 : Fin m → ℝ)) ∈ Set.univ ∧ D (s, 0) ∈ Φ.source) ↔ (s, 0) ∈ Φ.source
    rw [hDaxis]
    simp only [Set.mem_univ, true_and]
  · intro s
    change Φ (D (s, 0)) = Φ (s, 0)
    rw [hDaxis]
  · intro y hy
    rw [hmodel y (htarget ▸ hy)]
    exact
      (partialChartField_of_model_conjugacy D.toDiffeomorph.toPartialDiffeomorph Φ
          (cubicDescent σ τ) (cubicDescent σ τ) hpush hy).symm
  · intro a t u
    change Φ (D (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, t))) = _
    rw [signed_block_change_cubic_cylinder σ hσ P S]
    have hT :
      T ((MorseHandle.splitCoordinates σ).symm u) =
        (MorseHandle.splitCoordinates σ).symm (P u.1, S u.2) := by
      simp only [T, splitTransverseChange, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply]
    change Φ (cubicFlowCylinder σ a (T ((MorseHandle.splitCoordinates σ).symm u), t)) = _
    rw [hT]

/-- A native regular cubic field chart exists. -/
theorem MorseCancellation.exists_native_regular_cubic_field_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ Set.univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ι : (Fin m → ℝ) → M)
    (hformula : ∀ p ∈ Φ.source, Φ p = F p.2 (ι p.1)) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
          (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (ι 0)) ∧
            (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
              Ψ.source ⊆ Set.Ioo (-a) a ×ˢ Set.univ ∧ ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  let C := cubicFlowCylinderChart σ ha
  let Ψ := C.symm.trans Φ
  have htarget : Ψ.target = Φ.target := by
    ext x
    change x ∈ Φ.target ∧ Φ.symm x ∈ Set.univ ↔ x ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hcompose (p : (Fin m → ℝ) × ℝ) : Ψ (C p) = Φ p := by
    change Φ (C.symm (C p)) = Φ p
    have hh : C.symm (C p) = p := C.left_inv' (Set.mem_univ p)
    exact congrArg Φ hh
  have hopenaxis : Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change (s, (0 : Fin m → ℝ)) ∈ C.target ∧ C.symm (s, 0) ∈ Φ.source
    refine ⟨⟨hs, Set.mem_univ _⟩, ?_⟩
    rw [hsource]
    change (fun i => Real.exp (σ i * cubicAxisClock a s) * (0 : Fin m → ℝ) i) ∈ U ∧ _
    simp only [Pi.zero_apply, MulZeroClass.mul_zero]
    exact ⟨h0, Set.mem_univ _⟩
  refine ⟨Ψ, htarget, hopenaxis, ?_, ?_, fun _ hp => hp.1, hcompose⟩
  · intro s
    change Φ (cubicFlowCylinderInverse σ a (s, 0)) = _
    have hsΦ : cubicFlowCylinderInverse σ a (s, 0) ∈ Φ.source := by
      rw [hsource]
      simp only [cubicFlowCylinderInverse, Pi.zero_apply, MulZeroClass.mul_zero]
      exact ⟨h0, Set.mem_univ _⟩
    rw [hformula _ hsΦ]
    simp only [cubicFlowCylinderInverse, Pi.zero_apply, MulZeroClass.mul_zero]
    rfl
  · intro x hx
    have hxΦ : x ∈ Φ.target := htarget ▸ hx
    let p := Φ.symm x
    have hp : p ∈ Φ.source := Φ.map_target' hxΦ
    have hpU : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
    have hpC : C p ∈ Ψ.source := by
      change C p ∈ C.target ∧ C.symm (C p) ∈ Φ.source
      have hh : C.symm (C p) = p := C.left_inv' (Set.mem_univ p)
      exact ⟨C.map_source' (Set.mem_univ p), hh.symm ▸ hp⟩
    let α : ℝ → Model m := fun s => C (p.1, s)
    have hα : HasDerivAt α (cubicDescent σ (-(a ^ 2)) (α p.2)) p.2 :=
      hasDerivAt_cubicFlowCylinder σ a p.1 p.2
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Ψ.symm
        (cubicDescent σ (-(a ^ 2))) hα hpC
    have hcurveeq : Ψ.symm.symm ∘ α = fun t => F t (ι p.1) := by
      funext t
      have hpt : (p.1, t) ∈ Φ.source := by rw [hsource]; exact ⟨hpU, Set.mem_univ _⟩
      exact (hcompose (p.1, t)).trans (hformula (p.1, t) hpt)
    rw [hcurveeq] at hd
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (FlowConstruction.partialChartField Ψ.symm (cubicDescent σ (-(a ^ 2)))
            (Ψ (C p)))) at hd
    rw [hcompose p, hformula p hp] at hd
    have hh := (hF (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
    have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) => L 1) hh
    simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
    have hpx : F p.2 (ι p.1) = x := (hformula p hp).symm.trans (Φ.right_inv' hxΦ)
    rw [hpx] at hv
    exact hv

/-- A regular cubic chart of a native vertical field exists. -/
theorem MorseCancellation.exists_regular_cubic_chart_of_native_vertical_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ Set.univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ y ∈ Φ.target,
        V y =
          FlowConstruction.partialChartField Φ.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
          (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (Φ (0, 0))) ∧
            (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
              Ψ.source ⊆ Set.Ioo (-a) a ×ˢ Set.univ ∧ ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  apply exists_native_regular_cubic_field_chart σ ha Φ hsource h0 V F hF (fun z => Φ (z, 0))
  intro p hp
  have hz : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
  simpa only [zero_add] using
    (FlowSuspension.native_vertical_cylinder_flow Φ hsource hV hmodel F hF p.1 hz 0
        p.2).symm

/-! ### Full cubic field charts -/

/-- A cubic spatial overlap germ exists. -/
theorem MorseCancellation.exists_cubic_spatial_overlap_germ {m : ℕ} {M : Type*} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (Φ Ψ : Model m → M) {c r : ℝ} (hr : 0 < r) {l : Filter ℝ} [Filter.NeBot l]
    (hlim : Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) l (𝓝 (c, (0 : Fin m → ℝ))))
    {J : Set ℝ} (hJ : IsOpen J) (hJl : J ∈ l)
    (hmatch :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t ∈ J,
          cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
            Φ (cubicFlowCylinder σ a (z, t)) = Ψ (cubicFlowCylinder σ a (z, t))) :
    ∃ T ∈ J,
      cubicFlowCylinder σ a (0, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r ∧
        Φ =ᶠ[𝓝 (cubicFlowCylinder σ a (0, T))] Ψ := by
  have hnear : ∀ᶠ t in l, cubicFlowCylinder σ a (0, t) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  have hJevent : ∀ᶠ t in l, t ∈ J := hJl
  obtain ⟨T, hTJ, hTball⟩ := (hJevent.and hnear).exists
  let C := cubicFlowCylinderChart σ ha
  let p₀ : (Fin m → ℝ) × ℝ := (0, T)
  have htime : (fun p => Φ (C p)) =ᶠ[𝓝 p₀] (fun p => Ψ (C p)) := by
    have hball : ∀ᶠ p in 𝓝 p₀, C p ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
      (contDiff_cubicFlowCylinder σ a).continuous.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds hTball)
    filter_upwards [continuousAt_fst.eventually hmatch,
      continuousAt_snd.eventually (hJ.mem_nhds hTJ), hball] with p hp hpt hpball
    exact hp p.2 hpt (Metric.ball_subset_closedBall hpball)
  have hCt : C p₀ ∈ C.target := C.map_source' (Set.mem_univ p₀)
  have hi : C.symm (C p₀) = p₀ := C.left_inv' (Set.mem_univ p₀)
  have hInv : Filter.Tendsto C.symm (𝓝 (C p₀)) (𝓝 p₀) := by
    have hh : Filter.Tendsto C.symm (𝓝 (C p₀)) (𝓝 (C.symm (C p₀))) :=
      C.toOpenPartialHomeomorph.symm.continuousAt hCt |>.tendsto
    rwa [hi] at hh
  refine ⟨T, hTJ, hTball, ?_⟩
  filter_upwards [hInv.eventually htime, C.open_target.mem_nhds hCt] with p hp hpt
  have hright : C (C.symm p) = p := C.right_inv' hpt
  change Φ (C (C.symm p)) = Ψ (C (C.symm p)) at hp
  rwa [hright] at hp

/-- The cubic cylinder's forward flow stays in the box. -/
theorem MorseCancellation.cubicFlowCylinder_forward_stays_box {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim :
      Filter.Tendsto (fun t => cubicFlowCylinder σ a (z, t)) Filter.atTop
        (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) {t : ℝ}
    (ht : T ≤ t) : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear :
    ∀ᶠ u in Filter.atTop, cubicFlowCylinder σ a (z, u) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (Filter.eventually_ge_atTop t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨ht, hut⟩ hT (Metric.ball_subset_closedBall hu)

/-- The cubic cylinder's backward flow stays in the box. -/
theorem MorseCancellation.cubicFlowCylinder_backward_stays_box {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim :
      Filter.Tendsto (fun t => cubicFlowCylinder σ a (z, t)) Filter.atBot
        (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) {t : ℝ}
    (ht : t ≤ T) : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear :
    ∀ᶠ u in Filter.atBot, cubicFlowCylinder σ a (z, u) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (Filter.eventually_le_atBot t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨hut, ht⟩ (Metric.ball_subset_closedBall hu) hT

/-- The cubic axis parameter is strictly monotone. -/
theorem MorseCancellation.strictMono_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    StrictMono (cubicAxisParameter a) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left (Real.strictMono_tanh (mul_lt_mul_of_pos_left hst ha)) ha

/-- The cylinder axis tends to the top endpoint. -/
theorem MorseCancellation.tendsto_cubicFlowCylinder_axis_atTop {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) :
    Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) Filter.atTop
      (𝓝 (a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atTop (m := m) ha

/-- The cylinder axis tends to the bottom endpoint. -/
theorem MorseCancellation.tendsto_cubicFlowCylinder_axis_atBot {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) :
    Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) Filter.atBot
      (𝓝 (-a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atBot (m := m) ha

/-- The cylinder's clock at zero. -/
theorem MorseCancellation.cubicFlowCylinder_zero_clock {m : ℕ} (σ : Fin m → ℝ) {a s : ℝ} (ha : 0 < a)
    (hs : s ∈ Set.Ioo (-a) a) :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
  rw [cubicFlowCylinder_axis]
  change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
  rw [cubicAxisParameter_clock ha hs]

/-- The incoming axis segment lies in the box. -/
theorem MorseCancellation.incoming_axis_segment_in_box {m : ℕ} (σ : Fin m → ℝ) {a r T : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Set.Icc (cubicAxisParameter a T) a,
      (s, (0 : Fin m → ℝ)) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) r ∧
        (s < a → T ≤ cubicAxisClock a s) := by
  intro s hs
  rcases hs.2.lt_or_eq with hsa | hsa
  · have hs' : s ∈ Set.Ioo (-a) a := ⟨(cubicAxisParameter_mem ha T).1.trans_le hs.1, hsa⟩
    have ht : T ≤ cubicAxisClock a s := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.1
    have hb :=
      cubicFlowCylinder_forward_stays_box σ ha 0 hr (tendsto_cubicFlowCylinder_axis_atTop σ ha)
        hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩
  · subst s
    exact ⟨Metric.mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩

/-- The outgoing axis segment lies in the box. -/
theorem MorseCancellation.outgoing_axis_segment_in_box {m : ℕ} (σ : Fin m → ℝ) {a r T : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Set.Icc (-a) (cubicAxisParameter a T),
      (s, (0 : Fin m → ℝ)) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) r ∧
        (-a < s → cubicAxisClock a s ≤ T) := by
  intro s hs
  rcases hs.1.eq_or_lt with has | has
  · subst s
    exact ⟨Metric.mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩
  · have hs' : s ∈ Set.Ioo (-a) a := ⟨has, hs.2.trans_lt (cubicAxisParameter_mem ha T).2⟩
    have ht : cubicAxisClock a s ≤ T := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.2
    have hb :=
      cubicFlowCylinder_backward_stays_box σ ha 0 hr (tendsto_cubicFlowCylinder_axis_atBot σ ha)
        hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩

/-- A matched full cubic field chart exists. -/
theorem MorseCancellation.exists_matched_full_cubic_field_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (Φq Φm Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hmfield : ∀ y ∈ Φm.target, V y = nativeCubicDescent σ Φm (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y) {rq rp : ℝ}
    (hrq : 0 < rq) (hrp : 0 < rp) (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) rp ⊆ Φp.source)
    (hmiddle : ∀ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φm.source)
    (hleft : Φq (-a, 0) ∉ Φm.target) (hright : Φp (a, 0) ∉ Φm.target)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hmatchq :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          t ≤ -1 →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
              Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)))
    (hmatchp :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          2 ≤ t →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
              Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
          Φ (-a, 0) = Φq (-a, 0) ∧
            Φ (a, 0) = Φp (a, 0) ∧
              (∀ s ∈ Set.Ioo (-a) a, Φ (s, 0) = Φm (s, 0)) ∧
                ((Φ : Model m → M) =ᶠ[𝓝 (-a, (0 : Fin m → ℝ))] Φq) ∧
                  ((Φ : Model m → M) =ᶠ[𝓝 (a, (0 : Fin m → ℝ))] Φp) := by
  have hqmatch :
    ∀ᶠ z : Fin m → ℝ in 𝓝 0,
      ∀ t ∈ Set.Iio (-1 : ℝ),
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
          Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchq] with z hz
    exact fun t ht => hz t ht.le
  have hpmatch :
    ∀ᶠ z : Fin m → ℝ in 𝓝 0,
      ∀ t ∈ Set.Ioi (2 : ℝ),
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
          Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchp] with z hz
    exact fun t ht => hz t ht.le
  obtain ⟨Tq, hTq, hqball, hgq⟩ :=
    exists_cubic_spatial_overlap_germ σ ha Φq Φm hrq (tendsto_cubicFlowCylinder_axis_atBot σ ha)
      isOpen_Iio (Filter.Iio_mem_atBot (-1 : ℝ)) hqmatch
  obtain ⟨Tp, hTp, hpball, hgp⟩ :=
    exists_cubic_spatial_overlap_germ σ ha Φp Φm hrp (tendsto_cubicFlowCylinder_axis_atTop σ ha)
      isOpen_Ioi (Filter.Ioi_mem_atTop (2 : ℝ)) hpmatch
  have hcutq := cubicAxisParameter_mem ha Tq
  have hcutp := cubicAxisParameter_mem ha Tp
  have horder : cubicAxisParameter a Tq < cubicAxisParameter a Tp :=
    strictMono_cubicAxisParameter ha (by change Tq < -1 at hTq; change 2 < Tp at hTp; linarith)
  have hgq' : (Φq : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tq, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgq
  have hgp' : (Φp : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tp, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgp
  have hqsegment := outgoing_axis_segment_in_box σ ha hrq (Metric.ball_subset_closedBall hqball)
  have hpsegment := incoming_axis_segment_in_box σ ha hrp (Metric.ball_subset_closedBall hpball)
  have hqaxis (s : ℝ) (hs : s ∈ Set.Ioc (-a) (cubicAxisParameter a Tq)) : Φq (s, 0) = Φm (s, 0) :=
    by
    have hs' : s ∈ Set.Ioo (-a) a := ⟨hs.1, hs.2.trans_lt hcutq.2⟩
    obtain ⟨hb, ht⟩ := hqsegment s ⟨hs.1.le, hs.2⟩
    have hball :
      cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈
        Metric.closedBall (-a, (0 : Fin m → ℝ)) rq := by
      rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchq.self_of_nhds (cubicAxisClock a s) ((ht hs.1).trans hTq.le) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  have hpaxis (s : ℝ) (hs : s ∈ Set.Ico (cubicAxisParameter a Tp) a) : Φp (s, 0) = Φm (s, 0) := by
    have hs' : s ∈ Set.Ioo (-a) a := ⟨hcutp.1.trans_le hs.1, hs.2⟩
    obtain ⟨hb, ht⟩ := hpsegment s ⟨hs.1, hs.2.le⟩
    have hball :
      cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp :=
      by rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchp.self_of_nhds (cubicAxisClock a s) (hTp.le.trans (ht hs.2)) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  exact
    FieldChartGluing.exists_closed_axis_native_field_chart Φq Φm Φp
      (cubicDescent σ (-(a ^ 2))) V hqfield hmfield hpfield hcutq.1 horder hcutp.2
      (fun s hs => hboxq (hqsegment s hs).1) hmiddle (fun s hs => hboxp (hpsegment s hs).1) hgq'
      hgp' hqaxis hpaxis hleft hright hne

attribute [local instance 100] Classical.propDecidable in
/-- A full cubic chart from the corrected cylinder exists. -/
theorem MorseCancellation.exists_full_cubic_chart_from_corrected_cylinder {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {m : ℕ}
    {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a : ℝ} (ha : 0 < a) (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (L₁ : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (L₂ : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (Q P : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → Z)
    (v₀ v₁ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ)
    {Oq Op : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)}
    (hOq : IsOpen Oq) (hOp : IsOpen Op) (h0q : 0 ∈ Oq) (h0p : 0 ∈ Op) (hQU : ∀ u ∈ Oq, Q u ∈ U)
    (hPU : ∀ u ∈ Op, P u ∈ U) {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Oq,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
          Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ Op,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
          Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq :
      ∀ u ∈ Oq,
        Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
          A (Q u, Tq + v₀ u))
    (hphasep :
      ∀ u ∈ Op,
        Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
          A (P u, Tp + v₁ u))
    (Ξ :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ) 𝓘(ℝ, E)
        ((MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ) M ∞)
    {O : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)}
    (hO : IsOpen O) (h0O : 0 ∈ O) (hΞsource : Ξ.source = O ×ˢ Set.univ)
    (hΞtarget : Ξ.target = A.target)
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΞfield :
      ∀ y ∈ Ξ.target,
        W y =
          FlowConstruction.partialChartField Ξ.symm
            (fun _ :
                (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ =>
              (0, 1))
            y)
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    (hWq : ∀ᶠ y in 𝓝 (Φq (-a, 0)), W y = V y) (hWp : ∀ᶠ y in 𝓝 (Φp (a, 0)), W y = V y)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hleft :
      ∀ᶠ u in 𝓝 (0 : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
        ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright :
      ∀ᶠ u in 𝓝 (0 : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
        ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, W y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
          Φ (-a, 0) = Φq (-a, 0) ∧ Φ (a, 0) = Φp (a, 0) ∧ Φ (0, 0) = Ξ (0, 0) := by
  let e := MorseHandle.splitCoordinates σ
  let L := L₁.prodCongr L₂
  let T := splitTransverseChange e L₁ L₂
  let D := transverseFieldChange T
  have hqsrc : (-a, (0 : Fin m → ℝ)) ∈ Φq.source := hboxq (Metric.mem_closedBall_self hRq.le)
  have hpsrc : (a, (0 : Fin m → ℝ)) ∈ Φp.source := hboxp (Metric.mem_closedBall_self hRp.le)
  obtain ⟨Ψq, rq, hrq, hΨqbox, hΨqsub, _, hΨqmap, hΨqfield⟩ :=
    FieldChartGluing.exists_controlled_field_germ_chart Φq (cubicDescent σ (-(a ^ 2))) V W
      hqfield hqsrc hWq Metric.isOpen_ball (Metric.mem_ball_self hRq)
  have hcontrolq :
    Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq :=
    fun p hp => Metric.ball_subset_closedBall (hΨqsub (hΨqbox hp)).2
  obtain ⟨ΦpB, _, hpBsource, hpBaxis, hpBfield, hpBflow⟩ :=
    exists_signed_block_changed_cubic_chart σ hσ L₁ L₂ Φp V (-(a ^ 2)) hpfield
  have hDcenter : D (a, 0) = (a, 0) := by change (a, T 0) = (a, 0); rw [map_zero]
  have hOpcoord : IsOpen (D ⁻¹' Metric.ball (a, (0 : Fin m → ℝ)) Rp) :=
    Metric.isOpen_ball.preimage D.continuous
  have hpO : (a, (0 : Fin m → ℝ)) ∈ D ⁻¹' Metric.ball (a, (0 : Fin m → ℝ)) Rp := by
    change D (a, 0) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp
    rw [hDcenter]
    exact Metric.mem_ball_self hRp
  have hWpB : ∀ᶠ y in 𝓝 (ΦpB (a, 0)), W y = V y := by rw [hpBaxis]; exact hWp
  obtain ⟨Ψp, rp, hrp, hΨpbox, hΨpsub, _, hΨpmap, hΨpfield⟩ :=
    FieldChartGluing.exists_controlled_field_germ_chart ΦpB (cubicDescent σ (-(a ^ 2))) V W
      hpBfield ((hpBsource a).mpr hpsrc) hWpB hOpcoord hpO
  have hnewp (z : Fin m → ℝ) (t : ℝ) :
    Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) := by
    have hh := hpBflow a t (e z)
    change
      ΦpB (cubicFlowCylinder σ a (e.symm (e z), t)) =
        Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) at hh
    rw [e.symm_apply_apply] at hh
    exact (hΨpmap _).trans hh
  have hcontrolp (z : Fin m → ℝ) (t : ℝ)
    (hp : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp) :
    cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp := by
    have hb : D (cubicFlowCylinder σ a (z, t)) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp :=
      (hΨpsub (hΨpbox hp)).2
    have hc : D (cubicFlowCylinder σ a (z, t)) = cubicFlowCylinder σ a (e.symm (L (e z)), t) :=
      signed_block_change_cubic_cylinder σ hσ L₁ L₂ a t z
    rw [hc] at hb
    exact Metric.ball_subset_closedBall hb
  let R := PartialChart.restrictTarget e.toDiffeomorph.toPartialDiffeomorph hO
  have hRtarget : R.target = O := by
    ext u
    change
      (u ∈
            (Set.univ :
              Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)) ∧
          u ∈ O) ↔
        u ∈ O
    simp only [Set.mem_univ, true_and]
  have hR0 : (0 : Fin m → ℝ) ∈ R.source := by
    change (0 : Fin m → ℝ) ∈ Set.univ ∧ e 0 ∈ O
    rw [map_zero]
    exact ⟨Set.mem_univ _, h0O⟩
  obtain ⟨B₀, hBsource, hBtarget, hBmap, hBfield⟩ :=
    FlowSuspension.exists_native_phase_cylinder Ξ hΞsource R hRtarget (fun _ => (0 : ℝ))
      contDiff_const W hΞfield
  obtain ⟨Φm, hmTarget, hmidAxis, _, hmField, _, hcompose⟩ :=
    exists_regular_cubic_chart_of_native_vertical_field σ ha B₀ hBsource hR0 W hW hBfield G hG
  have hmid (z : Fin m → ℝ) (t : ℝ) : Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t) := by
    rw [hcompose, hBmap]
    change Ξ (e z, t + 0) = Ξ (e z, t)
    rw [add_zero]
  have hmTargetA : Φm.target = A.target := hmTarget.trans (hBtarget.trans hΞtarget)
  have hzeroAt (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) {c : ℝ}
    (hc : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (hcrit : c ^ 2 = a ^ 2)
    (hf : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) : V (Φ (c, 0)) = 0 := by
    rw [hf _ (Φ.map_source' hc)]
    apply (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) (Φ.map_source' hc)).mpr
    have hi : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hc
    rw [hi]
    ext i <;> simp [cubicDescent, hcrit]
  have hzeroq : V (Φq (-a, 0)) = 0 := hzeroAt Φq hqsrc (by ring) hqfield
  have hzerop : V (Φp (a, 0)) = 0 := hzeroAt Φp hpsrc rfl hpfield
  have hAregular (y : M) (hy : y ∈ A.target) : V y ≠ 0 := by
    intro hz
    rw [hAfield y hy] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hy).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqval : Ψq (-a, 0) = Φq (-a, 0) := hΨqmap _
  have hpval : Ψp (a, 0) = Φp (a, 0) := (hΨpmap _).trans (hpBaxis a)
  have hqnot : Ψq (-a, 0) ∉ Φm.target := by
    rw [hqval, hmTargetA]
    exact fun h => hAregular _ h hzeroq
  have hpnot : Ψp (a, 0) ∉ Φm.target := by
    rw [hpval, hmTargetA]
    exact fun h => hAregular _ h hzerop
  obtain ⟨hmatchq, hmatchp⟩ :=
    matched_cubic_time_formulas σ ha Φq Φp A hAsource hV hqfield hpfield hAfield F hF e L Q P v₀
      v₁ hOq hOp h0q h0p hQU hPU hboxq hboxp hsliceq hslicep hphaseq hphasep Ψq Ψp Φm Ξ hΨqmap
      hnewp hmid hcontrolq hcontrolp hleft hright
  obtain ⟨Φ, haxis, hfield, hΦq, hΦp, hΦmid, _, _⟩ :=
    exists_matched_full_cubic_field_chart σ ha Ψq Φm Ψp W hΨqfield hmField hΨpfield hrq hrp hΨqbox
      hΨpbox (fun s hs => hmidAxis ⟨hs, rfl⟩) hqnot hpnot (by rw [hqval, hpval]; exact hne)
      hmatchq hmatchp
  have hmid0 : Φm (0, 0) = Ξ (0, 0) := by
    have hh := hmid 0 0
    simpa only [cubicFlowCylinder_zero_time, map_zero] using hh
  exact
    ⟨Φ, haxis, hfield, hΦq.trans hqval, hΦp.trans hpval, (hΦmid 0 ⟨by linarith, ha⟩).trans hmid0⟩

/-! ### Cylinder basin labels -/

/-- The cylinder's transverse part vanishes exactly on the axis. -/
theorem MorseCancellation.cubicFlowCylinder_transverse_zero_iff {m : ℕ} (σ : Fin m → ℝ) (a T : ℝ)
    (z : Fin m → ℝ) (i : Fin m) : (cubicFlowCylinder σ a (z, T)).2 i = 0 ↔ z i = 0 := by
  simp [cubicFlowCylinder, Real.exp_ne_zero]

attribute [local instance 100] Classical.propDecidable in
/-- The incoming cubic slice basin. -/
theorem MorseCancellation.incoming_cubic_slice_basin {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (σ : Fin m → ℝ) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (F : Flow ℝ M) {p : M}
    (hbasin :
      ∀ z ∈ Φ.source,
        Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p) ↔ ∀ i, σ i = -1 → z.2 i = 0)
    (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Filter.Tendsto
        (fun t =>
          F t (Φ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T))))
        Filter.atTop (𝓝 p) ↔
      u.1 = 0 := by
  rw [hbasin _ hu]
  have he :
    (∀ i,
        σ i = -1 →
          (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = -1 → (MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← TransverseGerms.splitCoordinates_negative_zero_iff]
  rw [(MorseHandle.splitCoordinates σ).apply_symm_apply]

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing cubic slice basin. -/
theorem MorseCancellation.outgoing_cubic_slice_basin {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (F : Flow ℝ M) {q : M}
    (hbasin :
      ∀ z ∈ Φ.source,
        Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 q) ↔ ∀ i, σ i = 1 → z.2 i = 0)
    (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Filter.Tendsto
        (fun t =>
          F t (Φ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T))))
        Filter.atBot (𝓝 q) ↔
      u.2 = 0 := by
  rw [hbasin _ hu]
  have he :
    (∀ i,
        σ i = 1 →
          (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = 1 → (MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← TransverseGerms.splitCoordinates_positive_zero_iff σ hσ]
  rw [(MorseHandle.splitCoordinates σ).apply_symm_apply]

end
