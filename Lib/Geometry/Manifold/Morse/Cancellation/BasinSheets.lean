/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Cancellation.TransverseGerms
import Lib.Geometry.Manifold.Morse.Cancellation.ConnectionData

/-!
# Basin sheets of the cancellation data

For a cancellation datum `D` the outgoing sheet `D.outgoingSheet` (the unstable
manifold of `q` parametrised by time and the negative model coordinates) and
the incoming sheet `D.incomingSheet` (the stable manifold of `p`) pass through
`D.A 0`, are smooth there, and have time-independent labels in the cylinder
chart (`outgoingSheet_properties`, `incomingSheet_properties`). Transversality
of the two sheets in `M` gives `D.Transverse` (`transverse_of_native_sheets`).

The basins are graphs over planes in a chart at `D.A 0`
(`outgoing_basin_chart`, `incoming_basin_chart`); hence any map into the basin
of `q` (resp. `p`) through `D.A 0` factors through the outgoing (resp.
incoming) sheet (`outgoing_basin_factorization`,
`incoming_basin_factorization`). Consequently transverse maps `F`, `G` into
the two basins give `D.Transverse` (`transverse_of_native_basin_sheets`) and a
cancellation (`cancel_of_transverse_basin_sheets`).

This is the reduction of the transversality hypothesis of Milnor, *Lectures on
the h-cobordism theorem*, Theorem 5.4 to transversality of any two maps into
the stable and unstable manifolds of the connecting orbit.

## Tags

morse-theory, cancellation, stable-manifold, transversality
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Basin sheets and factorizations -/

/-- The outgoing basin sheet of the cancellation data. -/
def MorseCancellation.NativeConnectionCancellationData.outgoingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.NegativeSpace D.σ) : M :=
  D.flow (w.1 - D.Tq)
    (D.Φq
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm (w.2, 0), D.Tq)))

/-- The incoming basin sheet of the cancellation data. -/
def MorseCancellation.NativeConnectionCancellationData.incomingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.PositiveSpace D.σ) : M :=
  D.flow (w.1 - D.Tp)
    (D.Φp
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm (0, w.2), D.Tp)))

/-- The outgoing sheet's properties. -/
theorem MorseCancellation.NativeConnectionCancellationData.outgoingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, E) ∞ D.outgoingSheet 0 ∧
      D.outgoingSheet 0 = D.A 0 ∧
        (fun w : ℝ × MorseHandle.NegativeSpace D.σ =>
            (D.A.symm (D.outgoingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × MorseHandle.NegativeSpace D.σ => D.slices.Q (w.2, 0)) := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hh :=
    FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero
      (fun u =>
        D.Φq
          (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
            ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq)))
      D.slices.phaseQ D.Tq D.slices.smooth_phaseQ D.slices.zero_phaseQ D.slices.formulaQ
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

/-- The incoming sheet's properties. -/
theorem MorseCancellation.NativeConnectionCancellationData.incomingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) ∞ D.incomingSheet 0 ∧
      D.incomingSheet 0 = D.A 0 ∧
        (fun w : ℝ × MorseHandle.PositiveSpace D.σ =>
            (D.A.symm (D.incomingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × MorseHandle.PositiveSpace D.σ => D.slices.P (0, w.2)) := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hh :=
    FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero
      (fun u =>
        D.Φp
          (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
            ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp)))
      D.slices.phaseP D.Tp D.slices.smooth_phaseP D.slices.zero_phaseP D.slices.formulaP
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

/-- The native sheets are transverse. -/
theorem MorseCancellation.NativeConnectionCancellationData.transverse_of_native_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ)
        𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) D.outgoingSheet D.incomingSheet 0
        0) :
    D.Transverse := by
  obtain ⟨hout, hout0, houtlabel⟩ := D.outgoingSheet_properties
  obtain ⟨hin, hin0, hinlabel⟩ := D.incomingSheet_properties
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hQdiff :=
    (D.slices.Q.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.Q.open_source.mem_nhds hQ0)).differentiableAt
      (by simp)
  have hPdiff :=
    (D.slices.P.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.P.open_source.mem_nhds hP0)).differentiableAt
      (by simp)
  have hq :
    DifferentiableAt ℝ (fun x : MorseHandle.NegativeSpace D.σ => D.slices.Q (x, 0)) 0 :=
    hQdiff.comp (f := fun x : MorseHandle.NegativeSpace D.σ => (x, 0)) 0
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
          (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hp :
    DifferentiableAt ℝ (fun y : MorseHandle.PositiveSpace D.σ => D.slices.P (0, y)) 0 :=
    hPdiff.comp (f := fun y : MorseHandle.PositiveSpace D.σ => (0, y)) 0
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
          (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hA0 : (0 : (Fin m → ℝ) × ℝ) ∈ D.A.source := by
    rw [D.slices.source]
    exact ⟨D.slices.zero_domain, Set.mem_univ _⟩
  exact
    TransverseGerms.transverse_labels_of_native_flow_sheets D.A hA0 D.outgoingSheet
      D.incomingSheet (hout.mdifferentiableAt (by simp)) (hin.mdifferentiableAt (by simp)) hout0
      hin0 hq hp houtlabel hinlabel htrans

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing basin chart of the cancellation data. -/
theorem MorseCancellation.NativeConnectionCancellationData.outgoing_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.outgoingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × MorseHandle.NegativeSpace D.σ => P ((w.2, 0), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q) ↔ w.1.2 = 0 := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  let S := fun u =>
    D.Φq
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq))
  have hbasin (u) (hu : u ∈ D.slices.Q.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atBot (𝓝 q) ↔ u.2 = 0 :=
    MorseCancellation.outgoing_cubic_slice_basin D.σ D.signs (1 / 2) D.Tq D.Φq D.flow D.basinQ u
      (D.boxQ (D.slices.sliceQ u hu))
  obtain ⟨P, -, h0P, hP0, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero S D.slices.phaseQ D.Tq D.slices.smooth_phaseQ
      D.slices.zero_phaseQ D.slices.formulaQ
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q))
      (fun t y => MorseCancellation.flow_time_atBot_limit_iff D.flow t y q) (fun u => u.2 = 0) hbasin
  have heq :=
    FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.Q.open_source hQ0 D.flow S
      D.Tq hformula
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hP0, ?_, hplane⟩
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply] using heq

attribute [local instance 100] Classical.propDecidable in
/-- The incoming basin chart of the cancellation data. -/
theorem MorseCancellation.NativeConnectionCancellationData.incoming_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.incomingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × MorseHandle.PositiveSpace D.σ => P ((0, w.2), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p) ↔ w.1.1 = 0 := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  let S := fun u =>
    D.Φp
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp))
  have hbasin (u) (hu : u ∈ D.slices.P.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atTop (𝓝 p) ↔ u.1 = 0 :=
    MorseCancellation.incoming_cubic_slice_basin D.σ (1 / 2) D.Tp D.Φp D.flow D.basinP u
      (D.boxP (D.slices.sliceP u hu))
  obtain ⟨P, -, h0P, hPzero, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero S D.slices.phaseP D.Tp D.slices.smooth_phaseP
      D.slices.zero_phaseP D.slices.formulaP
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p))
      (fun t y => MorseCancellation.flow_time_atTop_limit_iff D.flow t y p) (fun u => u.1 = 0) hbasin
  have heq :=
    FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.P.open_source hP0 D.flow S
      D.Tp hformula
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hPzero, ?_, hplane⟩
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply] using heq

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing basin factorization. -/
theorem MorseCancellation.NativeConnectionCancellationData.outgoing_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atBot (𝓝 q)) :
    ∃ u : X → ℝ × MorseHandle.NegativeSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.outgoingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.outgoing_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × A) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inl ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ A)).prod
      (ContinuousLinearMap.fst ℝ ℝ A)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × A) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × A) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.1), ?_⟩
    exact Prod.ext (Prod.ext rfl hz) rfl
  exact
    TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q)) hp
      hbasin hmodel

attribute [local instance 100] Classical.propDecidable in
/-- The incoming basin factorization. -/
theorem MorseCancellation.NativeConnectionCancellationData.incoming_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atTop (𝓝 p)) :
    ∃ u : X → ℝ × MorseHandle.PositiveSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.incomingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.incoming_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × B) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inr ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ B)).prod
      (ContinuousLinearMap.fst ℝ ℝ B)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × B) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × B) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.2), ?_⟩
    exact Prod.ext (Prod.ext hz rfl) rfl
  exact
    TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p)) hp
      hbasin hmodel

/-- The native basin sheets are transverse. -/
theorem MorseCancellation.NativeConnectionCancellationData.transverse_of_native_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y) : D.Transverse := by
  obtain ⟨u, hu, hu0, hFu⟩ := D.outgoing_basin_factorization hF hx hFbasin
  obtain ⟨v, hv, hv0, hGv⟩ := D.incoming_basin_factorization hG hy hGbasin
  apply D.transverse_of_native_sheets
  exact
    TransverseGerms.native_transversality_of_sheet_factorizations
      (D.outgoingSheet_properties.1.mdifferentiableAt (by simp))
      (D.incomingSheet_properties.1.mdifferentiableAt (by simp)) hu hv hu0 hv0 hFu hGv
      (hy.trans hx.symm) htrans

/-- Transverse basin sheets give a cancellation. -/
theorem MorseCancellation.NativeConnectionCancellationData.cancel_of_transverse_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc c d → z = p ∨ z = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ z,
                z ∈ ManifoldMorse.criticalPoints E g ↔
                  z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
              ∀ z, f z ∉ Set.Ioo c d → g =ᶠ[𝓝 z] f :=
  D.cancel (D.transverse_of_native_basin_sheets hF hG hx hy hFbasin hGbasin htrans) hf hm hinj hp
    hq hpq hc hd hpair

end
