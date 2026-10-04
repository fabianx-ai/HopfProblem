/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Connection.CubicFieldChart
import Lib.Geometry.Manifold.Morse.Connection.EndpointBasins
import Lib.Geometry.Manifold.Morse.Connection.PhaseFlow
import Lib.Geometry.Manifold.Morse.Cancellation.CubicConnection

/-!
# Cancellation data of a unique connection

`MorseCancellation.NativeConnectionCancellationData f p q m` packages a
descending field with flow, cubic endpoint charts `Φq`, `Φp` at the critical
points `q` (above) and `p` (below), a vertical cylinder chart `A` on which the
field is `∂/∂t` and `f` is affine, the basin descriptions in the endpoint
charts, the uniqueness of the connecting orbit through `A (0, 0)`, and matching
endpoint slice data `NativeEndpointSliceData`.

The datum is `Transverse` when the two label sheets `Q (·, 0)`, `P (0, ·)` of
the slice data are transverse at `0`. A transverse datum can be cancelled:
there is a Morse function `g` equal to `f` off the band `f ⁻¹' (Ioo c d)`
whose critical set is that of `f` minus `{p, q}`
(`NativeConnectionCancellationData.cancel`, via
`cancel_native_endpoint_slice_data` and
`cancel_unique_native_transverse_connection`, which straighten the connection
into the cubic model of `Morse.Cancellation.CubicConnection`).

Such a datum exists for a unique connecting orbit between critical points of
adjacent index with signed Morse charts, `finrank ℝ E = m + 1`
(`exists_native_connection_cancellation_data`); its flow has the same orbits
and limits as the given one.

This is the hypothesis structure of Milnor, *Lectures on the h-cobordism
theorem*, Theorem 5.4: one trajectory, transverse intersection of the sphere
`S_R` with `S_L` in the middle level.

## Tags

morse-theory, cancellation, transversality
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Native cancellation data -/

/-- A unique descending connection equipped with cubic endpoint charts, a vertical cylinder, and matching slice data. -/
structure MorseCancellation.NativeConnectionCancellationData {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ)
    (p q : M) (m : ℕ) where
  σ : Fin m → ℝ
  signs : ∀ i, σ i = -1 ∨ σ i = 1
  field : (y : M) → TangentSpace 𝓘(ℝ, E) y
  smooth_field :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, field y⟩ : TangentBundle 𝓘(ℝ, E) M))
  flow : Flow ℝ M
  integral : ∀ y, IsMIntegralCurve (fun t => flow t y) field
  zero : ∀ y ∈ ManifoldMorse.criticalPoints E f, field y = 0
  descent : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (field y) < 0
  Φq : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  endpointQ : Φq (-(1 / 2 : ℝ), 0) = q
  endpointP : Φp (1 / 2, 0) = p
  fieldQ : ∀ y ∈ Φq.target, field y = nativeCubicDescent σ Φq (-(1 / 2 : ℝ) ^ 2) y
  fieldP : ∀ y ∈ Φp.target, field y = nativeCubicDescent σ Φp (-(1 / 2 : ℝ) ^ 2) y
  A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞
  vertical :
    ∀ y ∈ A.target,
      field y =
        FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y
  speed : ℝ
  positive_speed : 0 < speed
  height : ℝ
  height_formula : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = height - speed * z.2
  Rq : ℝ
  Rp : ℝ
  Tq : ℝ
  Tp : ℝ
  positive_Rq : 0 < Rq
  positive_Rp : 0 < Rp
  boxQ : Metric.closedBall (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) Rq ⊆ Φq.source
  boxP : Metric.closedBall (1 / 2, (0 : Fin m → ℝ)) Rp ⊆ Φp.source
  basinQ :
    ∀ z ∈ Φq.source,
      Filter.Tendsto (fun t => flow t (Φq z)) Filter.atBot (𝓝 q) ↔ ∀ i, σ i = 1 → z.2 i = 0
  basinP :
    ∀ z ∈ Φp.source,
      Filter.Tendsto (fun t => flow t (Φp z)) Filter.atTop (𝓝 p) ↔ ∀ i, σ i = -1 → z.2 i = 0
  unique :
    ∀ y,
      Filter.Tendsto (fun t => flow t y) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => flow t y) Filter.atTop (𝓝 p) → ∃ t, flow t (A (0, 0)) = y
  slices : NativeEndpointSliceData σ (1 / 2) Φq Φp A Rq Rp Tq Tp

/-! ### Cancellation of a transverse connection -/

attribute [local instance 100] Classical.propDecidable in
/-- A unique native transverse connection can be cancelled. -/
theorem MorseCancellation.cancel_unique_native_transverse_connection {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (Q P :
      PartialDiffeomorph
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) 𝓘(ℝ, Z)
        (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) Z ∞)
    (H :
      PartialDiffeomorph
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) ∞)
    (h0 : 0 ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hQsource : Q.source = H.source) (hPsource : P.source = H.target) (hQtarget : Q.target = U)
    (hPtarget : P.target = U) (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace σ)
        𝓘(ℝ, MorseHandle.PositiveSpace σ)
        𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
        (fun x => H (x, 0)) (fun y => (0, y)) 0 0)
    (v₀ v₁ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ)
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Q.source,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
          Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ P.source,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
          Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq :
      ∀ u ∈ Q.source,
        Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
          A (Q u, Tq + v₀ u))
    (hphasep :
      ∀ u ∈ P.source,
        Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
          A (P u, Tp + v₁ u))
    (hqbasin :
      ∀ z ∈ Φq.source,
        Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 (Φq (-a, 0))) ↔
          ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin :
      ∀ z ∈ Φp.source,
        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 (Φp (a, 0))) ↔
          ∀ i, σ i = -1 → z.2 i = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 (Φq (-a, 0))) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φq (-a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0))) {c d : ℝ} (hc : c < f (Φp (a, 0)))
    (hd : f (Φq (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  have hV1 := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : A (z, t) = F t (A (z, 0)) := by
    simpa only [zero_add] using
      (FlowSuspension.native_vertical_cylinder_flow A hAsource hV1 hAfield F hF z hz 0
          t).symm
  have hleft :=
    FlowSuspension.cylinder_outgoing_basin_labels F A Q (fun z hz => hflow z (hQU hz))
      (fun u => Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)))
      (fun u => Tq + v₀ u) hphaseq
      (fun u hu => outgoing_cubic_slice_basin σ hσ a Tq Φq F hqbasin u (hboxq (hsliceq u hu)))
  have hright :=
    FlowSuspension.cylinder_incoming_basin_labels F A P (fun z hz => hflow z (hPU hz))
      (fun u => Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)))
      (fun u => Tp + v₁ u) hphasep
      (fun u hu => incoming_cubic_slice_basin σ a Tp Φp F hpbasin u (hboxp (hslicep u hu)))
  rw [hQtarget, hQsource] at hleft
  rw [hPtarget, hPsource] at hright
  have hheightAux : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) / s = b / s - z.2 := by
    intro z hz ht
    rw [hheight z hz ht]
    field_simp
  obtain
    ⟨L₁, L₂, N, W, G, Ξ, _, hNsub, hW, hG, hzeroW, hdescW, hgerm, hΞsource, hΞtarget, hΞfield,
      hΞaxis, hunique, hmatch⟩ :=
    FlowSuspension.exists_unique_phase_corrected_cylinder A hAsource (hf.div_const s)
      hheightAux V hV hAfield F hF Q P H h0 hH0 hQ0 hP0 (fun _ hz => hQsource ▸ hz)
      (fun _ hz => hPsource ▸ hz) hQtarget hPtarget hdiagram htrans (fun z hz => hleft z hz 0)
      (fun z hz => hright z hz 1) hold hv₀ hv₁ hv₀zero hv₁zero
  have hdescWf (x : M) (hx : x ∉ ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f x (W x) < 0 :=
    (FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hs
          (W x)).mp
      (hdescW x
        ((FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp))
              hs (V x)).mpr
          (hdesc x hx)))
  have hAregular (x : M) (hx : x ∈ A.target) : V x ≠ 0 := by
    intro hz
    rw [hAfield x hx] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqN : Φq (-a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hq)
  have hpN : Φp (a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hp)
  have hQ0source : 0 ∈ Q.source := hQsource ▸ h0
  have hP0source : 0 ∈ P.source := by
    rw [hPsource, ← hH0]
    exact H.map_source' h0
  have hne : Φq (-a, 0) ≠ Φp (a, 0) := by
    intro h
    exact hpq.ne (congrArg f h.symm)
  obtain ⟨Γ, hΓaxis, hΓfield, hΓq, hΓp, hΓcenter⟩ :=
    exists_full_cubic_chart_from_corrected_cylinder σ hσ ha Φq Φp A hAsource hV1 hqfield hpfield
      hAfield F hF L₁ L₂ Q P v₀ v₁ Q.open_source P.open_source hQ0source hP0source
      (fun u hu => hQU (Q.map_source' hu)) (fun u hu => hPU (P.map_source' hu)) hRq hRp hboxq
      hboxp hsliceq hslicep hphaseq hphasep Ξ Q.open_source hQ0source hΞsource hΞtarget
      (hW.of_le (by simp)) hΞfield G hG (hgerm _ hqN) (hgerm _ hpN) hne
      (hmatch.mono fun _ h => h.1) (hmatch.mono fun _ h => h.2)
  have hΓ0 : Γ (0, 0) = A (0, 0) := hΓcenter.trans (hΞaxis 0)
  have hσne : ∀ i, σ i ≠ 0 := by
    intro i
    rcases hσ i with hi | hi <;> rw [hi] <;> norm_num
  have hcancel :=
    cancel_unique_native_cubic_connection σ hσne ha Γ hΓaxis hf hm W hW hΓfield G hG
      (fun x hx => (hzeroW x).mpr (hzero x hx)) hdescWf hinj (by rw [hΓp]; exact hp)
      (by rw [hΓq]; exact hq) (by rw [hΓp, hΓq]; exact hpq) (by rw [hΓp]; exact hc)
      (by rw [hΓq]; exact hd) (by simpa only [hΓp, hΓq] using hpair)
      (by
        intro x _ hbot htop
        rw [hΓq] at hbot
        rw [hΓp] at htop
        rw [hΓ0]
        exact hunique x hbot htop)
  simpa only [hΓp, hΓq] using hcancel

/-- Native endpoint slice data can be cancelled. -/
theorem MorseCancellation.cancel_native_endpoint_slice_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞) {Rq Rp Tq Tp : ℝ}
    (D : NativeEndpointSliceData σ a Φq Φp A Rq Rp Tq Tp)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace σ)
        𝓘(ℝ, MorseHandle.PositiveSpace σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.Q (x, 0))
        (fun y => D.P (0, y)) 0 0)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y =
          FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hqbasin :
      ∀ z ∈ Φq.source,
        Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 (Φq (-a, 0))) ↔
          ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin :
      ∀ z ∈ Φp.source,
        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 (Φp (a, 0))) ↔
          ∀ i, σ i = -1 → z.2 i = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 (Φq (-a, 0))) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φq (-a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0))) {c d : ℝ} (hc : c < f (Φp (a, 0)))
    (hd : f (Φq (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  have hrelative :=
    TransverseGerms.relative_transverse_of_label_sheets D.Q D.P D.H D.zero_source D.H_zero
      D.Q_zero D.P_zero (fun _ hz => D.Q_source ▸ hz) (fun _ hz => D.P_source ▸ hz) D.diagram
      htrans
  exact
    cancel_unique_native_transverse_connection σ hσ ha Φq Φp A D.source hf hm hs hheight V hV
      hqfield hpfield hAfield F hF hzero hdesc hinj D.Q D.P D.H D.zero_source D.H_zero D.Q_zero
      D.P_zero D.Q_source D.P_source D.Q_target D.P_target D.diagram hrelative D.phaseQ D.phaseP
      D.smooth_phaseQ D.smooth_phaseP D.zero_phaseQ D.zero_phaseP hRq hRp hboxq hboxp D.sliceQ
      D.sliceP D.formulaQ D.formulaP hqbasin hpbasin hold hp hq hpq hc hd hpair

/-! ### Transversality of the cancellation data -/

/-- The cancellation data's sheets are transverse. -/
def MorseCancellation.NativeConnectionCancellationData.Transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ}
    {f : M → ℝ} {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    Prop :=
  NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace D.σ)
    𝓘(ℝ, MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.slices.Q (x, 0))
    (fun y => D.slices.P (0, y)) 0 0

/-- The cancellation of a native connection datum. -/
theorem MorseCancellation.NativeConnectionCancellationData.cancel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) (htrans : D.Transverse)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ y ∈ ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ y,
                y ∈ ManifoldMorse.criticalPoints E g ↔
                  y ∈ ManifoldMorse.criticalPoints E f ∧ y ≠ p ∧ y ≠ q) ∧
              ∀ y, f y ∉ Set.Ioo c d → g =ᶠ[𝓝 y] f := by
  have hh :=
    MorseCancellation.cancel_native_endpoint_slice_data D.σ D.signs (by norm_num) D.Φq D.Φp D.A D.slices
      htrans hf hm D.positive_speed D.height_formula D.field D.smooth_field D.fieldQ D.fieldP
      D.vertical D.flow D.integral D.zero D.descent hinj D.positive_Rq D.positive_Rp D.boxQ D.boxP
      (by simpa only [D.endpointQ] using D.basinQ) (by simpa only [D.endpointP] using D.basinP)
      (by simpa only [D.endpointQ, D.endpointP] using D.unique) (by rw [D.endpointP]; exact hp)
      (by rw [D.endpointQ]; exact hq) (by rw [D.endpointP, D.endpointQ]; exact hpq)
      (by rw [D.endpointP]; exact hc) (by rw [D.endpointQ]; exact hd)
      (by simpa only [D.endpointP, D.endpointQ] using hpair)
  simpa only [D.endpointP, D.endpointQ] using hh

attribute [local instance 100] Classical.propDecidable in
/-- Native connection cancellation data exists. -/
theorem MorseCancellation.exists_native_connection_cancellation_data {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q x : M} (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ y ∈ ManifoldMorse.criticalPoints E f, V y = 0)
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ y ∈ ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q)
    (hp : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
    (hunique :
      ∀ y,
        Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) → ∃ t, F t x = y)
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y) :
    ∃ D : NativeConnectionCancellationData (E := E) f p q m,
      (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ z in 𝓝 y, D.field z = V z) ∧
        (∀ y,
            Set.range (fun t => D.flow t y) = Set.range (fun t => F t y) ∧
              (∀ z,
                  Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 z) ↔
                    Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 z)) ∧
                ∀ z,
                  Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 z) ↔
                    Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 z)) ∧
          ∃ t, F t x = D.A 0 := by
  obtain
    ⟨x₀, r, b, W, G, U, A, hxp, hxq, hr, hW, hG, hzeros, hneg, hgerms, hmono, hp₀, hq₀, hunique₀,
      _, h0U, hAsource, hAaxis, hheight, hAfield, hgeometry, hreference⟩ :=
    FlowTimeChange.exists_normalized_connection_cylinder hf hdim V hV hzero hdesc F hF hpq
      hc hd hpair hp hq hunique
  have hgp : ∀ᶠ y in 𝓝 p, W y = cp.descentField y := by
    filter_upwards [hgerms p hpc, heqp] with y h₁ h₂
    exact h₁.trans h₂
  have hgq : ∀ᶠ y in 𝓝 q, W y = cq.descentField y := by
    filter_upwards [hgerms q hqc, heqq] with y h₁ h₂
    exact h₁.trans h₂
  obtain
    ⟨σ, Ψq, Ψp, B, Rq, Rp, Tq, Tp, hσ, hRq, hRp, hqval, hpval, hqbox, hpbox, hqfield, hpfield,
      hqbasin, hpbasin, hBsub, _, hBmap, hBfield, ⟨D⟩⟩ :=
    exists_actual_connection_slice_data cp cq hf.continuous hdim hindex hW G hG hmono hxp hxq hp₀
      hq₀ hgp hgq A hAsource h0U hAfield hAaxis
  have hB0 : B (0, 0) = x₀ := by rw [hBmap, hAaxis, G.map_zero_apply]
  refine
    ⟨{  σ := σ
        signs := hσ
        field := W
        smooth_field := hW
        flow := G
        integral := hG
        zero := hzeros
        descent := hneg
        Φq := Ψq
        Φp := Ψp
        endpointQ := hqval
        endpointP := hpval
        fieldQ := hqfield
        fieldP := hpfield
        A := B
        vertical := hBfield
        speed := r
        positive_speed := hr
        height := b
        height_formula := ?_
        Rq := Rq
        Rp := Rp
        Tq := Tq
        Tp := Tp
        positive_Rq := hRq
        positive_Rp := hRp
        boxQ := hqbox
        boxP := hpbox
        basinQ := hqbasin
        basinP := hpbasin
        unique := ?_
        slices := D }, hgerms, hgeometry, ?_⟩
  · intro z hz ht
    rw [hBmap]
    exact hheight z (hBsub hz) ⟨ht.1.le, ht.2.le⟩
  · intro y hyq hyp
    rw [hB0]
    exact hunique₀ y hyq hyp
  · change ∃ t, F t x = B (0, 0)
    rw [hB0]
    exact hreference

end
