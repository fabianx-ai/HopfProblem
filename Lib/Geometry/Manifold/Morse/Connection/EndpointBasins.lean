/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints
import Lib.Geometry.Manifold.Morse.Connection.SignEnumerations
import Lib.Geometry.Manifold.Morse.Connection.TransitionPhase
import Lib.Geometry.Manifold.Morse.Connection.TransportedCorrections

/-!
# Stable and unstable planes at the cubic endpoints

Two critical points `q` (index `λ + 1`) and `p` (index `λ`) joined by an orbit `x` of a descent
field `V` whose flow decreases `f`, with Morse charts `cq`, `cp`, are given cubic charts
`Φq`, `Φp : Model m → M` with a common sign vector `σ` in which `V` is the cubic descent field
and the forward basin of `p` (the backward basin of `q`) is the coordinate plane
`{z_i = 0 | σ_i = -1}` (`{z_i = 0 | σ_i = 1}`):

* `incoming_linear_stable_plane`, `outgoing_linear_unstable_plane`: the linear model;
* `endpoint_axis_tail_of_restriction`, `exists_cubic_endpoint_basin_restriction`,
  `exists_actual_incoming_cubic_basin`, `exists_actual_outgoing_cubic_basin`: restricting the
  cubic chart so that the basin is exactly the coordinate plane, with the orbit `x` entering
  along the axis;
* `exists_matched_connection_basin_endpoints`: both endpoints at once, with the same `σ`.

`NativeEndpointSliceData σ a Φq Φp A Rq Rp Tq Tp` records slices of the two cubic charts at
times `Tq`, `Tp` inside boxes of radii `Rq`, `Rp`, identified with a vertical flow-box chart `A`
of the orbit through base charts `Q`, `P` (with transition `H`, `P ∘ H = Q`) and phases
`phaseQ`, `phaseP`; `exists_original_endpoint_slice_data` and
`exists_actual_connection_slice_data` construct it.

cf. Milnor, *Lectures on the h-cobordism theorem*, §5, proof of Theorem 5.4 (coordinates near
the two critical points in which the trajectory and the stable and unstable manifolds are
coordinate planes).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Native cancellation data -/

/-- Endpoint slice charts and phase data identifying the two cubic ends with a common flow cylinder. -/
structure MorseCancellation.NativeEndpointSliceData {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    (Rq Rp Tq Tp : ℝ) where
  labelDomain : Set (Fin m → ℝ)
  open_domain : IsOpen labelDomain
  zero_domain : (0 : Fin m → ℝ) ∈ labelDomain
  source : A.source = labelDomain ×ˢ Set.univ
  Q :
    PartialDiffeomorph 𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      𝓘(ℝ, Fin m → ℝ) (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (Fin m → ℝ) ∞
  P :
    PartialDiffeomorph 𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      𝓘(ℝ, Fin m → ℝ) (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (Fin m → ℝ) ∞
  H :
    PartialDiffeomorph 𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      𝓘(ℝ, MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
      (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) ∞
  zero_source : 0 ∈ H.source
  H_zero : H 0 = 0
  Q_zero : Q 0 = 0
  P_zero : P 0 = 0
  Q_source : Q.source = H.source
  P_source : P.source = H.target
  Q_target : Q.target = labelDomain
  P_target : P.target = labelDomain
  diagram : ∀ u ∈ H.source, P (H u) = Q u
  phaseQ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ
  phaseP : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ
  smooth_phaseQ : ContDiff ℝ ∞ phaseQ
  smooth_phaseP : ContDiff ℝ ∞ phaseP
  zero_phaseQ : phaseQ 0 = 0
  zero_phaseP : phaseP 0 = 0
  sliceQ :
    ∀ u ∈ Q.source,
      cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
        Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq
  sliceP :
    ∀ u ∈ P.source,
      cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
        Metric.closedBall (a, (0 : Fin m → ℝ)) Rp
  formulaQ :
    ∀ u ∈ Q.source,
      Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
        A (Q u, Tq + phaseQ u)
  formulaP :
    ∀ u ∈ P.source,
      Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
        A (P u, Tp + phaseP u)

/-! ### Endpoint basins -/

attribute [local instance 100] Classical.propDecidable in
/-- Original endpoint slice data exists. -/
theorem MorseCancellation.exists_original_endpoint_slice_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : A.source = U ×ˢ Set.univ) (h0U : 0 ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y =
          FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    {Rq Rp δq δp Tq Tp : ℝ} (hδq : 0 < δq) (hδp : 0 < δp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ z : Fin m → ℝ,
        ‖z‖ ≤ δq → cubicFlowCylinder σ a (z, Tq) ∈ Metric.ball (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ z : Fin m → ℝ,
        ‖z‖ ≤ δp → cubicFlowCylinder σ a (z, Tp) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp)
    (hpointq : Φq (cubicFlowCylinder σ a (0, Tq)) = A (0, Tq))
    (hpointp : Φp (cubicFlowCylinder σ a (0, Tp)) = A (0, Tp)) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞,
      B.source ⊆ A.source ∧
        B.target ⊆ A.target ∧
          (∀ z, B z = A z) ∧
            (∀ y ∈ B.target,
                V y =
                  FlowConstruction.partialChartField B.symm
                    (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
              Nonempty (NativeEndpointSliceData σ a Φq Φp B Rq Rp Tq Tp) := by
  obtain ⟨Q, v, hQ0, hQfix, hv0, hv, hQU, hQslice, hQphase⟩ :=
    FlowSuspension.exists_native_endpoint_slice_phase σ ha Φq A hsource h0U V hqfield
      hAfield hδq hboxq hsliceq hpointq
  obtain ⟨P, w, hP0, hPfix, hw0, hw, hPU, hPslice, hPphase⟩ :=
    FlowSuspension.exists_native_endpoint_slice_phase σ ha Φp A hsource h0U V hpfield
      hAfield hδp hboxp hslicep hpointp
  let e := MorseHandle.splitCoordinates σ
  obtain
    ⟨Q', P', H, O, hO, h0O, h0H, hH0, hQ'0, hP'0, hQ's, hP's, hQ't, hP't, hOsub, hQ'sub, hP'sub,
      hQ'map, hP'map, hdiagram, _⟩ :=
    TransverseGerms.exists_common_transverse_coordinates e Q P hQ0 hP0 hQfix hPfix
  have hOU : O ⊆ U := fun _ hz => hQU (hOsub hz).1
  obtain ⟨B, hBs, hBsub, hBt, hBmap, hBfield⟩ :=
    TransverseGerms.exists_restricted_native_cylinder A hsource hO hOU V hAfield
  refine
    ⟨B, hBsub, hBt, hBmap, hBfield,
      ⟨{  labelDomain := O
          open_domain := hO
          zero_domain := h0O
          source := hBs
          Q := Q'
          P := P'
          H := H
          zero_source := h0H
          H_zero := hH0
          Q_zero := hQ'0
          P_zero := hP'0
          Q_source := hQ's
          P_source := hP's
          Q_target := hQ't
          P_target := hP't
          diagram := hdiagram
          phaseQ := fun u => v (e.symm u)
          phaseP := fun u => w (e.symm u)
          smooth_phaseQ := hv.comp e.symm.contDiff
          smooth_phaseP := hw.comp e.symm.contDiff
          zero_phaseQ := by rw [map_zero, hv0]
          zero_phaseP := by rw [map_zero, hw0]
          sliceQ := fun u hu => hQslice (e.symm u) (hQ'sub u hu)
          sliceP := fun u hu => hPslice (e.symm u) (hP'sub u hu)
          formulaQ := ?_
          formulaP := ?_ }⟩⟩
  · intro u hu
    rw [hBmap, hQ'map]
    exact hQphase (e.symm u) (hQ'sub u hu)
  · intro u hu
    rw [hBmap, hP'map]
    exact hPphase (e.symm u) (hP'sub u hu)

attribute [local instance 100] Classical.propDecidable in
/-- The incoming linear stable plane. -/
theorem MorseCancellation.incoming_linear_stable_plane {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) 1 p) = MorseHandle.descent (L p))
    (p : Model m) : (L p).1 = 0 ↔ ∀ i, σ i = -1 → p.2 i = 0 := by
  have heig : (L p).1 = 0 ↔ endpointLinearField σ (1 / 2) 1 p = -p := by
    constructor
    · intro hz
      apply L.injective
      rw [hL, map_neg]
      apply Prod.ext
      · change (L p).1 = -(L p).1
        rw [hz, neg_zero]
      · rfl
    · intro h
      have hh := congrArg Prod.fst (hL p)
      rw [h, map_neg] at hh
      have hs : (2 : ℝ) • (L p).1 = 0 := by
        rw [two_smul]
        exact (congrArg (fun z => z + (L p).1) hh.symm).trans (neg_add_cancel _)
      exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  rw [heig]
  constructor
  · intro h i hi
    have hh := congrArg (fun q : Model m => q.2 i) h
    change -σ i * p.2 i = -p.2 i at hh
    rw [hi] at hh
    linarith
  · intro h
    apply Prod.ext
    · simp [endpointLinearField]
    · funext i
      rcases hσ i with hi | hi
      · simp [endpointLinearField, hi, h i hi]
      · simp [endpointLinearField, hi]

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing linear unstable plane. -/
theorem MorseCancellation.outgoing_linear_unstable_plane {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) (-1) p) = MorseHandle.descent (L p))
    (p : Model m) : (L p).2 = 0 ↔ ∀ i, σ i = 1 → p.2 i = 0 := by
  have heig : (L p).2 = 0 ↔ endpointLinearField σ (1 / 2) (-1) p = p := by
    constructor
    · intro hz
      apply L.injective
      rw [hL]
      apply Prod.ext
      · rfl
      · change -(L p).2 = (L p).2
        rw [hz, neg_zero]
    · intro h
      have hh := congrArg Prod.snd (hL p)
      rw [h] at hh
      have hs : (2 : ℝ) • (L p).2 = 0 := by
        rw [two_smul]
        exact (congrArg (fun z => z + (L p).2) hh).trans (neg_add_cancel _)
      exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  rw [heig]
  constructor
  · intro h i hi
    have hh := congrArg (fun q : Model m => q.2 i) h
    simp only [endpointLinearField, hi] at hh
    linarith
  · intro h
    apply Prod.ext
    · simp [endpointLinearField]
    · funext i
      rcases hσ i with hi | hi
      · simp [endpointLinearField, hi]
      · simp [endpointLinearField, hi, h i hi]

attribute [local instance 100] Classical.propDecidable in
/-- The endpoint axis tail of a restriction. -/
theorem MorseCancellation.endpoint_axis_tail_of_restriction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {p : M} {m : ℕ} (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hsub : Ψ.source ⊆ Φ.source) (hmap : ∀ z, Ψ z = Φ z) {a b c : ℝ}
    (hc : (c, (0 : Fin m → ℝ)) ∈ Ψ.source) (hcenter : Ψ (c, 0) = p) (F : Flow ℝ M) (x : M)
    {l : Filter ℝ} (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p))
    (htail : ∀ᶠ t in l, ∃ s ∈ Set.Ioo a b, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∀ᶠ t in l, ∃ s ∈ Set.Ioo a b, (s, (0 : Fin m → ℝ)) ∈ Ψ.source ∧ Ψ (s, 0) = F t x := by
  have hp : p ∈ Ψ.target := hcenter ▸ Ψ.map_source' hc
  filter_upwards [htail, hlim.eventually (Ψ.open_target.mem_nhds hp)] with t ht htΨ
  obtain ⟨s, hs, hsΦ, hval⟩ := ht
  have hz : Ψ.symm (F t x) ∈ Ψ.source := Ψ.map_target' htΨ
  have hzval : Ψ (Ψ.symm (F t x)) = F t x := Ψ.right_inv' htΨ
  have heq : Ψ.symm (F t x) = (s, (0 : Fin m → ℝ)) :=
    Φ.toOpenPartialHomeomorph.injOn (hsub hz) hsΦ ((hmap _).symm.trans (hzval.trans hval.symm))
  exact ⟨s, hs, heq ▸ hz, (hmap _).trans hval⟩

attribute [local instance 100] Classical.propDecidable in
/-- A cubic endpoint basin restriction exists. -/
theorem MorseCancellation.exists_cubic_endpoint_basin_restriction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {e : ℝ}
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ z, L (endpointLinearField σ (1 / 2) e z) = MorseHandle.descent (L z))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hc : (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source) (hcenter : Φ (e / 2, 0) = p)
    (hfield : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y)
    (hcoord : ∀ z ∈ Φ.source, c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) e z)) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.source ⊆ Φ.source ∧
        (∀ z, Ψ z = Φ z) ∧
          (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source ∧
            Ψ (e / 2, 0) = p ∧
              Ψ.target ⊆ c.splitChart.source ∧
                (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(1 / 2 : ℝ) ^ 2) y) ∧
                  ∀ z ∈ Ψ.source,
                    (e = 1 →
                        (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atTop (𝓝 p) ↔
                          ∀ i, σ i = -1 → z.2 i = 0)) ∧
                      (e = -1 →
                        (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atBot (𝓝 p) ↔
                          ∀ i, σ i = 1 → z.2 i = 0)) := by
  obtain ⟨r, hr, _, hbasin⟩ := exists_native_morse_basin_block c hf hV F hF hmono heq
  have hct : ContinuousAt c.splitChart p :=
    c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hnear :
    ∀ᶠ y in 𝓝 p, y ∈ c.splitChart.source ∧ ‖(c.splitChart y).1‖ < r ∧ ‖(c.splitChart y).2‖ < r := by
    have hB :
      Metric.ball (0 : c.NegativeCoordinates) r ×ˢ Metric.ball (0 : c.PositiveCoordinates) r ∈
        𝓝 (c.splitChart p) := by
      rw [c.splitChart_center]
      exact
        (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
          ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
    filter_upwards [c.splitChart.open_source.mem_nhds c.splitChart_mem_source,
      hct.eventually hB] with y hy hby
    exact ⟨hy, mem_ball_zero_iff.mp hby.1, mem_ball_zero_iff.mp hby.2⟩
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hnear
  let Ψ := PartialChart.restrictTarget Φ hU
  have hsource : Ψ.source ⊆ Φ.source := fun _ hz => hz.1
  have hΨc : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, 0) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hc, hcenter.symm ▸ hpU⟩
  refine ⟨Ψ, hsource, fun _ => rfl, hΨc, hcenter, fun y hy => (hUsub hy.2).1, ?_, ?_⟩
  · intro y hy
    exact hfield y hy.1
  · intro z hz
    obtain ⟨hy, hn, hp⟩ := hUsub (Ψ.map_source' hz).2
    have hclass := hbasin (Ψ z) hy hn hp
    have hcz : c.splitChart (Ψ z) = L (endpointFieldProduct (1 / 2) e z) := hcoord z (hsource hz)
    constructor
    · intro he
      subst e
      rw [hclass.1, hcz]
      exact incoming_linear_stable_plane c σ hσ L hL (endpointFieldProduct (1 / 2) 1 z)
    · intro he
      subst e
      rw [hclass.2, hcz]
      exact outgoing_linear_unstable_plane c σ hσ L hL (endpointFieldProduct (1 / 2) (-1) z)

attribute [local instance 100] Classical.propDecidable in
/-- An actual incoming cubic basin exists. -/
theorem MorseCancellation.exists_actual_incoming_cubic_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E))
    (he : c.weights (ρ Option.none) = 1) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (1 / 2, 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ z ∈ Φ.source,
                  Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p) ↔
                    ∀ i, σ i = -1 → z.2 i = 0) ∧
                ∀ᶠ t in Filter.atTop,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨Φ, hc, hcenter, _, hfield, htail, L, hL, hcoord⟩ :=
    exists_actual_incoming_cubic_endpoint c ρ he hV F hF hxp hlim heq
  obtain ⟨Ψ, hsub, hmap, hΨc, hΨcenter, htarget, hΨfield, hbasin⟩ :=
    exists_cubic_endpoint_basin_restriction c hf σ (fun i => c.signs _) L hL hV F hF hmono heq Φ
      hc hcenter hfield hcoord
  refine ⟨Ψ, hΨc, hΨcenter, htarget, hΨfield, ?_, ?_⟩
  · exact fun z hz => (hbasin z hz).1 rfl
  · exact endpoint_axis_tail_of_restriction Φ Ψ hsub hmap hΨc hΨcenter F x hlim htail

attribute [local instance 100] Classical.propDecidable in
/-- An actual outgoing cubic basin exists. -/
theorem MorseCancellation.exists_actual_outgoing_cubic_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E))
    (he : c.weights (ρ Option.none) = -1) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (-(1 / 2 : ℝ), 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ z ∈ Φ.source,
                  Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 p) ↔
                    ∀ i, σ i = 1 → z.2 i = 0) ∧
                ∀ᶠ t in Filter.atBot,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨Φ, hc, hcenter, _, hfield, htail, L, hL, hcoord⟩ :=
    exists_actual_outgoing_cubic_endpoint c ρ he hV F hF hxp hlim heq
  have hc' : ((-1 : ℝ) / 2, (0 : Fin m → ℝ)) ∈ Φ.source := by convert! hc using 1; norm_num
  have hcenter' : Φ ((-1 : ℝ) / 2, 0) = p := by convert! hcenter using 1; norm_num
  obtain ⟨Ψ, hsub, hmap, hΨc, hΨcenter, htarget, hΨfield, hbasin⟩ :=
    exists_cubic_endpoint_basin_restriction c hf σ (fun i => c.signs _) L hL hV F hF hmono heq Φ
      hc' hcenter' hfield hcoord
  have hΨc' : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Ψ.source := by convert! hΨc using 1; norm_num
  have hΨcenter' : Ψ (-(1 / 2 : ℝ), 0) = p := by convert! hΨcenter using 1; norm_num
  refine ⟨Ψ, hΨc', hΨcenter', htarget, hΨfield, ?_, ?_⟩
  · exact fun z hz => (hbasin z hz).2 rfl
  · exact endpoint_axis_tail_of_restriction Φ Ψ hsub hmap hΨc' hΨcenter' F x hlim htail

/-! ### Matched connection endpoints -/

attribute [local instance 100] Classical.propDecidable in
/-- Matched connection basin endpoints exist. -/
theorem MorseCancellation.exists_matched_connection_basin_endpoints {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p q : M} (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : Continuous f) {m : ℕ}
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {x : M} (hxp : x ≠ p) (hxq : x ≠ q)
    (hp : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y) :
    ∃ (σ : Fin m → ℝ) (Φp Φq : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧
        (1 / 2, (0 : Fin m → ℝ)) ∈ Φp.source ∧
          Φp (1 / 2, 0) = p ∧
            (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φq.source ∧
              Φq (-(1 / 2 : ℝ), 0) = q ∧
                (∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(1 / 2 : ℝ) ^ 2) y) ∧
                  (∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(1 / 2 : ℝ) ^ 2) y) ∧
                    (∀ z ∈ Φp.source,
                        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 p) ↔
                          ∀ i, σ i = -1 → z.2 i = 0) ∧
                      (∀ z ∈ Φq.source,
                          Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 q) ↔
                            ∀ i, σ i = 1 → z.2 i = 0) ∧
                        (∀ᶠ t in Filter.atTop,
                            ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                              (s, (0 : Fin m → ℝ)) ∈ Φp.source ∧ Φp (s, 0) = F t x) ∧
                          ∀ᶠ t in Filter.atBot,
                            ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                              (s, (0 : Fin m → ℝ)) ∈ Φq.source ∧ Φq (s, 0) = F t x := by
  obtain ⟨ρp, ρq, hρp, hρq, hmatch⟩ :=
    SignedCoordinates.exists_adjacent_sign_enumerations_of_dimension hdim cp.weights
      cq.weights cp.signs cq.signs hindex
  let σ := fun i : Fin m => cp.weights (ρp (Option.some i))
  obtain ⟨Φp, hpc, hpv, _, hpfield, hpbasin, hptail⟩ :=
    exists_actual_incoming_cubic_basin cp hf ρp hρp hV F hF hmono hxp hp heqp
  obtain ⟨Φq, hqc, hqv, _, hqfield, hqbasin, hqtail⟩ :=
    exists_actual_outgoing_cubic_basin cq hf ρq hρq hV F hF hmono hxq hq heqq
  have hsigma : (fun i : Fin m => cq.weights (ρq (Option.some i))) = σ :=
    funext (fun i => (hmatch i).symm)
  rw [hsigma] at hqfield hqbasin
  exact
    ⟨σ, Φp, Φq, fun i => cp.signs _, hpc, hpv, hqc, hqv, hpfield, hqfield, hpbasin, hqbasin,
      hptail, hqtail⟩

attribute [local instance 100] Classical.propDecidable in
/-- Actual connection slice data exists. -/
theorem MorseCancellation.exists_actual_connection_slice_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q x : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : Continuous f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    (hmono : ∀ y, Antitone (fun t => f (F t y))) (hxp : x ≠ p) (hxq : x ≠ q)
    (hp : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hAsource : A.source = U ×ˢ Set.univ) (h0U : 0 ∈ U)
    (hAfield :
      ∀ y ∈ A.target,
        V y =
          FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (hAaxis : ∀ t : ℝ, A (0, t) = F t x) :
    ∃ (σ : Fin m → ℝ) (Ψq Ψp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (B :
      PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞) (Rq Rp Tq Tp : ℝ),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧
        0 < Rq ∧
          0 < Rp ∧
            Ψq (-(1 / 2 : ℝ), 0) = q ∧
              Ψp (1 / 2, 0) = p ∧
                Metric.closedBall (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) Rq ⊆ Ψq.source ∧
                  Metric.closedBall (1 / 2, (0 : Fin m → ℝ)) Rp ⊆ Ψp.source ∧
                    (∀ y ∈ Ψq.target, V y = nativeCubicDescent σ Ψq (-(1 / 2 : ℝ) ^ 2) y) ∧
                      (∀ y ∈ Ψp.target, V y = nativeCubicDescent σ Ψp (-(1 / 2 : ℝ) ^ 2) y) ∧
                        (∀ z ∈ Ψq.source,
                            Filter.Tendsto (fun t => F t (Ψq z)) Filter.atBot (𝓝 q) ↔
                              ∀ i, σ i = 1 → z.2 i = 0) ∧
                          (∀ z ∈ Ψp.source,
                              Filter.Tendsto (fun t => F t (Ψp z)) Filter.atTop (𝓝 p) ↔
                                ∀ i, σ i = -1 → z.2 i = 0) ∧
                            B.source ⊆ A.source ∧
                              B.target ⊆ A.target ∧
                                (∀ z, B z = A z) ∧
                                  (∀ y ∈ B.target,
                                      V y =
                                        FlowConstruction.partialChartField B.symm
                                          (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
                                    Nonempty
                                      (NativeEndpointSliceData σ (1 / 2) Ψq Ψp B Rq Rp Tq Tp) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  obtain
    ⟨σ, Φp, Φq, hσ, hpc, hpv, hqc, hqv, hpfield, hqfield, hpbasin, hqbasin, hptail, hqtail⟩ :=
    exists_matched_connection_basin_endpoints cp cq hf hdim hindex (hV.of_le (by simp)) F hF hmono
      hxp hxq hp hq heqp heqq
  obtain ⟨Ψp, Rp, δp, Tp, hps, hpval, hRp, hδp, hpbox, hpslice, hpf, hpaxis, hplimits⟩ :=
    exists_basin_preserving_endpoint_clock σ ha Φp hV hpfield F hF
      (show (1 / 2 : ℝ) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) by constructor <;> norm_num) rfl hpc x
      (by rw [hpv]; exact hp) hptail
  obtain ⟨Ψq, Rq, δq, Tq, hqs, hqval, hRq, hδq, hqbox, hqslice, hqf, hqaxis, hqlimits⟩ :=
    exists_basin_preserving_endpoint_clock σ ha Φq hV hqfield F hF
      (show (-(1 / 2 : ℝ)) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) by constructor <;> norm_num) (by ring)
      hqc x (by rw [hqv]; exact hq) hqtail
  have hqp : Ψq (cubicFlowCylinder σ (1 / 2) (0, Tq)) = A (0, Tq) :=
    (hqaxis Tq (Metric.ball_subset_closedBall (hqslice 0 (by simpa using hδq.le)))).trans
      (hAaxis Tq).symm
  have hpp : Ψp (cubicFlowCylinder σ (1 / 2) (0, Tp)) = A (0, Tp) :=
    (hpaxis Tp (Metric.ball_subset_closedBall (hpslice 0 (by simpa using hδp.le)))).trans
      (hAaxis Tp).symm
  obtain ⟨B, hBs, hBt, hBmap, hBfield, hdata⟩ :=
    exists_original_endpoint_slice_data σ ha Ψq Ψp A hAsource h0U V hqf hpf hAfield hδq hδp hqbox
      hpbox hqslice hpslice hqp hpp
  refine
    ⟨σ, Ψq, Ψp, B, Rq, Rp, Tq, Tp, hσ, hRq, hRp, hqval.trans hqv, hpval.trans hpv, hqbox, hpbox,
      hqf, hpf, ?_, ?_, hBs, hBt, hBmap, hBfield, hdata⟩
  · intro z hz
    exact (hqlimits z q).2.trans (hqbasin z (hqs ▸ hz))
  · intro z hz
    exact (hplimits z p).1.trans (hpbasin z (hps ▸ hz))

end
