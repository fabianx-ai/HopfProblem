/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.PhaseCylinder

/-!
# Transition maps between flow-box charts

Two flow-box charts `A`, `C` of the same field (in which the field is the constant vertical
field) have a transition map preserving the vertical direction
(`native_field_transition_pushforward`, `native_vertical_transition_derivative`). Such a map
is, on a connected time interval, of the form `(t, z) ↦ (t + c z, P z)`
(`vertical_transition_formula`); near a point of the axis it is `(t, z) ↦ (t + v z, P z)` with
`P` a local diffeomorphism of the transversal and `v` a smooth *phase* vanishing at the axis
(`exists_vertical_transition_phase`, `exists_transverse_transition_chart`,
`exists_native_transition_phase`, `exists_global_native_transition_phase`, and the
time-last variant `exists_time_last_native_transition_phase`).

`exists_native_endpoint_slice_phase`: the slice at time `T` of a cubic chart matches a vertical
flow-box chart `A` of the same field up to such a base map `P` and phase `v`.

cf. Lee, *Introduction to Smooth Manifolds*, Theorem 9.22 (flow-box coordinates are unique up
to a diffeomorphism of the transversal and a time shift).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Transition phases -/

/-- A vertical transition phase exists. -/
theorem FlowSuspension.exists_vertical_transition_phase {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (R : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) (ℝ × Z) (ℝ × Z) ∞)
    (hvertical : ∀ p ∈ R.source, fderiv ℝ R p (1, 0) = (1, 0)) {t₀ : ℝ}
    (hp : (t₀, (0 : Z)) ∈ R.source) (hfix : R (t₀, 0) = (t₀, 0)) :
    ∃ (ε : ℝ) (P : Z → Z) (v : Z → ℝ),
      0 < ε ∧
        ContDiffOn ℝ ∞ P (Metric.ball 0 ε) ∧
          ContDiffOn ℝ ∞ v (Metric.ball 0 ε) ∧
            P 0 = 0 ∧
              v 0 = 0 ∧
                Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ Metric.ball (0 : Z) ε ⊆ R.source ∧
                  ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
                    ∀ z ∈ Metric.ball (0 : Z) ε, R (t, z) = (t + v z, P z) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (R.open_source.mem_nhds hp)
  have hsub : Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ Metric.ball (0 : Z) ε ⊆ R.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    apply hball
    rw [← ball_prod_same]
    refine ⟨?_, hz⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht₀ : t₀ ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  let P : Z → Z := fun z => (R (t₀, z)).2
  let v : Z → ℝ := fun z => (R (t₀, z)).1 - t₀
  have hc : ContDiffOn ℝ ∞ (fun z : Z => R (t₀, z)) (Metric.ball 0 ε) :=
    R.contMDiffOn_toFun.contDiffOn.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z hz => hsub ⟨ht₀, hz⟩)
  refine
    ⟨ε, P, v, hε, contDiff_snd.comp_contDiffOn hc,
      (contDiff_fst.comp_contDiffOn hc).sub contDiffOn_const, ?_, ?_, hsub, ?_⟩
  · change (R (t₀, 0)).2 = 0
    rw [hfix]
  · change (R (t₀, 0)).1 - t₀ = 0
    rw [hfix, sub_self]
  · intro t ht z hz
    exact vertical_transition_formula R hvertical isOpen_Ioo isPreconnected_Ioo hsub ht₀ ht hz

/-- A transverse transition chart exists. -/
theorem FlowSuspension.exists_transverse_transition_chart {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (R : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) (ℝ × Z) (ℝ × Z) ∞)
    (hvertical : ∀ p ∈ R.source, fderiv ℝ R p (1, 0) = (1, 0)) {t₀ : ℝ}
    (hp : (t₀, (0 : Z)) ∈ R.source) (hfix : R (t₀, 0) = (t₀, 0)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧
        (0 : Z) ∈ P.source ∧
          P 0 = 0 ∧
            v 0 = 0 ∧
              ContDiffOn ℝ ∞ v P.source ∧
                Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ P.source ⊆ R.source ∧
                  ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ z ∈ P.source, R (t, z) = (t + v z, P z) := by
  obtain ⟨ε, Q, v, hε, hQ, hv, hQ0, hv0, hsub, hformula⟩ :=
    exists_vertical_transition_phase R hvertical hp hfix
  have ht₀ : t₀ ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hQeq : Q =ᶠ[𝓝 (0 : Z)] (fun z => (R (t₀, z)).2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Z) hε] with z hz
    exact (congrArg Prod.snd (hformula t₀ ht₀ z hz)).symm
  have hRdiff :=
    (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds hp)).differentiableAt
      (by simp)
  have hι : HasFDerivAt (fun z : Z => (t₀, z)) (ContinuousLinearMap.inr ℝ ℝ Z) 0 := by
    exact (hasFDerivAt_const t₀ (0 : Z)).prodMk (hasFDerivAt_id (0 : Z))
  have hslice :
    HasFDerivAt (fun z : Z => (R (t₀, z)).2)
      (AxisCoordinates.transverseBlock (fderiv ℝ R (t₀, 0))) 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := R (t₀, 0))).comp 0 (hRdiff.hasFDerivAt.comp 0 hι)
  have hfull : (fderiv ℝ R (t₀, 0)).IsInvertible := by
    have hl : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) ∞ R (t₀, 0) := ⟨R, hp, fun _ _ => rfl⟩
    refine ⟨hl.mfderivToContinuousLinearEquiv (by simp), ?_⟩
    have he := hl.mfderivToContinuousLinearEquiv_coe (by simp)
    rw [mfderiv_eq_fderiv] at he
    exact he
  have hQinv : (fderiv ℝ Q 0).IsInvertible := by
    rw [hQeq.fderiv_eq, hslice.fderiv]
    exact AxisCoordinates.isInvertible_transverseBlock _ (hvertical (t₀, 0) hp) hfull
  obtain ⟨P, hP0, hPsub, hPmap⟩ :=
    exists_partialDiffeomorph_of_contDiffOn Metric.isOpen_ball (Metric.mem_ball_self hε)
      hQ hQinv
  refine ⟨ε, P, v, hε, hP0, ?_, hv0, hv.mono hPsub, ?_, ?_⟩
  · rw [hPmap]
    exact hQ0
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact hsub ⟨ht, hPsub hz⟩
  · intro t ht z hz
    rw [hPmap]
    exact hformula t ht z (hPsub hz)

/-- A native transition phase exists. -/
theorem FlowSuspension.exists_native_transition_phase {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A C : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA :
      ∀ x ∈ A.target,
        V x = FlowConstruction.partialChartField A.symm (fun _ : ℝ × Z => (1, 0)) x)
    (hC :
      ∀ x ∈ C.target,
        V x = FlowConstruction.partialChartField C.symm (fun _ : ℝ × Z => (1, 0)) x)
    {t₀ : ℝ} (hpA : (t₀, (0 : Z)) ∈ A.source) (hpC : (t₀, (0 : Z)) ∈ C.source)
    (hpoint : A (t₀, 0) = C (t₀, 0)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧
        (0 : Z) ∈ P.source ∧
          P 0 = 0 ∧
            v 0 = 0 ∧
              ContDiffOn ℝ ∞ v P.source ∧
                ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
                  ∀ z ∈ P.source,
                    (t, z) ∈ A.source ∧ (t + v z, P z) ∈ C.source ∧ A (t, z) = C (t + v z, P z) :=
  by
  let R := A.trans C.symm
  have hp : (t₀, (0 : Z)) ∈ R.source := by
    refine ⟨hpA, ?_⟩
    change A (t₀, 0) ∈ C.target
    rw [hpoint]
    exact C.map_source' hpC
  have hfix : R (t₀, 0) = (t₀, 0) := by
    change C.symm (A (t₀, 0)) = (t₀, 0)
    rw [hpoint]
    exact C.left_inv' hpC
  have hvertical (p : ℝ × Z) (hp : p ∈ R.source) : fderiv ℝ R p (1, 0) = (1, 0) :=
    native_vertical_transition_derivative A C V hA hC hp
  obtain ⟨ε, P, v, hε, hP0, hPzero, hv0, hv, hsub, hformula⟩ :=
    exists_transverse_transition_chart R hvertical hp hfix
  refine ⟨ε, P, v, hε, hP0, hPzero, hv0, hv, ?_⟩
  intro t ht z hz
  have hpR : (t, z) ∈ R.source := hsub ⟨ht, hz⟩
  have hmap : C.symm (A (t, z)) = (t + v z, P z) := hformula t ht z hz
  refine ⟨hpR.1, ?_, ?_⟩
  · have hh : C.symm (A (t, z)) ∈ C.source := C.map_target' hpR.2
    rwa [hmap] at hh
  · have hh : C (C.symm (A (t, z))) = A (t, z) := C.right_inv' hpR.2
    rw [hmap] at hh
    exact hh.symm

/-- A global native transition phase exists. -/
theorem FlowSuspension.exists_global_native_transition_phase {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A C : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA :
      ∀ x ∈ A.target,
        V x = FlowConstruction.partialChartField A.symm (fun _ : ℝ × Z => (1, 0)) x)
    (hC :
      ∀ x ∈ C.target,
        V x = FlowConstruction.partialChartField C.symm (fun _ : ℝ × Z => (1, 0)) x)
    {t₀ : ℝ} (hpA : (t₀, (0 : Z)) ∈ A.source) (hpC : (t₀, (0 : Z)) ∈ C.source)
    (hpoint : A (t₀, 0) = C (t₀, 0)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧
        (0 : Z) ∈ P.source ∧
          P 0 = 0 ∧
            v 0 = 0 ∧
              ContDiff ℝ ∞ v ∧
                ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
                  ∀ z ∈ P.source,
                    (t, z) ∈ A.source ∧ (t + v z, P z) ∈ C.source ∧ A (t, z) = C (t + v z, P z) :=
  by
  obtain ⟨ε, P, v, hε, hP0, hPzero, hv0, hv, hformula⟩ :=
    exists_native_transition_phase A C V hA hC hpA hpC hpoint
  have hzero : ({0} : Set Z) ⊆ P.source := Set.singleton_subset_iff.mpr hP0
  obtain ⟨g, hg, W, hW, h0W, hWsub, heq⟩ :=
    LineBundleTransport.exists_smooth_extension_near_closed isClosed_singleton P.open_source hzero
      hv
  let Q := PartialChart.restrictSource P hW
  have hQ0 : (0 : Z) ∈ Q.source := ⟨hP0, h0W (Set.mem_singleton 0)⟩
  have hg0 : g 0 = 0 := (heq (h0W (Set.mem_singleton 0))).trans hv0
  refine ⟨ε, Q, g, hε, hQ0, hPzero, hg0, hg, ?_⟩
  intro t ht z hz
  have hh := hformula t ht z hz.1
  change (t, z) ∈ A.source ∧ (t + g z, P z) ∈ C.source ∧ A (t, z) = C (t + g z, P z)
  rw [heq hz.2]
  exact hh

/-- A latest-time native transition phase exists. -/
theorem FlowSuspension.exists_time_last_native_transition_phase {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA :
      ∀ x ∈ A.target,
        V x = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) x)
    (hC :
      ∀ x ∈ C.target,
        V x = FlowConstruction.partialChartField C.symm (fun _ : Z × ℝ => (0, 1)) x)
    {T : ℝ} (hpA : ((0 : Z), T) ∈ A.source) (hpC : ((0 : Z), T) ∈ C.source)
    (hpoint : A (0, T) = C (0, T)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧
        (0 : Z) ∈ P.source ∧
          P 0 = 0 ∧
            v 0 = 0 ∧
              ContDiff ℝ ∞ v ∧
                ∀ t ∈ Set.Ioo (T - ε) (T + ε),
                  ∀ z ∈ P.source,
                    (z, t) ∈ A.source ∧ (P z, t + v z) ∈ C.source ∧ A (z, t) = C (P z, t + v z) :=
  by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ Z
  let D := e.toDiffeomorph.toPartialDiffeomorph
  have hpush (p : ℝ × Z) (_ : p ∈ D.source) : fderiv ℝ D p (1, 0) = ((0 : Z), (1 : ℝ)) := by
    change fderiv ℝ e p (1, 0) = ((0 : Z), (1 : ℝ))
    rw [e.fderiv]
    rfl
  have hfield (B : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    (hB :
      ∀ x ∈ B.target,
        V x = FlowConstruction.partialChartField B.symm (fun _ : Z × ℝ => (0, 1)) x) :
    ∀ x ∈ (D.trans B).target,
      V x =
        FlowConstruction.partialChartField (D.trans B).symm (fun _ : ℝ × Z => (1, 0)) x := by
    intro x hx
    exact
      (hB x hx.1).trans
        (MorseCancellation.partialChartField_of_model_conjugacy D B (fun _ : ℝ × Z => (1, 0))
            (fun _ : Z × ℝ => (0, 1)) hpush hx).symm
  have hAs : (T, (0 : Z)) ∈ (D.trans A).source := ⟨Set.mem_univ _, hpA⟩
  have hCs : (T, (0 : Z)) ∈ (D.trans C).source := ⟨Set.mem_univ _, hpC⟩
  obtain ⟨ε, P, v, hε, hP0, hPfix, hv0, hv, hformula⟩ :=
    exists_global_native_transition_phase (D.trans A) (D.trans C) V (hfield A hA) (hfield C hC)
      hAs hCs hpoint
  refine ⟨ε, P, v, hε, hP0, hPfix, hv0, hv, ?_⟩
  intro t ht z hz
  have hh := hformula t ht z hz
  exact ⟨hh.1.2, hh.2.1.2, hh.2.2⟩

/-- A native endpoint slice phase exists. -/
theorem FlowSuspension.exists_native_endpoint_slice_phase {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, MorseCancellation.Model m) 𝓘(ℝ, E) (MorseCancellation.Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : A.source = U ×ˢ Set.univ) (h0U : 0 ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hΦ : ∀ y ∈ Φ.target, V y = MorseCancellation.nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (hA :
      ∀ y ∈ A.target,
        V y =
          FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    {c r δ T : ℝ} (hδ : 0 < δ) (hbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source)
    (hslice :
      ∀ z : Fin m → ℝ,
        ‖z‖ ≤ δ → MorseCancellation.cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r)
    (hpoint : Φ (MorseCancellation.cubicFlowCylinder σ a (0, T)) = A (0, T)) :
    ∃ (P : PartialDiffeomorph 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin m → ℝ) (Fin m → ℝ) (Fin m → ℝ) ∞) (v :
      (Fin m → ℝ) → ℝ),
      (0 : Fin m → ℝ) ∈ P.source ∧
        P 0 = 0 ∧
          v 0 = 0 ∧
            ContDiff ℝ ∞ v ∧
              P.target ⊆ U ∧
                (∀ z ∈ P.source,
                    MorseCancellation.cubicFlowCylinder σ a (z, T) ∈
                      Metric.closedBall (c, (0 : Fin m → ℝ)) r) ∧
                  ∀ z ∈ P.source,
                    Φ (MorseCancellation.cubicFlowCylinder σ a (z, T)) = A (P z, T + v z) := by
  let C := MorseCancellation.cubicFlowCylinderChart σ ha
  let B := C.trans Φ
  have hB0 : ((0 : Fin m → ℝ), T) ∈ B.source :=
    ⟨Set.mem_univ _, hbox (Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le)))⟩
  have hBfield :
    ∀ y ∈ B.target,
      V y =
        FlowConstruction.partialChartField B.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y := by
    intro y hy
    exact
      (hΦ y hy.1).trans
        (MorseCancellation.partialChartField_of_model_conjugacy C Φ (fun _ : (Fin m → ℝ) × ℝ => (0, 1))
            (MorseCancellation.cubicDescent σ (-(a ^ 2)))
            (fun p _ => MorseCancellation.cubicFlowCylinder_pushforward_vertical σ a p) hy).symm
  have hA0 : ((0 : Fin m → ℝ), T) ∈ A.source := by
    rw [hsource]
    exact ⟨h0U, Set.mem_univ _⟩
  obtain ⟨ε, P, v, hε, hP0, hPfix, hv0, hv, hformula⟩ :=
    exists_time_last_native_transition_phase B A V hBfield hA hB0 hA0 hpoint
  let Q :=
    PartialChart.restrictSource P
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Fin m → ℝ) δ))
  have hT : T ∈ Set.Ioo (T - ε) (T + ε) := ⟨by linarith, by linarith⟩
  have hQ0 : (0 : Fin m → ℝ) ∈ Q.source := ⟨hP0, Metric.mem_ball_self hδ⟩
  refine ⟨Q, v, hQ0, hPfix, hv0, hv, ?_, ?_, ?_⟩
  · intro z hz
    have hu := Q.map_target' hz
    have hh := (hformula T hT (Q.symm z) hu.1).2.1
    rw [hsource] at hh
    have hi : P (Q.symm z) = z := Q.right_inv' hz
    exact hi ▸ hh.1
  · intro z hz
    exact
      Metric.ball_subset_closedBall
        (hslice z (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz.2)))
  · intro z hz
    exact (hformula T hT z hz.1).2.2

end
