/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Connection.LevelHolonomy
import Lib.Geometry.Manifold.Morse.Connection.TimeChange

/-!
# Flow-box charts of a connecting orbit with a phase

A vertical flow-box chart of a flow `F` is a chart `A` on `U × ℝ` with
`F t (A (z, s)) = A (z, s + t)`; a transverse slice through it may be given by a base
reparametrisation `Q` and a *phase* `v`: `S u = A (Q u, T + v u)`.

* `phase_slice_flow_coordinates`, `phase_flow_sheet_contMDiffAt`,
  `phase_flow_subsheet_properties`, `exists_phase_flow_basin_chart`,
  `phase_flow_chart_subsheet_germ`: the sheet `(t, u) ↦ F (t - T) (S u)` is smooth and is
  itself a flow-box chart, with basins read off on the base.
* `phaseCylinderChart Q v hv`: the chart `(u, t) ↦ (Q u, t + v u)` of `Z × ℝ`
  (`phaseCylinderChart_target`, `phaseCylinderChart_vertical`), and
  `exists_native_phase_cylinder`: reparametrising the base of a vertical chart by `Q` and `v`
  keeps the field vertical.
* `native_flow_chart_vertical`, `exists_euclidean_level_flow_cylinder`: the chart
  `(y, t) ↦ F t (ι y)` around a point of a regular level, with Euclidean base, is a vertical
  flow-box chart.
* `exists_arbitrary_gap_flow_cylinder`, `exists_normalized_connection_cylinder`: after a time
  change, a unique connecting orbit from `q` to `p` has a vertical flow-box chart `A` on
  `U × ℝ` with axis `A (0, t) = G t x₀` and height `f (A (z, t)) = b - r t` for `t ∈ [0, 1]`,
  with the same orbits, limits and unique connection as before.
* `cubicFlowCylinder_pushforward_vertical`: the cubic cylinder coordinates push the vertical
  field to the cubic descent field.

cf. Lee, *Introduction to Smooth Manifolds*, Theorem 9.22 (canonical form of a vector field
near a regular point), and Milnor, *Lectures on the h-cobordism theorem*, §5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Phase cylinder charts -/

/-- The phase slice flow coordinates. -/
theorem FlowSuspension.phase_slice_flow_coordinates {D Z E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : A.source = U ×ˢ Set.univ) (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U) (S : D → M) (v : D → ℝ)
    (T : ℝ) (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) :
    ∀ u ∈ Q.source,
      ∀ t : ℝ, F (t - T) (S u) = A (Q u, t + v u) ∧ A.symm (F (t - T) (S u)) = (Q u, t + v u) := by
  intro u hu t
  have hq := hQU (Q.map_source' hu)
  have hh : F (t - T) (S u) = A (Q u, t + v u) := by
    rw [hphase u hu, hflow (Q u) hq]
    exact congrArg (fun s : ℝ => A (Q u, s)) (by ring)
  refine ⟨hh, ?_⟩
  rw [hh]
  apply A.left_inv'
  rw [hsource]
  exact ⟨hq, Set.mem_univ _⟩

/-- The phase flow sheet is smooth. -/
theorem FlowSuspension.phase_flow_sheet_contMDiffAt {D Z E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : A.source = U ×ˢ Set.univ) (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U) (h0 : (0 : D) ∈ Q.source)
    (hQ0 : Q 0 = 0) (S : D → M) (v : D → ℝ) (T : ℝ) (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) :
    ContMDiffAt 𝓘(ℝ, ℝ × D) 𝓘(ℝ, E) ∞ (fun w : ℝ × D => F (w.1 - T) (S w.2)) 0 := by
  have h0U : (0 : Z) ∈ U := hQ0 ▸ hQU (Q.map_source' h0)
  have h0A : ((0 : Z), (0 : ℝ)) ∈ A.source := by
    rw [hsource]
    exact ⟨h0U, Set.mem_univ _⟩
  have hQ : ContDiffAt ℝ ∞ Q (0 : D) :=
    Q.contMDiffOn_toFun.contDiffOn.contDiffAt (Q.open_source.mem_nhds h0)
  have hparam : ContDiffAt ℝ ∞ (fun w : ℝ × D => (Q w.2, w.1 + v w.2)) 0 :=
    (hQ.comp (f := fun w : ℝ × D => w.2) 0 contDiffAt_snd).prodMk
      (contDiffAt_fst.add (hv.contDiffAt.comp (f := fun w : ℝ × D => w.2) 0 contDiffAt_snd))
  have hAparam : (Q ((0 : ℝ × D).2), (0 : ℝ × D).1 + v (0 : ℝ × D).2) ∈ A.source := by
    simpa only [Prod.fst_zero, Prod.snd_zero, hQ0, hv0, add_zero] using h0A
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ × D) 𝓘(ℝ, E) ∞ (fun w : ℝ × D => A (Q w.2, w.1 + v w.2)) 0 :=
    (A.contMDiffOn_toFun.contMDiffAt (A.open_source.mem_nhds hAparam)).comp (f := fun w : ℝ × D =>
      (Q w.2, w.1 + v w.2)) 0 hparam.contMDiffAt
  have hnear : ∀ᶠ w : ℝ × D in 𝓝 0, w.2 ∈ Q.source :=
    continuous_snd.continuousAt.eventually (Q.open_source.mem_nhds h0)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  exact (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase w.2 hw w.1).1

/-- The phase flow subsheet's properties. -/
theorem FlowSuspension.phase_flow_subsheet_properties {D Z E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : A.source = U ×ˢ Set.univ) (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U) (h0 : (0 : D) ∈ Q.source)
    (hQ0 : Q 0 = 0) (S : D → M) (v : D → ℝ) (T : ℝ) (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) (L : B →L[ℝ] D) :
    ContMDiffAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) ∞ (fun w : ℝ × B => F (w.1 - T) (S (L w.2))) 0 ∧
      F (-T) (S (L 0)) = A 0 ∧
        (fun w : ℝ × B => (A.symm (F (w.1 - T) (S (L w.2)))).1) =ᶠ[𝓝 0]
          (fun w : ℝ × B => Q (L w.2)) := by
  have hbase := phase_flow_sheet_contMDiffAt A hsource F hflow Q hQU h0 hQ0 S v T hv hv0 hphase
  have hparam : ContDiff ℝ ∞ (fun w : ℝ × B => (w.1, L w.2)) :=
    contDiff_fst.prodMk (L.contDiff.comp contDiff_snd)
  have hparam0 : ((0 : ℝ × B).1, L (0 : ℝ × B).2) = (0 : ℝ × D) := by simp
  have hbase' :
    ContMDiffAt 𝓘(ℝ, ℝ × D) 𝓘(ℝ, E) ∞ (fun w : ℝ × D => F (w.1 - T) (S w.2))
      ((0 : ℝ × B).1, L (0 : ℝ × B).2) := by
    rw [hparam0]
    exact hbase
  refine ⟨hbase'.comp (f := fun w : ℝ × B => (w.1, L w.2)) 0 hparam.contMDiff.contMDiffAt, ?_, ?_⟩
  · have hh := (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase 0 h0 0).1
    change F (-T) (S (L 0)) = A ((0 : Z), (0 : ℝ))
    simpa only [map_zero, zero_sub, zero_add, hQ0, hv0] using hh
  · have hnear : ∀ᶠ w : ℝ × B in 𝓝 0, L w.2 ∈ Q.source :=
      (L.continuous.comp continuous_snd).continuousAt.eventually
        (Q.open_source.mem_nhds (by simpa using h0))
    filter_upwards [hnear] with w hw
    exact
      congrArg Prod.fst
        (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase (L w.2) hw w.1).2

/-- The phase cylinder chart. -/
def FlowSuspension.phaseCylinderChart {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (v : E → ℝ) (hv : ContDiff ℝ ∞ v) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, Z × ℝ) (E × ℝ) (Z × ℝ) ∞ := by
  have hQ : ContDiffOn ℝ ∞ (fun p : E × ℝ => Q p.1) (Q.source ×ˢ Set.univ) :=
    Q.contMDiffOn_toFun.contDiffOn.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hQi : ContDiffOn ℝ ∞ (fun p : Z × ℝ => Q.symm p.1) (Q.target ×ˢ Set.univ) :=
    Q.contMDiffOn_invFun.contDiffOn.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  refine
    { toFun := fun p => (Q p.1, p.2 + v p.1)
      invFun := fun p => (Q.symm p.1, p.2 - v (Q.symm p.1))
      source := Q.source ×ˢ Set.univ
      target := Q.target ×ˢ Set.univ
      map_source' := fun p hp => ⟨Q.map_source' hp.1, Set.mem_univ _⟩
      map_target' := fun p hp => ⟨Q.map_target' hp.1, Set.mem_univ _⟩
      left_inv' := ?_
      right_inv' := ?_
      open_source := Q.open_source.prod isOpen_univ
      open_target := Q.open_target.prod isOpen_univ
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · intro p hp
    have hi : Q.symm (Q p.1) = p.1 := Q.left_inv' hp.1
    change (Q.symm (Q p.1), p.2 + v p.1 - v (Q.symm (Q p.1))) = p
    rw [hi, add_sub_cancel_right]
  · intro p hp
    have hi : Q (Q.symm p.1) = p.1 := Q.right_inv' hp.1
    change (Q (Q.symm p.1), p.2 - v (Q.symm p.1) + v (Q.symm p.1)) = p
    rw [hi, sub_add_cancel]
  · exact (hQ.prodMk (contDiff_snd.contDiffOn.add (hv.comp contDiff_fst).contDiffOn)).contMDiffOn
  · exact
      (hQi.prodMk
          (contDiff_snd.contDiffOn.sub
            (hv.contDiffOn.comp hQi (Set.mapsTo_univ _ _)))).contMDiffOn

/-- The phase cylinder chart's target. -/
theorem FlowSuspension.phaseCylinderChart_target {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (v : E → ℝ) (hv : ContDiff ℝ ∞ v) :
    (phaseCylinderChart Q v hv).target = Q.target ×ˢ Set.univ :=
  rfl

/-- The phase cylinder chart is vertical. -/
theorem FlowSuspension.phaseCylinderChart_vertical {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (v : E → ℝ) (hv : ContDiff ℝ ∞ v) {p : E × ℝ}
    (hp : p ∈ (phaseCylinderChart Q v hv).source) :
    fderiv ℝ (phaseCylinderChart Q v hv) p (0, 1) = (0, 1) := by
  let R := phaseCylinderChart Q v hv
  have hdiff :=
    (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds hp)).differentiableAt
      (by simp)
  have hcurve : HasDerivAt (fun t : ℝ => (p.1, p.2 + t)) (0, 1) 0 :=
    (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2)
  have hdiff' : HasFDerivAt R (fderiv ℝ R p) (p.1, p.2 + 0) := by
    simpa only [add_zero, Prod.mk.eta] using hdiff.hasFDerivAt
  have hd := hdiff'.comp_hasDerivAt (0 : ℝ) hcurve
  have hd' : HasDerivAt (fun t : ℝ => (Q p.1, p.2 + t + v p.1)) (fderiv ℝ R p (0, 1)) 0 := by
    convert! hd using 1
  have he : HasDerivAt (fun t : ℝ => (Q p.1, p.2 + t + v p.1)) (0, 1) 0 :=
    (hasDerivAt_const 0 (Q p.1)).prodMk
      (((hasDerivAt_id (0 : ℝ)).const_add p.2).add_const (v p.1))
  exact hd'.unique he

/-- A phase flow basin chart exists. -/
theorem FlowSuspension.exists_phase_flow_basin_chart {D Z E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : A.source = U ×ˢ Set.univ) (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U) (h0 : (0 : D) ∈ Q.source)
    (hQ0 : Q 0 = 0) (S : D → M) (v : D → ℝ) (T : ℝ) (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) (Basin : M → Prop)
    (hshift : ∀ t x, Basin (F t x) ↔ Basin x) (R : D → Prop)
    (hbasin : ∀ u ∈ Q.source, Basin (S u) ↔ R u) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, D × ℝ) 𝓘(ℝ, E) (D × ℝ) M ∞,
      P.source = Q.source ×ˢ Set.univ ∧
        (0 : D × ℝ) ∈ P.source ∧
          P 0 = A 0 ∧
            (∀ u ∈ Q.source, ∀ t, P (u, t) = F (t - T) (S u)) ∧
              ∀ w ∈ P.source, Basin (P w) ↔ R w.1 := by
  let C := phaseCylinderChart Q v hv
  let P := C.trans A
  have hPsource : P.source = Q.source ×ˢ Set.univ := by
    ext w
    change (w ∈ Q.source ×ˢ Set.univ ∧ (Q w.1, w.2 + v w.1) ∈ A.source) ↔ w ∈ Q.source ×ˢ Set.univ
    constructor
    · exact And.left
    · intro hw
      refine ⟨hw, ?_⟩
      rw [hsource]
      exact ⟨hQU (Q.map_source' hw.1), Set.mem_univ _⟩
  have hP0 : (0 : D × ℝ) ∈ P.source := by
    rw [hPsource]
    exact ⟨h0, Set.mem_univ _⟩
  have hPzero : P 0 = A 0 := by
    change A (Q 0, 0 + v 0) = A (0, 0)
    rw [hQ0, hv0, zero_add]
  have hPflow (u : D) (hu : u ∈ Q.source) (t : ℝ) : P (u, t) = F (t - T) (S u) :=
    (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase u hu t).1.symm
  refine ⟨P, hPsource, hP0, hPzero, hPflow, ?_⟩
  intro w hw
  rw [hPsource] at hw
  rw [show P w = F (w.2 - T) (S w.1) from hPflow w.1 hw.1 w.2]
  exact (hshift (w.2 - T) (S w.1)).trans (hbasin w.1 hw.1)

/-- The phase flow chart's subsheet germ. -/
theorem FlowSuspension.phase_flow_chart_subsheet_germ {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : PartialDiffeomorph 𝓘(ℝ, D × ℝ) 𝓘(ℝ, E) (D × ℝ) M ∞) {O : Set D} (hO : IsOpen O)
    (h0 : (0 : D) ∈ O) (F : Flow ℝ M) (S : D → M) (T : ℝ)
    (hformula : ∀ u ∈ O, ∀ t, P (u, t) = F (t - T) (S u)) (L : B →L[ℝ] D) :
    (fun w : ℝ × B => F (w.1 - T) (S (L w.2))) =ᶠ[𝓝 0] (fun w : ℝ × B => P (L w.2, w.1)) := by
  have hnear : ∀ᶠ w : ℝ × B in 𝓝 0, L w.2 ∈ O :=
    (L.continuous.comp continuous_snd).continuousAt.eventually
      (hO.mem_nhds (by simpa only [Function.comp_apply, Prod.snd_zero, map_zero] using h0))
  filter_upwards [hnear] with w hw
  exact (hformula (L w.2) hw w.1).symm

/-- The native flow is vertical in the chart. -/
theorem FlowCancellation.native_flow_chart_vertical {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × ℝ) 𝓘(ℝ, E) (D × ℝ) M ∞) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ι : D → M)
    (hformula : ∀ p : D × ℝ, Φ p = F p.2 (ι p.1)) :
    ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm (fun _ => (0, 1)) x := by
  intro x hx
  let p := Φ.symm x
  have hp : p ∈ Φ.source := Φ.map_target' hx
  let α : ℝ → D × ℝ := fun t => (p.1, t)
  have hα : HasDerivAt α ((0 : D), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hd :=
    FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm (fun _ : D × ℝ => (0, 1)) hα
      hp
  have heq : Φ.symm.symm ∘ α = fun t => F t (ι p.1) := funext (fun t => hformula (p.1, t))
  rw [heq] at hd
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (FlowConstruction.partialChartField Φ.symm (fun _ : D × ℝ => (0, 1)) (Φ p))) at hd
  rw [hformula p] at hd
  have hpF : F p.2 (ι p.1) = x := (hformula p).symm.trans (Φ.right_inv' hx)
  have hh := (hcurve (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
  have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) => L (1 : ℝ)) hh
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
  change
    V (F p.2 (ι p.1)) =
      FlowConstruction.partialChartField Φ.symm (fun _ : D × ℝ => (0, 1))
        (F p.2 (ι p.1)) at hv
  rw [hpF] at hv
  exact hv

/-- A Euclidean level flow cylinder exists. -/
theorem FlowCancellation.exists_euclidean_level_flow_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M} (hx : f x = c) :
    ∃ (U : Set (RegularLevel.Model E)) (ι : RegularLevel.Model E → M) (Φ :
      PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E × ℝ) 𝓘(ℝ, E)
        (RegularLevel.Model E × ℝ) M ∞),
      IsOpen U ∧
        (0 : RegularLevel.Model E) ∈ U ∧
          ι 0 = x ∧
            Φ.source = U ×ˢ Set.univ ∧
              (∀ y ∈ U, f (ι y) = c) ∧
                (∀ p, Φ p = F p.2 (ι p.1)) ∧
                  ∀ y ∈ Φ.target,
                    V y = FlowConstruction.partialChartField Φ.symm (fun _ => (0, 1)) y := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let z : { x : M // f x = c } := ⟨x, hx⟩
  obtain ⟨C, hCsource, -, hCformula, -⟩ :=
    exists_native_level_flow_cylinder hf hreg hV F hcurve hboundary z
  let Q := NativeParametrization.centered (D := RegularLevel.Model E) z
  have hz : (0 : RegularLevel.Model E) ∈ Q.source :=
    NativeParametrization.zero_mem_centered_source z
  let A := PartialChart.prod Q (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  let P := (PartialChart.vectorProduct (RegularLevel.Model E) ℝ).toPartialDiffeomorph
  let Φ := (P.trans A).trans C
  let ι : RegularLevel.Model E → M := fun y => Q y
  have hsource : Φ.source = Q.source ×ˢ Set.univ := by
    ext p
    change (p ∈ Set.univ ∧ (p.1 ∈ Q.source ∧ p.2 ∈ Set.univ)) ∧ A (P p) ∈ C.source ↔ _
    rw [hCsource]
    simp only [Set.mem_univ, true_and, and_true, Set.mem_prod]
  have hformula (p : RegularLevel.Model E × ℝ) : Φ p = F p.2 (ι p.1) := hCformula (A (P p))
  refine
    ⟨Q.source, ι, Φ, Q.open_source, hz, ?_, hsource, fun y _ => (Q y).property, hformula,
      native_flow_chart_vertical Φ F hcurve ι hformula⟩
  exact congrArg Subtype.val (NativeParametrization.centered_zero z)

/-- A native phase cylinder exists. -/
theorem FlowSuspension.exists_native_phase_cylinder {Z E B M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (hQtarget : Q.target = U) (v : E → ℝ) (hv : ContDiff ℝ ∞ v)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hmodel :
      ∀ y ∈ Φ.target,
        V y = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) y) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
      Ψ.source = Q.source ×ˢ Set.univ ∧
        Ψ.target = Φ.target ∧
          (∀ p, Ψ p = Φ (Q p.1, p.2 + v p.1)) ∧
            ∀ y ∈ Ψ.target,
              V y = FlowConstruction.partialChartField Ψ.symm (fun _ : E × ℝ => (0, 1)) y :=
  by
  let R := phaseCylinderChart Q v hv
  let Ψ := R.trans Φ
  have hRtarget : R.target = Φ.source := by rw [phaseCylinderChart_target, hQtarget, hsource]
  have hΨsource : Ψ.source = Q.source ×ˢ Set.univ := by
    ext p
    change (p ∈ R.source ∧ R p ∈ Φ.source) ↔ p ∈ Q.source ×ˢ Set.univ
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, hRtarget ▸ R.map_source' hp⟩
  have hΨtarget : Ψ.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ R.target) ↔ y ∈ Φ.target
    constructor
    · exact And.left
    · exact fun hy => ⟨hy, hRtarget.symm ▸ Φ.map_target' hy⟩
  refine ⟨Ψ, hΨsource, hΨtarget, fun _ => rfl, ?_⟩
  intro y hy
  rw [hmodel y (hΨtarget ▸ hy)]
  exact
    (MorseCancellation.partialChartField_of_model_conjugacy R Φ (fun _ : E × ℝ => (0, 1))
        (fun _ : Z × ℝ => (0, 1)) (fun p hp => phaseCylinderChart_vertical Q v hv hp) hy).symm

/-- A flow cylinder with an arbitrary gap exists. -/
theorem FlowTimeChange.exists_arbitrary_gap_flow_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    {x : M} (hx : f x = c) :
    ∃ (r : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M) (U : Set (Fin m → ℝ)) (Φ :
      PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞),
      0 < r ∧
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
            (∀ y, W y = 0 ↔ V y = 0) ∧
              (∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
                (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ z in 𝓝 y, W z = V z) ∧
                  (∀ y,
                      Set.range (fun t => G t y) = Set.range (fun t => F t y) ∧
                        (∀ p,
                            Filter.Tendsto (fun t => G t y) Filter.atTop (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                          ∀ p,
                            Filter.Tendsto (fun t => G t y) Filter.atBot (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                    IsOpen U ∧
                      (0 : Fin m → ℝ) ∈ U ∧
                        Φ.source = U ×ˢ Set.univ ∧
                          (∀ t : ℝ, Φ (0, t) = G t x) ∧
                            (∀ z ∈ Φ.source, z.2 ∈ Set.Icc (0 : ℝ) 1 → f (Φ z) = c - r * z.2) ∧
                              ∀ y ∈ Φ.target,
                                W y =
                                  FlowConstruction.partialChartField Φ.symm
                                    (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y := by
  let r : ℝ := (c - a) / 2
  have hr : 0 < r := div_pos (sub_pos.mpr ha) (by norm_num)
  let g : M → ℝ := fun y => f y / r
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g := hf.div_const r
  have hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f :=
    criticalPoints_height_div_const hf hr.ne'
  have hdescent :
    ∀ y, y ∉ ManifoldMorse.criticalPoints E g → mvfderiv 𝓘(ℝ, E) g y (V y) < 0 := by
    intro y hy
    rw [hcrit] at hy
    exact
      (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (V y)).mpr (hdesc y hy)
  have hregular :
    ∀ y, g y ∈ Set.Icc (a / r) (b / r) → y ∉ ManifoldMorse.criticalPoints E g := by
    intro y hy
    rw [hcrit]
    exact
      hband y ⟨(div_le_div_iff_of_pos_right hr).mp hy.1, (div_le_div_iff_of_pos_right hr).mp hy.2⟩
  obtain ⟨H, W, G, hH, hIH, hW, hG, hzero, hneg, hspeed, hgerms, _, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hg hV hdescent F hF hregular
  have hc : c / r ∈ Set.Icc (a / r) (b / r) :=
    ⟨div_le_div_of_nonneg_right ha.le hr.le, div_le_div_of_nonneg_right hb.le hr.le⟩
  have hreg (y : M) (hy : g y = c / r) : y ∉ ManifoldMorse.criticalPoints E g :=
    hregular y (hy ▸ hc)
  have hboundary (y : M) (hy : g y = c / r) : mvfderiv 𝓘(ℝ, E) g y (W y) < 0 := by
    rw [hspeed y (hy ▸ hIH hc)]
    norm_num
  obtain ⟨O, ι, A, hO, h0O, hι0, hAsource, hlevel, hAmap, hAfield⟩ :=
    FlowCancellation.exists_euclidean_level_flow_cylinder hg hreg hW G hG hboundary
      (show g x = c / r by change f x / r = c / r; rw [hx])
  let e : (Fin m → ℝ) ≃L[ℝ] RegularLevel.Model E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [RegularLevel.Model, hdim])
  let Q := PartialChart.restrictTarget e.toDiffeomorph.toPartialDiffeomorph hO
  have hQtarget : Q.target = O := by
    ext z
    change (z ∈ (Set.univ : Set (RegularLevel.Model E)) ∧ z ∈ O) ↔ z ∈ O
    simp only [Set.mem_univ, true_and]
  have hQ0 : (0 : Fin m → ℝ) ∈ Q.source := by
    change (0 : Fin m → ℝ) ∈ Set.univ ∧ e 0 ∈ O
    rw [map_zero]
    exact ⟨Set.mem_univ _, h0O⟩
  obtain ⟨Φ, hΦsource, _, hΦmap, hΦfield⟩ :=
    FlowSuspension.exists_native_phase_cylinder A hAsource Q hQtarget (fun _ => (0 : ℝ))
      contDiff_const W hAfield
  have hmap (z : (Fin m → ℝ) × ℝ) : Φ z = A (Q z.1, z.2) := by rw [hΦmap, add_zero]
  have hnegf (y : M) (hy : y ∉ ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f y (W y) < 0 :=
    (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (W y)).mp
      (hneg y (hcrit ▸ hy))
  refine
    ⟨r, W, G, Q.source, Φ, hr, hW, hG, hzero, hnegf, (fun y hy => hgerms y (hcrit ▸ hy)),
      hgeometry, Q.open_source, hQ0, hΦsource, ?_, ?_, hΦfield⟩
  · intro t
    rw [hmap, hAmap]
    change G t (ι (e 0)) = G t x
    rw [map_zero, hι0]
  · intro z hz ht
    rw [hΦsource] at hz
    have hQo : Q z.1 ∈ O := hQtarget ▸ Q.map_source' hz.1
    have hi : g (ι (Q z.1)) = c / r := hlevel _ hQo
    have he : c / r - z.2 = (c - r * z.2) / r := by field_simp
    have hend : g (ι (Q z.1)) - z.2 ∈ Set.Icc (a / r) (b / r) := by
      rw [hi, he]
      constructor
      · apply div_le_div_of_nonneg_right _ hr.le
        dsimp [r]
        nlinarith [ht.2]
      · apply div_le_div_of_nonneg_right _ hr.le
        nlinarith [mul_nonneg hr.le ht.1]
    have hh :=
      native_local_height_translation hg G hG hH hIH hspeed (ι (Q z.1)) z.2 (hi ▸ hc) hend
    rw [hi, he] at hh
    have hhf : f (G z.2 (ι (Q z.1))) = c - r * z.2 := (div_left_inj' hr.ne').mp hh
    rw [hmap, hAmap]
    exact hhf

/-- A normalized connection cylinder exists. -/
theorem FlowTimeChange.exists_normalized_connection_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = m + 1)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ y ∈ ManifoldMorse.criticalPoints E f, V y = 0)
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {p q x : M} (hpq : f p < f q)
    {c d : ℝ} (hc : c < f p) (hd : f q < d)
    (hpair : ∀ y ∈ ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q)
    (hp : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
    (hunique :
      ∀ y,
        Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) → ∃ t, F t x = y) :
    ∃ (x₀ : M) (r b : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M) (U :
      Set (Fin m → ℝ)) (A :
      PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞),
      x₀ ≠ p ∧
        x₀ ≠ q ∧
          0 < r ∧
            ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
              (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
                (∀ y ∈ ManifoldMorse.criticalPoints E f, W y = 0) ∧
                  (∀ y,
                      y ∉ ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
                    (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ z in 𝓝 y, W z = V z) ∧
                      (∀ y, Antitone (fun t => f (G t y))) ∧
                        Filter.Tendsto (fun t => G t x₀) Filter.atTop (𝓝 p) ∧
                          Filter.Tendsto (fun t => G t x₀) Filter.atBot (𝓝 q) ∧
                            (∀ y,
                                Filter.Tendsto (fun t => G t y) Filter.atBot (𝓝 q) →
                                  Filter.Tendsto (fun t => G t y) Filter.atTop (𝓝 p) →
                                    ∃ t, G t x₀ = y) ∧
                              IsOpen U ∧
                                (0 : Fin m → ℝ) ∈ U ∧
                                  A.source = U ×ˢ Set.univ ∧
                                    (∀ t : ℝ, A (0, t) = G t x₀) ∧
                                      (∀ z ∈ A.source,
                                          z.2 ∈ Set.Icc (0 : ℝ) 1 → f (A z) = b - r * z.2) ∧
                                        (∀ y ∈ A.target,
                                            W y =
                                              FlowConstruction.partialChartField A.symm
                                                (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
                                          (∀ y,
                                              Set.range (fun t => G t y) =
                                                  Set.range (fun t => F t y) ∧
                                                (∀ z,
                                                    Filter.Tendsto (fun t => G t y) Filter.atTop
                                                        (𝓝 z) ↔
                                                      Filter.Tendsto (fun t => F t y) Filter.atTop
                                                        (𝓝 z)) ∧
                                                  ∀ z,
                                                    Filter.Tendsto (fun t => G t y) Filter.atBot
                                                        (𝓝 z) ↔
                                                      Filter.Tendsto (fun t => F t y) Filter.atBot
                                                        (𝓝 z)) ∧
                                            ∃ t, F t x = x₀ := by
  let b : ℝ := (f p + f q) / 2
  let lo : ℝ := (f p + b) / 2
  let hi : ℝ := (b + f q) / 2
  have hpb : f p < b := by dsimp [b]; linarith
  have hbq : b < f q := by dsimp [b]; linarith
  have hplo : f p < lo := by dsimp [lo]; linarith
  have hlob : lo < b := by dsimp [lo]; linarith
  have hbhi : b < hi := by dsimp [hi]; linarith
  have hhiq : hi < f q := by dsimp [hi]; linarith
  have hband : ∀ y, f y ∈ Set.Icc lo hi → y ∉ ManifoldMorse.criticalPoints E f := by
    intro y hy hcrit
    have houter : f y ∈ Set.Icc c d := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rcases hpair y hcrit houter with he | he
    · rw [he] at hy
      exact (not_le_of_gt hplo) hy.1
    · rw [he] at hy
      exact (not_le_of_gt hhiq) hy.2
  obtain ⟨t₀, ht₀⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits F hf.continuous hq hp hbq hpb
  let x₀ := F t₀ x
  have hxp : x₀ ≠ p := by
    intro hh
    have hv : f p = b := hh ▸ ht₀
    exact hpb.ne hv
  have hxq : x₀ ≠ q := by
    intro hh
    have hv : f q = b := hh ▸ ht₀
    exact hbq.ne hv.symm
  have hp₀ : Filter.Tendsto (fun t => F t x₀) Filter.atTop (𝓝 p) :=
    (MorseCancellation.flow_time_atTop_limit_iff F t₀ x p).mpr hp
  have hq₀ : Filter.Tendsto (fun t => F t x₀) Filter.atBot (𝓝 q) :=
    (MorseCancellation.flow_time_atBot_limit_iff F t₀ x q).mpr hq
  have hunique₀ :
    ∀ y,
      Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) → ∃ t, F t x₀ = y := by
    intro y hyq hyp
    obtain ⟨t, ht⟩ := hunique y hyq hyp
    refine ⟨t - t₀, ?_⟩
    change F (t - t₀) (F t₀ x) = y
    rw [← F.map_add, sub_add_cancel]
    exact ht
  obtain
    ⟨r, W, G, U, A, hr, hW, hG, hWzero, hWdesc, hgerms, hgeometry, hU, h0U, hsource, haxis,
      hheight, hfield⟩ :=
    exists_arbitrary_gap_flow_cylinder hf hdim hV hdesc F hF hlob hbhi hband ht₀
  have hzeros : ∀ y ∈ ManifoldMorse.criticalPoints E f, W y = 0 := fun y hy =>
    (hWzero y).mpr (hzero y hy)
  have huniqueG :
    ∀ y,
      Filter.Tendsto (fun t => G t y) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => G t y) Filter.atTop (𝓝 p) → ∃ t, G t x₀ = y := by
    intro y hyq hyp
    have hh : y ∈ Set.range (fun t => F t x₀) :=
      hunique₀ y ((hgeometry y).2.2 q |>.mp hyq) ((hgeometry y).2.1 p |>.mp hyp)
    rw [← (hgeometry x₀).1] at hh
    exact hh
  exact
    ⟨x₀, r, b, W, G, U, A, hxp, hxq, hr, hW, hG, hzeros, hWdesc, hgerms,
      FlowConstruction.antitone_flow_height hf G hG hzeros hWdesc,
      (hgeometry x₀).2.1 p |>.mpr hp₀, (hgeometry x₀).2.2 q |>.mpr hq₀, huniqueG, hU, h0U,
      hsource, haxis, hheight, hfield, hgeometry, t₀, rfl⟩

/-- The cubic flow cylinder pushes the vertical field forward. -/
theorem MorseCancellation.cubicFlowCylinder_pushforward_vertical {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    (p : (Fin m → ℝ) × ℝ) :
    fderiv ℝ (cubicFlowCylinder σ a) p (0, 1) =
      cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a p) := by
  have hd :=
    ((contDiff_cubicFlowCylinder σ a).differentiable (by simp) p).hasFDerivAt |>.comp_hasDerivAt
      p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hd' := hasDerivAt_cubicFlowCylinder σ a p.1 p.2
  exact hd.unique hd'

/-- The native field's transition pushforward. -/
theorem FlowSuspension.native_field_transition_pushforward {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (C : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (WA : D → D) (WC : B → B)
    (hA : ∀ x ∈ A.target, V x = FlowConstruction.partialChartField A.symm WA x)
    (hC : ∀ x ∈ C.target, V x = FlowConstruction.partialChartField C.symm WC x) {p : D}
    (hp : p ∈ (A.trans C.symm).source) : fderiv ℝ (C.symm ∘ A) p (WA p) = WC (C.symm (A p)) := by
  have hpA : p ∈ A.source := hp.1
  have hpC : A p ∈ C.target := hp.2
  have hpushA :
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) A p ((NormedSpace.fromTangentSpace p).symm (WA p)) = V (A p) := by
    have hh := hA (A p) (A.map_source' hpA)
    rw [FlowConstruction.partialChartField_eq_mfderiv_symm A.symm WA
        (A.map_source' hpA)] at hh
    have hi : A.symm (A p) = p := A.left_inv' hpA
    rw [hi] at hh
    exact hh.symm
  have hdiff : C.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, B) :=
    ⟨C.symm.mdifferentiableOn (by simp), C.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) C.symm (A p)).IsInvertible := ⟨hdiff.mfderiv hpC, rfl⟩
  have hpushC :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) C.symm (A p) (V (A p)) =
      (NormedSpace.fromTangentSpace (C.symm (A p))).symm (WC (C.symm (A p))) := by
    rw [hC (A p) hpC]
    unfold FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply]
    exact hinv.self_apply_inverse _
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp p (C.symm.mdifferentiableAt (by simp) hpC) (A.mdifferentiableAt (by simp) hpA)]
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) C.symm (A p))
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) A p) ((NormedSpace.fromTangentSpace p).symm (WA p))) =
      _
  rw [hpushA]
  exact hpushC

/-- The native vertical transition derivative. -/
theorem FlowSuspension.native_vertical_transition_derivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A C : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA :
      ∀ x ∈ A.target,
        V x = FlowConstruction.partialChartField A.symm (fun _ : ℝ × Z => (1, 0)) x)
    (hC :
      ∀ x ∈ C.target,
        V x = FlowConstruction.partialChartField C.symm (fun _ : ℝ × Z => (1, 0)) x)
    {p : ℝ × Z} (hp : p ∈ (A.trans C.symm).source) : fderiv ℝ (C.symm ∘ A) p (1, 0) = (1, 0) :=
  native_field_transition_pushforward A C V (fun _ => (1, 0)) (fun _ => (1, 0)) hA hC hp

/-- The vertical transition formula. -/
theorem FlowSuspension.vertical_transition_formula {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (R : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) (ℝ × Z) (ℝ × Z) ∞)
    (hvertical : ∀ p ∈ R.source, fderiv ℝ R p (1, 0) = (1, 0)) {I : Set ℝ} (hI : IsOpen I)
    (hconn : IsPreconnected I) {U : Set Z} (hsub : I ×ˢ U ⊆ R.source) {t₀ t : ℝ} (h₀ : t₀ ∈ I)
    (ht : t ∈ I) {z : Z} (hz : z ∈ U) : R (t, z) = (t + ((R (t₀, z)).1 - t₀), (R (t₀, z)).2) := by
  let γ : ℝ → ℝ × Z := fun s => R (s, z) - (s, 0)
  have hd (s : ℝ) (hs : s ∈ I) : HasDerivAt γ 0 s := by
    have hp := hsub (show (s, z) ∈ I ×ˢ U from ⟨hs, hz⟩)
    have hR :=
      (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds hp)).differentiableAt
        (by simp)
    have hh := hR.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
    have hh' : HasDerivAt (fun u => R (u, z)) (1, (0 : Z)) s := by
      convert! hh using 1
      exact (hvertical (s, z) hp).symm
    have hdiff := hh'.sub ((hasDerivAt_id s).prodMk (hasDerivAt_const s (0 : Z)))
    convert! hdiff using 1; simp []
  have heq : γ t = γ t₀ :=
    hI.is_const_of_deriv_eq_zero hconn
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht h₀
  apply Prod.ext
  · have hh : (R (t, z)).1 - t = (R (t₀, z)).1 - t₀ := congrArg Prod.fst heq
    linarith
  · have hh : (R (t, z)).2 - 0 = (R (t₀, z)).2 - 0 := congrArg Prod.snd heq
    simpa only [sub_zero] using hh

end
