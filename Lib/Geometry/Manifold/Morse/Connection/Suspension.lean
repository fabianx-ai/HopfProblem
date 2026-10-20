/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime

/-!
# The suspended flow of a level diffeomorphism

For a manifold `N` and a diffeomorphism `Ψ` of `N × ℝ` preserving the height, the *suspended
flow* `nativeSuspensionFlow Ψ` is the vertical translation flow `(x, s) ↦ (x, s + t)`
conjugated by `Ψ` (`nativeSuspensionFlow_chart`); its generating field is
`nativeSuspensionField Ψ`, the push-forward of the vertical field `nativeVerticalField`
(`nativeSuspensionFlow_integralCurve`, `contMDiff_nativeSuspensionField`,
`nativeSuspensionFlow_height`). `exists_native_base_suspension` produces such a `Ψ` from a
supported relative isotopy from the identity to `D`: `Ψ = id` for heights `≤ 1/3` and
`Ψ = D × id` for heights `≥ 2/3`.

Model fields pulled back along a chart: `native_model_pullback_zero_iff`,
`contMDiffOn_native_model_pullback`, `native_model_pullback_eq_mfderiv_symm`,
`hasMFDerivAt_lift_native_model_curve`, `exists_native_model_field_replacement` (replacing the
model field inside a compact part of the chart keeps a smooth field with the same zeros),
`native_model_flow_all_time`, `native_model_target_invariant`, `native_chart_flow_all_time`,
`native_chart_target_invariant`, `flow_complement_invariant` (a chart whose model flow is
complete carries the flow of `V` for all times).

The level flow cylinder: `exists_native_level_flow_cylinder_with_field` and
`native_level_flow_chart_vertical` give, for a regular level `{f = c}`, the chart
`A (p, t) = F t p` on `{f = c} × ℝ` onto the level basin, in which `V` is the vertical field.

cf. Milnor, *Lectures on the h-cobordism theorem*, §4 (a diffeomorphism of a level surface
isotopic to the identity is realised by altering the gradient-like field in a collar).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### The native suspended flow -/

/-- The native model pullback vanishes exactly on the critical set. -/
theorem FlowSuspension.native_model_pullback_zero_iff {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z) {x : M} (hx : x ∈ e.source) :
    VectorField.mpullback 𝓘(ℝ, E) I e W x = 0 ↔ W (e x) = 0 := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  let L := he.mfderiv hx
  rw [VectorField.mpullback_apply]
  change L.toContinuousLinearMap.inverse (W (e x)) = 0 ↔ W (e x) = 0
  rw [ContinuousLinearMap.inverse_equiv]
  constructor
  · intro h
    exact L.symm.injective (h.trans (map_zero L.symm).symm)
  · intro h
    rw [h]
    exact map_zero L.symm

/-- The native model pullback is smooth. -/
theorem FlowSuspension.contMDiffOn_native_model_pullback {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [IsManifold I ∞ X] (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞) (W : (z : X) → TangentSpace I z)
    (hW : ContMDiff I I.tangent ∞ (fun z => (⟨z, W z⟩ : TangentBundle I X))) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, VectorField.mpullback 𝓘(ℝ, E) I e W x⟩ : TangentBundle 𝓘(ℝ, E) M))
      e.source := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) I e x).IsInvertible := ⟨he.mfderiv hx, rfl⟩
  exact
    ((hW (e x)).mpullback_vectorField_preimage
        (e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx)) hinv
        (by simp)).contMDiffWithinAt

/-- A native model field replacement exists. -/
theorem FlowSuspension.exists_native_model_field_replacement {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [IsManifold I ∞ X] [T2Space M] (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (W₀ W : (z : X) → TangentSpace I z)
    (hW : ContMDiff I I.tangent ∞ (fun z => (⟨z, W z⟩ : TangentBundle I X)))
    (hmodel : ∀ y ∈ A.target, V y = VectorField.mpullback 𝓘(ℝ, E) I A.symm W₀ y)
    (hregular₀ : ∀ z ∈ A.source, W₀ z ≠ 0) (hregular : ∀ z ∈ A.source, W z ≠ 0) {K : Set X}
    (hK : IsCompact K) (hKA : K ⊆ A.source) (hfix : ∀ z ∉ K, W z = W₀ z) :
    ∃ V' : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ y ∈ A.target, V' y = VectorField.mpullback 𝓘(ℝ, E) I A.symm W y) ∧
          (∀ y, V' y = 0 ↔ V y = 0) ∧ ∀ y ∉ A '' K, ∀ᶠ z in 𝓝 y, V' z = V z := by
  let Wn := VectorField.mpullback 𝓘(ℝ, E) I A.symm W
  have hWn := contMDiffOn_native_model_pullback A.symm W hW
  have hreg (y : M) (hy : y ∈ A.target) : Wn y ≠ 0 := fun h =>
    hregular (A.symm y) (A.map_target' hy) ((native_model_pullback_zero_iff A.symm W hy).mp h)
  have hregV (y : M) (hy : y ∈ A.target) : V y ≠ 0 := by
    rw [hmodel y hy]
    exact fun h =>
      hregular₀ (A.symm y) (A.map_target' hy) ((native_model_pullback_zero_iff A.symm W₀ hy).mp h)
  have hkeep (y : M) (hy : y ∈ A.target) (hout : y ∉ A '' K) : Wn y = V y := by
    have hn : A.symm y ∉ K := fun h => hout ⟨A.symm y, h, A.right_inv' hy⟩
    rw [hmodel y hy]
    change
      VectorField.mpullback 𝓘(ℝ, E) I A.symm W y = VectorField.mpullback 𝓘(ℝ, E) I A.symm W₀ y
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hfix (A.symm y) hn]
  obtain ⟨V', hV', hnew, hzero, hgerm⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement A V Wn hV hWn hK hKA hkeep hreg
  refine ⟨V', hV', hnew, ?_, hgerm⟩
  intro y
  exact (hzero y).trans ⟨And.left, fun hy => ⟨hy, fun ht => hregV y ht hy⟩⟩

/-- The native chart flow exists for all time. -/
theorem FlowSuspension.native_chart_flow_all_time {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, B) E M ∞)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V) (F : Flow ℝ E) (W : E → E)
    (hF : ∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t)
    (hmodel : ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm W x) {p : E}
    (hstay : ∀ t, F t p ∈ Φ.source) : ∀ t, G t (Φ p) = Φ (F t p) := by
  let γ : ℝ → M := fun t => Φ (F t p)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm W (hF p t) (hstay t)
    have hy := Φ.map_source' (hstay t)
    have hd' :
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (FlowConstruction.partialChartField Φ.symm W (γ t))) :=
      hd
    rw [← hmodel (γ t) hy] at hd'
    exact hd'
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hG (Φ p)) hγ (t₀ := 0)
      (by simp only [γ, G.map_zero_apply, F.map_zero_apply])
  exact fun t => congrFun heq t

/-- The native chart target is flow invariant. -/
theorem FlowSuspension.native_chart_target_invariant {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, B) E M ∞)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V) (F : Flow ℝ E) (W : E → E)
    (hF : ∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t)
    (hmodel : ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm W x)
    (hstay : ∀ p ∈ Φ.source, ∀ t, F t p ∈ Φ.source) : ∀ x ∈ Φ.target, ∀ t, G t x ∈ Φ.target := by
  intro x hx t
  have hp := Φ.map_target' hx
  have heq := native_chart_flow_all_time Φ hV G hG F W hF hmodel (hstay _ hp) t
  rw [Φ.right_inv' hx] at heq
  rw [heq]
  exact Φ.map_source' (hstay _ hp t)

/-- The flow complement is invariant. -/
theorem FlowSuspension.flow_complement_invariant {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S : Set X} (hS : ∀ x ∈ S, ∀ t, F t x ∈ S) : ∀ x ∉ S, ∀ t, F t x ∉ S := by
  intro x hx t ht
  have hh := hS (F t x) ht (-t)
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  exact hx hh

/-- The native model pullback is the inverse derivative. -/
theorem FlowSuspension.native_model_pullback_eq_mfderiv_symm {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z) {x : M} (hx : x ∈ e.source) :
    VectorField.mpullback 𝓘(ℝ, E) I e W x = mfderiv I 𝓘(ℝ, E) e.symm (e x) (W (e x)) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  rw [VectorField.mpullback_apply]
  change (mfderiv 𝓘(ℝ, E) I e' x).inverse (W (e' x)) = _
  rw [hi]
  rfl

/-- A native model curve lifts to a manifold curve. -/
theorem FlowSuspension.hasMFDerivAt_lift_native_model_curve {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z) {α : ℝ → X} {t : ℝ}
    (hα : HasMFDerivAt 𝓘(ℝ, ℝ) I α t ((1 : ℝ →L[ℝ] ℝ).smulRight (W (α t))))
    (ht : α t ∈ e.target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (e.symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (VectorField.mpullback 𝓘(ℝ, E) I e W (e.symm (α t)))) := by
  have hi :=
    (e.symm.contMDiffOn_toFun.contMDiffAt (e.open_target.mem_nhds ht)).mdifferentiableAt (by simp)
  have hd := hi.hasMFDerivAt.comp t hα
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let s : ℝ := a
  change
    (mfderiv I 𝓘(ℝ, E) e.symm (α t)) (s • W (α t)) =
      s • VectorField.mpullback 𝓘(ℝ, E) I e W (e.symm (α t))
  rw [map_smul]
  have hp := native_model_pullback_eq_mfderiv_symm e W (x := e.symm (α t)) (e.map_target' ht)
  have hr : e (e.symm (α t)) = α t := e.right_inv' ht
  rw [hr] at hp
  exact congrArg (fun v : TangentSpace 𝓘(ℝ, E) (e.symm (α t)) => s • v) hp.symm

/-- The native model flow exists for all time. -/
theorem FlowSuspension.native_model_flow_all_time {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V) (F : Flow ℝ X)
    (W : (z : X) → TangentSpace I z) (hF : ∀ p, IsMIntegralCurve (fun t => F t p) W)
    (hmodel : ∀ x ∈ A.target, V x = VectorField.mpullback 𝓘(ℝ, E) I A.symm W x) {p : X}
    (hstay : ∀ t, F t p ∈ A.source) : ∀ t, G t (A p) = A (F t p) := by
  let γ : ℝ → M := fun t => A (F t p)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hd := hasMFDerivAt_lift_native_model_curve A.symm W (hF p t) (hstay t)
    have hd' :
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (VectorField.mpullback 𝓘(ℝ, E) I A.symm W (γ t))) :=
      hd
    rw [← hmodel (γ t) (A.map_source' (hstay t))] at hd'
    exact hd'
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hG (A p)) hγ (t₀ := 0)
      (by simp only [γ, G.map_zero_apply, F.map_zero_apply])
  exact fun t => congrFun heq t

/-- The native model target is invariant. -/
theorem FlowSuspension.native_model_target_invariant {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V) (F : Flow ℝ X)
    (W : (z : X) → TangentSpace I z) (hF : ∀ p, IsMIntegralCurve (fun t => F t p) W)
    (hmodel : ∀ x ∈ A.target, V x = VectorField.mpullback 𝓘(ℝ, E) I A.symm W x)
    (hstay : ∀ p ∈ A.source, ∀ t, F t p ∈ A.source) : ∀ x ∈ A.target, ∀ t, G t x ∈ A.target := by
  intro x hx t
  have hp := A.map_target' hx
  have heq := native_model_flow_all_time A hV G hG F W hF hmodel (hstay _ hp) t
  rw [A.right_inv' hx] at heq
  rw [heq]
  exact A.map_source' (hstay _ hp t)

/-- A native base suspension exists. -/
theorem FlowSuspension.exists_native_base_suspension {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N] (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N}
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞,
      (∀ p, (Ψ p).2 = p.2) ∧
        (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
          (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
            (∀ p, p.1 ∉ K → Ψ p = p) ∧ ∀ p, p.1 ∈ S → Ψ p = p := by
  let τ : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hτ : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hlow (t : ℝ) (ht : t ≤ 1 / 3) : τ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hhigh (t : ℝ) (ht : 2 / 3 ≤ t) : τ t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  let A : N × ℝ → N := fun p => I.family (τ p.2, p.1)
  have hA : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Z) ∞ A :=
    I.smooth.comp ((hτ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst)
  have hslice : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞, ∀ x, d x = A (x, t) := fun t =>
    I.slices (τ t)
  let Ψ := FiberwiseDiffeomorph.diffeomorph hA hslice
  have hmap (p : N × ℝ) : Ψ p = (I.family (τ p.2, p.1), p.2) := rfl
  refine ⟨Ψ, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hmap, hlow p.2 hp, I.zero]
  · intro p hp
    rw [hmap, hhigh p.2 hp, I.one]
  · intro p hp
    rw [hmap, I.fixedOutside (τ p.2) p.1 hp]
  · intro p hp
    rw [hmap, I.fixedOn (τ p.2) p.1 hp]

/-- The native suspended flow. -/
def FlowSuspension.nativeSuspensionFlow {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) :
    Flow ℝ (N × ℝ) where
  toFun t p := Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)
  cont' :=
    Ψ.continuous.comp
      ((Ψ.symm.continuous.comp continuous_snd).fst.prodMk
        ((Ψ.symm.continuous.comp continuous_snd).snd.add continuous_fst))
  map_zero' p := by simp only [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  map_add' s t
    p := by
    simp only [Ψ.symm_apply_apply]
    congr 1
    apply Prod.ext
    · rfl
    · ring

/-- The native suspended flow computes in the chart. -/
theorem FlowSuspension.nativeSuspensionFlow_chart {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) (t : ℝ)
    (p : N × ℝ) : nativeSuspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

/-- The native vertical field on the cylinder. -/
def FlowSuspension.nativeVerticalField {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N] (p : N × ℝ) :
    TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p :=
  (show Z × ℝ from (0, 1))

/-- The native vertical field is smooth. -/
theorem FlowSuspension.contMDiff_nativeVerticalField {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N] :
    ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p : N × ℝ =>
        (⟨p, nativeVerticalField p⟩ : TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) := by
  have hz :
    ContMDiff 𝓘(ℝ, Z) (𝓘(ℝ, Z).tangent) ∞
      (fun x : N => (⟨x, (0 : Z)⟩ : TangentBundle 𝓘(ℝ, Z) N)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, Z) : N → Type _)
  have ho :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have hpair :
      ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) ∞ (fun t : ℝ => (show ModelProd ℝ ℝ from (t, 1))) := by
      unfold ModelWithCorners.tangent
      rw [← modelWithCornersSelf_prod]
      exact (contDiff_id.prodMk contDiff_const).contMDiff
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, ℝ)) (n := ∞)).comp hpair
  have hp :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, Z)) (I' := 𝓘(ℝ, ℝ)) (M := N) (M' := ℝ) (n :=
          ∞)).comp
      ((hz.comp contMDiff_fst).prodMk (ho.comp contMDiff_snd))
  exact hp

/-- The native suspension field. -/
def FlowSuspension.nativeSuspensionField {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (p : N × ℝ) : TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p :=
  mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (Ψ.symm p)
    (nativeVerticalField (Ψ.symm p))

/-- The native suspension field is smooth. -/
theorem FlowSuspension.contMDiff_nativeSuspensionField {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) :
    ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p : N × ℝ =>
        (⟨p, nativeSuspensionField Ψ p⟩ : TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) := by
  have ht :=
    (Ψ.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
      (contMDiff_nativeVerticalField.comp Ψ.symm.contMDiff)
  convert! ht using 1
  funext p
  apply Bundle.TotalSpace.ext (Ψ.apply_symm_apply p).symm
  rfl

/-- The native vertical field's integral curve. -/
theorem FlowSuspension.nativeVerticalField_integralCurve {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N] (p : N × ℝ) :
    IsMIntegralCurve (fun t : ℝ => (p.1, p.2 + t)) (nativeVerticalField (Z := Z)) := by
  intro t
  have hn : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) (fun _ : ℝ => p.1) t (0 : ℝ →L[ℝ] Z) :=
    hasMFDerivAt_const p.1 t
  have ht :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) p.2 t).add
      (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t)
  apply (hn.prodMk ht).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change ((0 : Z), (0 : ℝ) + s) = s • ((0 : Z), (1 : ℝ))
  simp

/-- The native suspended flow is an integral curve. -/
theorem FlowSuspension.nativeSuspensionFlow_integralCurve {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (p : N × ℝ) :
    IsMIntegralCurve (fun t : ℝ => nativeSuspensionFlow Ψ t p) (nativeSuspensionField Ψ) := by
  intro t
  let γ : ℝ → N × ℝ := fun s => ((Ψ.symm p).1, (Ψ.symm p).2 + s)
  have hb := nativeVerticalField_integralCurve (Z := Z) (Ψ.symm p) t
  have hd := (Ψ.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.comp (f := γ) t hb
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (fun s => Ψ (γ s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (Ψ.symm (Ψ (γ t)))
          (nativeVerticalField (Ψ.symm (Ψ (γ t))))))
  rw [Ψ.symm_apply_apply]
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (fun s => Ψ (γ s)) t
      ((mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeVerticalField (γ t)))) at hd
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  exact
    (mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (γ t)).map_smul (r : ℝ)
      (nativeVerticalField (γ t))

/-- The native suspended flow's height. -/
theorem FlowSuspension.nativeSuspensionFlow_height {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (t : ℝ) (p : N × ℝ) :
    (nativeSuspensionFlow Ψ t p).2 = p.2 + t := by
  have hi : (Ψ.symm p).2 = p.2 := by
    have hh := hheight (Ψ.symm p)
    rw [Ψ.apply_symm_apply] at hh
    exact hh.symm
  change (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)).2 = p.2 + t
  rw [hheight, hi]

/-- The native level flow is vertical in the chart. -/
theorem FlowSuspension.native_level_flow_chart_vertical {Z E N M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace N] [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    [TopologicalSpace M] [ChartedSpace E M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ι : N → M)
    (hformula : ∀ p : N × ℝ, A p = F p.2 (ι p.1)) :
    ∀ x ∈ A.target,
      V x = VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField x := by
  intro x hx
  let p := A.symm x
  have hp : p ∈ A.source := A.map_target' hx
  let α : ℝ → N × ℝ := fun t => (p.1, t)
  have hα :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) α p.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeVerticalField (α p.2))) := by
    have hn : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) (fun _ : ℝ => p.1) p.2 (0 : ℝ →L[ℝ] Z) :=
      hasMFDerivAt_const p.1 p.2
    apply (hn.prodMk (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) p.2)).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    let u : ℝ := r
    change ((0 : Z), u) = u • ((0 : Z), (1 : ℝ))
    simp
  have hd := hasMFDerivAt_lift_native_model_curve A.symm nativeVerticalField hα hp
  have heq : A.symm.symm ∘ α = fun t => F t (ι p.1) := funext (fun t => hformula (p.1, t))
  rw [heq] at hd
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField
          (A p))) at hd
  rw [hformula p] at hd
  have hpF : F p.2 (ι p.1) = x := (hformula p).symm.trans (A.right_inv' hx)
  have hh := (hcurve (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
  have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) => L (1 : ℝ)) hh
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
  change
    V (F p.2 (ι p.1)) =
      VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField
        (F p.2 (ι p.1)) at hv
  rw [hpF] at hv
  exact hv

/-- A native level flow cylinder with the field exists. -/
theorem FlowSuspension.exists_native_level_flow_cylinder_with_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) (z : { x : M // f x = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ A :
      PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ x : M // f x = c } × ℝ) M ∞,
      A.source = Set.univ ∧
        A.target = FlowCancellation.levelBasin F f c ∧
          (∀ p, A p = F p.2 p.1) ∧
            ∀ x ∈ A.target,
              V x =
                VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ))
                  A.symm nativeVerticalField x := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  obtain ⟨A, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hreg hV F hcurve hboundary z
  exact
    ⟨A, hsource, htarget, hformula,
      native_level_flow_chart_vertical A F hcurve Subtype.val hformula⟩

end
