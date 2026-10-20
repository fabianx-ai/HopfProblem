/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Flow.Compact

/-!
# Descent flows of a function on a compact manifold

Flows of vector fields `V` on a manifold `M` along which a smooth function `f : M → ℝ` does not
increase. The derivative of `f` along an integral curve of `V` is `df (V)`
(`hasDerivAt_comp_integralCurve`); hence if `V` vanishes at the critical points of `f` and
`df (V) < 0` elsewhere, then `f` is antitone along every orbit and strictly antitone along the
orbits of regular points, critical points are fixed and regular points stay regular. On a
compact manifold such a field and its flow exist for every Morse function
(`exists_adaptedDescentFlow`), and if `f` has no critical point with value in `[a, b]` there is a
flow along which `f` has derivative `1` on that band (`exists_regularBandFlow`). These are the
gradient-like fields of Milnor, *Lectures on the h-cobordism theorem*, §3, and the
unit-speed field of Milnor, *Morse Theory*, Theorem 3.1.

## Main results

* `FlowConstruction.hasDerivAt_comp_integralCurve` : the derivative of `f` along an integral
  curve.
* `FlowConstruction.exists_regularBandField`, `FlowConstruction.exists_regularBandFlow` : a
  field, and a flow, with `df (V) = φ ∘ f` where `φ = 1` near `[a, b]`.
* `FlowConstruction.flow_fixed_of_zero`, `FlowConstruction.flow_preserves_regular`,
  `FlowConstruction.antitone_flow_height`, `FlowConstruction.strictAnti_flow_height` :
  monotonicity of the height along a descent flow.
* `FlowConstruction.exists_adaptedDescentFlow` : a descent field of a Morse function that is the
  model descent field of a signed Morse chart near each critical point, with its flow.
* `FlowConstruction.continuous_mvfderiv_field` : `x ↦ df_x (V x)` is continuous.

## References

* [John Milnor, *Morse Theory*][milnor63], §3
* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3

## Tags

gradient-like vector field, descent flow, Morse function
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-- A function along an integral curve differentiates to the field derivative. -/
theorem FlowConstruction.hasDerivAt_comp_integralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (v (γ t))) t := by
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • v (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (v (γ t))
  exact map_smul _ _ _

/-- A regular band field exists between two regular levels. -/
theorem FlowConstruction.exists_regularBandField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ),
      ContDiff ℝ ∞ φ ∧
        IsOpen W ∧
          Set.Icc a b ⊆ W ∧
            Set.EqOn φ (fun _ => 1) W ∧
              ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
                ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                    (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                  ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = φ (f x) := by
  let B := f '' ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Set.Icc a b ⊆ Bᶜ := by
    intro y hy
    rintro ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hφB, W, hW, hAW, -, hφW⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ ∘ f) := hφ.contMDiff.comp hf
  have hsupp : tsupport (φ ∘ f) ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hxφ := tsupport_comp_subset_preimage φ hf.continuous hx
    exact hφB hxφ ⟨x, hcrit, rfl⟩
  obtain ⟨V, hV, hVφ⟩ := exists_prescribedDerivativeField hf hχ hsupp
  exact ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩

/-- A regular band flow exists between two regular levels. -/
theorem FlowConstruction.exists_regularBandFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ) (F : Flow ℝ M),
      ContDiff ℝ ∞ φ ∧
        IsOpen W ∧
          Set.Icc a b ⊆ W ∧
            Set.EqOn φ (fun _ => 1) W ∧
              ∀ x t, HasDerivAt (fun s => f (F s x)) (φ (f (F t x))) t := by
  obtain ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩ := exists_regularBandField hf hband
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  refine ⟨φ, W, compactFlow hV₁, hφ, hW, hAW, hφW, ?_⟩
  intro x t
  have hd := hasDerivAt_comp_integralCurve hf (isMIntegralCurve_compactFlow hV₁ x) t
  rw [hVφ] at hd
  exact hd

/-- The flow fixes points where the field vanishes. -/
theorem FlowConstruction.flow_fixed_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hx : V x = 0)
    (t : ℝ) : F t x = x := by
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve x) (isMIntegralCurve_const hx)
      (t₀ := 0) (F.map_zero_apply x)
  exact congrFun heq t

/-- The flow preserves the regular locus. -/
theorem FlowConstruction.flow_preserves_regular {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f) (t : ℝ) :
    F t x ∉ ManifoldMorse.criticalPoints E f := by
  intro hy
  have hfix := flow_fixed_of_zero hV F hcurve (hzero (F t x) hy) (-t)
  have hinv : F (-t) (F t x) = x := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have hxy : x = F t x := hinv.symm.trans hfix
  exact hx (hxy.symm ▸ hy)

/-- The height is antitone along the descent flow. -/
theorem FlowConstruction.antitone_flow_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (x : M) : Antitone (fun t => f (F t x)) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
  intro t
  change mvfderiv 𝓘(ℝ, E) f (F t x) (V (F t x)) ≤ 0
  by_cases ht : F t x ∈ ManifoldMorse.criticalPoints E f
  · rw [hzero (F t x) ht, map_zero]
  · exact (hdesc (F t x) ht).le

/-- The height is strictly antitone along a nonvanishing descent flow. -/
theorem FlowConstruction.strictAnti_flow_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hx : x ∉ ManifoldMorse.criticalPoints E f) : StrictAnti (fun t => f (F t x)) :=
  strictAnti_of_hasDerivAt_neg (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
    (fun t => hdesc (F t x) (flow_preserves_regular hV F hcurve hzero hx t))

/-- An adapted descent flow exists on a regular region. -/
theorem FlowConstruction.exists_adaptedDescentFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [FiniteDimensional ℝ E] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ p ∈ ManifoldMorse.criticalPoints E f,
                  ∃ c : ManifoldMorse.SignedMorseChart (E := E) f p,
                    ∀ᶠ x in 𝓝 p, V x = c.descentField x) ∧
                (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ t, F t x = x) ∧
                  (∀ x,
                      x ∉ ManifoldMorse.criticalPoints E f →
                        StrictAnti (fun t => f (F t x))) ∧
                    ∀ x, Antitone (fun t => f (F t x)) := by
  obtain ⟨V, hV, hzero, hdesc, hcharts⟩ := ManifoldMorse.exists_adaptedDescentField hf hm
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  let F := compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V := isMIntegralCurve_compactFlow hV₁ x
  exact
    ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, fun x hx t =>
      flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t, fun x hx =>
      strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx, fun x =>
      antitone_flow_height hf F hcurve hzero hdesc x⟩

/-- The field derivative of the height is continuous. -/
theorem FlowConstruction.continuous_mvfderiv_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.continuous_tangentMap (by simp)).comp hV.continuous
  have hp := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp ht
  convert hp.snd using 1
  rfl
