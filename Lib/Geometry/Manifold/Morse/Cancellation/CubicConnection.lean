/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints
import Lib.Geometry.Manifold.Morse.Cancellation.CubicModel
import Lib.Geometry.Manifold.Morse.Cancellation.LyapunovResidence
import Lib.Geometry.Manifold.Morse.Cancellation.BandReplacement

/-!
# Cancellation of a unique cubic connection

Let `f` be a Morse function on a compact manifold with a descending field `V`,
and let `Φ` be a chart in which `V` is the cubic descent field
`nativeCubicDescent σ Φ (-(a ^ 2))` with the two critical points `Φ (a, 0)`,
`Φ (-a, 0)` joined by the axis. If the axis is the only trajectory from
`Φ (-a, 0)` to `Φ (a, 0)` and no other critical value lies in `[c, d]`, then
`f` can be replaced inside the band `f ⁻¹' (Ioo c d)` by a Morse function `g`
with exactly the two critical points removed
(`MorseCancellation.cancel_unique_native_cubic_connection`).

The steps are: the flow along the axis is the model orbit
(`native_cubic_axis_flow`, `native_cubic_axis_orbit`, `native_cubic_closed_axis`);
the cancelled field of `Morse.Cancellation.CubicModel` is transported into the
chart (`exists_native_cubic_field_cancellation_in`); a Lyapunov residence bound
for the transported field (`exists_native_cancelledDescent_residence_bound`) and
the no-return property of the connection give a finite passage time through the
band (`exists_native_cubic_field_finite_passage`,
`exists_cubic_connection_finite_passage`); the band replacement of
`Morse.Cancellation.BandReplacement` then removes the pair.

This is the heart of Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4
(First Cancellation Theorem), in the cubic local model.

## Tags

morse-theory, cancellation, gradient-like-flow
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### The cancelled field in a chart -/

/-- A native cubic field cancellation inside a set exists. -/
theorem MorseCancellation.exists_native_cubic_field_cancellation_in {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ)
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (hσ : ∀ i, σ i ≠ 0) {a : ℝ}
    (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) {N : Set M}
    (hN : IsOpen N) (haxisN : ∀ s ∈ Set.Icc (-a) a, Φ (s, 0) ∈ N) :
    ∃ φ : Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ Φ.source ∧
            Φ '' tsupport φ ⊆ N ∧
              (∀ p, φ p ∈ Set.Icc (0 : ℝ) 1) ∧
                (∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) ∧
                  ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
                    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                      (∀ x ∈ Φ.target,
                          V' x =
                            FlowConstruction.partialChartField Φ.symm
                              (cancelledDescent σ a φ) x) ∧
                        (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
                          ∀ x ∉ Φ '' tsupport φ, ∀ᶠ y in 𝓝 x, V' y = V y := by
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' N) := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hN
  have haxis' : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∩ Φ ⁻¹' N := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact ⟨haxis ⟨hs, rfl⟩, haxisN s hs⟩
  obtain ⟨φ, hφ, hc, hsupp', hrange, hone, hD, hnonzero, hoff⟩ :=
    exists_cubic_field_cancellation σ hσ ha hopen haxis'
  have hsupp : tsupport φ ⊆ Φ.source := fun _ hx => (hsupp' hx).1
  have hsuppN : Φ '' tsupport φ ⊆ N := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsupp' hz).2
  let W := FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ)
  have hW :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
      Φ.target :=
    FlowConstruction.contMDiffOn_partialChartField Φ.symm hD
  have hfix (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' tsupport φ) : W x = V x := by
    have hinv : Φ.symm x ∉ tsupport φ := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    have he := (hoff (Φ.symm x) hinv).eq_of_nhds
    rw [hmodel x hx]
    unfold W nativeCubicDescent FlowConstruction.partialChartField
    simp only [VectorField.mpullback_apply, he]
  have hreg (x : M) (hx : x ∈ Φ.target) : W x ≠ 0 := by
    intro hz
    exact hnonzero _ ((partialChartField_zero_iff Φ (cancelledDescent σ a φ) hx).mp hz)
  obtain ⟨V', hV', heq, hzero, hkeep⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement Φ V W hV hW hc hsupp hfix hreg
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  refine ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, ?_, hkeep⟩
  intro x
  rw [hzero x]
  constructor
  · rintro ⟨hx, hout⟩
    exact ⟨hx, fun he => hout (he ▸ Φ.map_source' hp), fun he => hout (he ▸ Φ.map_source' hq)⟩
  · rintro ⟨hx, hxp, hxq⟩
    refine ⟨hx, ?_⟩
    intro hxt
    have hz : FlowConstruction.partialChartField Φ.symm (cubicDescent σ (-(a ^ 2))) x = 0 :=
      (hmodel x hxt).symm.trans hx
    have hd := (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) hxt).mp hz
    rcases (cubicDescent_zero_iff σ hσ a (Φ.symm x)).mp hd with hh | hh
    · exact hxp ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))
    · exact hxq ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))

/-! ### Residence bounds for the cancelled field -/

/-- A cancelled-descent residence bound exists. -/
theorem MorseCancellation.exists_native_cancelledDescent_residence_bound {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1)
    {C : Set (Model m)} (hC : IsCompact C) (hsource : C ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV :
      ∀ x ∈ Φ '' C,
        V x = FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ) x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨k, -, hL, hneg⟩ := exists_compact_fieldLyapunov σ hσ ha hφ hφnonneg hone hC
  exact
    exists_native_compact_lyapunov_residence Φ hL (contDiff_cancelledDescent σ a hφ).continuous hC
      hsource hneg hV

/-- A native cubic field has finite passage time. -/
theorem MorseCancellation.exists_native_cubic_field_finite_passage {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} {N U : Set M} (hN : IsOpen N)
    (hNU : N ⊆ U) (haxisN : ∀ s ∈ Set.Icc (-a) a, Φ (s, 0) ∈ N) {C : Set (Model m)}
    (hC : IsCompact C) (hCΦ : C ⊆ Φ.source) (hUC : U ⊆ Φ '' C)
    (hneg : ∀ x, f x ∈ Set.Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧
        K ⊆ N ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                ∃ T : ℝ,
                  0 < T ∧
                    ∀ γ : ℝ → M,
                      IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d := by
  obtain ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, hzero, hkeep⟩ :=
    exists_native_cubic_field_cancellation_in σ hσ ha Φ haxis V hV hmodel hN haxisN
  have hK : IsCompact (Φ '' tsupport φ) :=
    hc.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hsupp)
  obtain ⟨T₀, hT₀, hres⟩ :=
    exists_native_cancelledDescent_residence_bound σ hσ ha Φ hφ (fun p => (hrange p).1) hone hC
      hCΦ
      (fun x hx =>
        heq x
          (by
            obtain ⟨z, hz, rfl⟩ := hx
            exact Φ.map_source' (hCΦ hz)))
  have hinner :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U := by
    refine ⟨T₀, hT₀, ?_⟩
    intro γ hγ
    obtain ⟨t, ht, hout⟩ := hres γ hγ
    exact ⟨t, ht, fun h => hout (hUC h)⟩
  refine ⟨Φ '' tsupport φ, V', hK, hsuppN, hV', hzero, hkeep, ?_⟩
  exact
    FlowCancellation.exists_perturbed_band_residence hf hV hV' F hcurve hK.isClosed hN
      hsuppN hNU (fun x hx => (hkeep x hx).self_of_nhds) hneg hnoreturn hinner

/-! ### The cubic axis flow -/

/-- The native cubic axis flow. -/
theorem MorseCancellation.native_cubic_axis_flow {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    F t (Φ (0, 0)) = Φ (cubicModelOrbit a t) := by
  have hmem (s : ℝ) : cubicModelOrbit a s ∈ Φ.source := by
    have hs := cubicAxisParameter_mem ha s
    exact haxis ⟨⟨hs.1.le, hs.2.le⟩, rfl⟩
  have hΓ : IsMIntegralCurve (Φ ∘ cubicModelOrbit a) V := by
    intro s
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
        (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicModelOrbit σ a s) (hmem s)
    have he := hmodel (Φ (cubicModelOrbit a s)) (Φ.map_source' (hmem s))
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ ∘ cubicModelOrbit a) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (nativeCubicDescent σ Φ (-(a ^ 2)) (Φ (cubicModelOrbit a s)))) at hd
    rw [← he] at hd
    exact hd
  have hinit : F 0 (Φ (0, 0)) = (Φ ∘ cubicModelOrbit a) 0 := by
    simp only [F.map_zero_apply, Function.comp_apply, cubicModelOrbit_zero]
    rfl
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve (Φ (0, 0))) hΓ hinit
  exact congrFun heq t

/-- The native cubic axis orbit. -/
theorem MorseCancellation.native_cubic_axis_orbit {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Set.range (fun t : ℝ => F t (Φ (0, 0))) = Φ '' (Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)}) ∧
      Filter.Tendsto (fun t : ℝ => F t (Φ (0, 0))) Filter.atTop (𝓝 (Φ (a, 0))) ∧
        Filter.Tendsto (fun t : ℝ => F t (Φ (0, 0))) Filter.atBot (𝓝 (Φ (-a, 0))) := by
  have heq : (fun t : ℝ => F t (Φ (0, 0))) = Φ ∘ cubicModelOrbit a :=
    funext (native_cubic_axis_flow σ ha Φ haxis hV hmodel F hcurve)
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.range_comp, range_cubicModelOrbit ha]
  · exact
      (Φ.mdifferentiableAt (by simp) hp).continuousAt.tendsto.comp
        (tendsto_cubicModelOrbit_atTop ha)
  · exact
      (Φ.mdifferentiableAt (by simp) hq).continuousAt.tendsto.comp
        (tendsto_cubicModelOrbit_atBot ha)

/-- The native cubic closed axis. -/
theorem MorseCancellation.native_cubic_closed_axis {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Φ '' (Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}) =
      Insert.insert (Φ (a, 0))
        (Insert.insert (Φ (-a, 0)) (Set.range (fun t : ℝ => F t (Φ (0, 0))))) := by
  rw [(native_cubic_axis_orbit σ ha Φ haxis hV hmodel F hcurve).1]
  ext x
  constructor
  · rintro ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsright : s = a
    · exact Or.inl (congrArg (fun r => Φ (r, 0)) hsright)
    by_cases hsleft : s = -a
    · exact Or.inr (Or.inl (congrArg (fun r => Φ (r, 0)) hsleft))
    · exact
        Or.inr
          (Or.inr
            ⟨(s, 0), ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hsleft), lt_of_le_of_ne hs.2 hsright⟩, rfl⟩,
              rfl⟩)
  · rintro (hx | hx | hx)
    · exact ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, hx.symm⟩
    · exact ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, hx.symm⟩
    · obtain ⟨⟨s, z⟩, ⟨hs, hz⟩, he⟩ := hx
      exact ⟨(s, z), ⟨⟨hs.1.le, hs.2.le⟩, hz⟩, he⟩

/-! ### Finite passage of a cubic connection -/

/-- A cubic connection has finite passage. -/
theorem MorseCancellation.exists_cubic_connection_finite_passage {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ ManifoldMorse.criticalPoints E f) (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique :
      ∀ x ∉ ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 (Φ (-a, 0))) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 (Φ (a, 0))) →
            ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧
        K ⊆ Φ.target ∩ f ⁻¹' Set.Ioo c d ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                (∃ T : ℝ,
                    0 < T ∧
                      ∀ γ : ℝ → M,
                        IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d) ∧
                  ∃ G : Flow ℝ M,
                    (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
                      (∃ T : ℝ,
                          0 < T ∧
                            (∀ x, f x ≤ d → f (G T x) < c) ∧ ∀ x, c ≤ f x → d < f (G (-T) x)) ∧
                        ContinuousOn (FlowConstruction.entryTime G {x | f x ≤ c})
                          {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  obtain ⟨hrange, htop, hbot⟩ := native_cubic_axis_orbit σ ha Φ haxis hV₁ hmodel F hcurve
  have hclosed := native_cubic_closed_axis σ ha Φ haxis hV₁ hmodel F hcurve
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc (Φ (0, 0))
  have hztop := hf.continuous.continuousAt.tendsto.comp htop
  have hzbot := hf.continuous.continuousAt.tendsto.comp hbot
  have hzband (t : ℝ) : f (F t (Φ (0, 0))) ∈ Set.Icc (f (Φ (a, 0))) (f (Φ (-a, 0))) :=
    ⟨hmono.le_of_tendsto hztop t, hmono.ge_of_tendsto hzbot t⟩
  let A := Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}
  have hAband : Φ '' A ⊆ f ⁻¹' Set.Ioo c d := by
    intro x hx
    rw [hclosed] at hx
    rcases hx with hx | hx | ⟨t, ht⟩
    · rw [hx]
      exact ⟨hc, lt_trans hpq hd⟩
    · rw [hx]
      exact ⟨lt_trans hc hpq, hd⟩
    · rw [← ht]
      exact ⟨lt_of_lt_of_le hc (hzband t).1, lt_of_le_of_lt (hzband t).2 hd⟩
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' (f ⁻¹' Set.Ioo c d)) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_Ioo.preimage hf.continuous)
  have hAsub : A ⊆ Φ.source ∩ Φ ⁻¹' (f ⁻¹' Set.Ioo c d) := fun x hx =>
    ⟨haxis hx, hAband ⟨x, hx, rfl⟩⟩
  obtain ⟨C, hC, hAC, hCsub⟩ :=
    exists_compact_between
      (show IsCompact A from CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hopen hAsub
  have hCΦ : C ⊆ Φ.source := fun x hx => (hCsub hx).1
  let U := Φ '' interior C
  have hU : IsOpen U :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
      (fun x hx => hCΦ (interior_subset hx))
  have hAU : Φ '' A ⊆ U := Set.image_mono hAC
  have hpU : Φ (a, (0 : Fin m → ℝ)) ∈ U := hAU ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩
  have hqU : Φ (-a, (0 : Fin m → ℝ)) ∈ U := hAU ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
  have hzU (t : ℝ) : F t (Φ (0, 0)) ∈ U := by
    apply hAU
    rw [hclosed]
    exact Or.inr (Or.inr ⟨t, rfl⟩)
  obtain ⟨N, hN, hNU, hpN, hqN, hzN, hnoreturn⟩ :=
    FlowCancellation.exists_native_connection_no_return hf hV F hcurve hzero hdesc hinj hp
      hq hpq (fun x hx hh => hpair x hx ⟨le_trans hc.le hh.1, le_trans hh.2 hd.le⟩) hzband hunique
      hU hpU hqU hzU
  have haxisN (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : Φ (s, (0 : Fin m → ℝ)) ∈ N := by
    have hh : Φ (s, (0 : Fin m → ℝ)) ∈ Φ '' A := ⟨(s, 0), ⟨hs, rfl⟩, rfl⟩
    rw [hclosed] at hh
    rcases hh with hh | hh | ⟨t, ht⟩
    · exact hh ▸ hpN
    · exact hh ▸ hqN
    · exact ht ▸ hzN t
  have hneg (x : M) (hx : f x ∈ Set.Icc c d) (hout : x ∉ N) : mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    apply hdesc x
    intro hcrit
    rcases hpair x hcrit hx with he | he
    · exact hout (he ▸ hpN)
    · exact hout (he ▸ hqN)
  obtain ⟨K, V', hK, hKN, hV', hzeros, hkeep, hpass⟩ :=
    exists_native_cubic_field_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve hN hNU haxisN
      hC hCΦ (Set.image_mono interior_subset) hneg hnoreturn
  have hKsub : K ⊆ Φ.target ∩ f ⁻¹' Set.Ioo c d := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hNU (hKN hx)
    exact ⟨Φ.map_source' (hCΦ (interior_subset hz)), (hCsub (interior_subset hz)).2⟩
  have hcd : c ≤ d := by linarith
  have hboundary (x : M) (hx : f x = c ∨ f x = d) : mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Set.Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Set.Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd⟩
        · exact ⟨hcd, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  refine ⟨K, V', hK, hKsub, hV', hzeros, hkeep, hpass, ?_⟩
  exact
    FlowCancellation.exists_native_flow_band_crossing hf hV'
      (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hpass

/-! ### Cancellation of a unique cubic connection -/

/-- A unique native cubic connection can be cancelled. -/
theorem MorseCancellation.cancel_unique_native_cubic_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ ManifoldMorse.criticalPoints E f) (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique :
      ∀ x ∉ ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 (Φ (-a, 0))) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 (Φ (a, 0))) →
            ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨K, V', -, hKsub, hV', -, hkeep, -, G, hGcurve, hcross, -⟩ :=
    exists_cubic_connection_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve hzero hdesc
      hinj hp hq hpq hc hd hpair hunique
  have hcd : c < d := lt_trans hc (lt_trans hpq hd)
  have hboundary (x : M) (hx : f x = c ∨ f x = d) : mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Set.Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Set.Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd.le⟩
        · exact ⟨hcd.le, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  have hneq : Φ (a, (0 : Fin m → ℝ)) ≠ Φ (-a, 0) := by
    intro h
    exact hpq.ne (congrArg f h)
  exact
    FlowCancellation.remove_morse_band_pair hf hm hV' G hGcurve hcd
      (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hcross hneq hp
      hq ⟨hc.le, (hpq.trans hd).le⟩ ⟨(hc.trans hpq).le, hd.le⟩ hpair

end
