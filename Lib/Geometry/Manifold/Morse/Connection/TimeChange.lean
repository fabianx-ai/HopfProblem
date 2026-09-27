/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.NoReturn

/-!
# Time changes of a descent flow

Multiplying a descent field `V` by a positive smooth function `ρ` changes neither the orbits nor
their limits:

* `exists_positive_integral_clock`, `native_curve_positive_reparametrization`,
  `exists_native_flow_time_change`, `native_flow_time_change_orbits`: the flow `G` of `ρ • V`
  is `G t x = F (c⁻¹ t) x` for the clock `c t = ∫₀ᵗ ρ (F s x)⁻¹`, with the same orbits and
  limits as the flow `F` of `V`.
* `exists_positive_height_rescaling`, `exists_positive_band_normalization`: `ρ` can be chosen
  with `df (ρ • V) = -1` on a band `[a, b]` free of critical points and `ρ = 1` near the
  critical points.
* `local_affine_height_germ`, `scalar_local_height_translation`,
  `native_local_height_translation`, `normalized_flow_level_image`,
  `normalized_flow_sublevel_iff`, `normalized_flow_sublevel_image`: with `df (V) = -1` on the
  band the flow translates the height, and `F (a - b)` carries `{f = a}` onto `{f = b}` and
  `{f ≤ a}` onto `{f ≤ b}`.
* `exists_orbit_preserving_band_normalization`,
  `exists_orbit_preserving_ambient_band_bridge`, `exists_orbit_preserving_native_band_bridge`:
  the resulting diffeomorphism of `M` moving along orbits, and the induced diffeomorphism of the
  regular levels `{f = a} → {f = b}`.

`TransverseCoordinates.surjective_coprod_swap` is the symmetry of the transversality condition
under swapping the two summands.

cf. Milnor, *Lectures on the h-cobordism theorem*, §3 (a gradient-like field normalised so that
`ξ (f) = 1` on a band without critical points gives a product structure).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

section

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2

/-! ### Supported divisions and no-return perturbations -/

/-- The coproduct swap of transverse coordinates is surjective. -/
theorem TransverseCoordinates.surjective_coprod_swap {D Z E : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : D →L[ℝ] E) (C : Z →L[ℝ] E) (h : Function.Surjective (A.coprod C)) :
    Function.Surjective (C.coprod A) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ := h w
  refine ⟨(v, u), ?_⟩
  change C v + A u = w
  rw [add_comm]
  exact huv

/-- A positive height rescaling exists. -/
theorem MorseCancellation.exists_positive_height_rescaling {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ) (hχrange : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hdesc : ∀ x ∈ tsupport χ, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ ρ : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ x, 0 < ρ x) ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
              (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
              (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) < 0) ∧
                (∀ x, χ x = 1 → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) = -1) ∧
                  ∀ x ∉ tsupport χ, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let ρ (x : M) := 1 - χ x + χ x / (-D x)
  have hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D := contMDiff_directionalDerivative hf hV
  have hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.sub hχ).add
      (contMDiff_supported_division hχ hD.neg (fun x hx => neg_ne_zero.mpr (hdesc x hx).ne))
  have hpos (x : M) : 0 < ρ x := by
    by_cases hx : x ∈ tsupport χ
    · have hdx : 0 < -D x := neg_pos.mpr (hdesc x hx)
      by_cases he : χ x = 1
      · simpa only [ρ, he, sub_self, zero_add] using one_div_pos.mpr hdx
      · exact
          add_pos_of_pos_of_nonneg (sub_pos.mpr (lt_of_le_of_ne (hχrange x).2 he))
            (div_nonneg (hχrange x).1 hdx.le)
    · simp only [ρ, image_eq_zero_of_notMem_tsupport hx, sub_zero, zero_div, add_zero]
      exact zero_lt_one
  refine ⟨ρ, hρ, hpos, hρ.smul_section hV, ?_, ?_, ?_, ?_⟩
  · intro x
    exact smul_eq_zero.trans (or_iff_right (hpos x).ne')
  · intro x hx
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hpos x) hx
  · intro x hx
    have hs : x ∈ tsupport χ := subset_tsupport χ (by simp [Function.mem_support, hx])
    have hd : D x ≠ 0 := (hdesc x hs).ne
    rw [map_smul, smul_eq_mul]
    change (1 - χ x + χ x / (-D x)) * D x = -1
    rw [hx]
    field_simp
    ring
  · intro x hx
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [ρ, image_eq_zero_of_notMem_tsupport hy, sub_zero, zero_div, add_zero]

/-- A positive band normalization exists. -/
theorem MorseCancellation.exists_positive_band_normalization {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {a b : ℝ} (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (ρ : M → ℝ) (U : Set ℝ),
      IsOpen U ∧
        Set.Icc a b ⊆ U ∧
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ ∧
            (∀ x, 0 < ρ x) ∧
              ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                  (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
                  (∀ x,
                      x ∉ ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) < 0) ∧
                    (∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) = -1) ∧
                      ∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let B := f '' ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Set.Icc a b ⊆ Bᶜ := by
    rintro y hy ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hsupp, U, hU, hAU, -, hφU⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  let χ := Real.smoothTransition ∘ φ ∘ f
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ :=
    (Real.smoothTransition.contDiff.comp hφ).contMDiff.comp hf
  have hχsupport : tsupport χ ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hp := tsupport_comp_subset Real.smoothTransition.zero (φ ∘ f) hx
    exact hsupp (tsupport_comp_subset_preimage φ hf.continuous hp) ⟨x, hcrit, rfl⟩
  obtain ⟨ρ, hρ, hpos, hW, hzero, hneg, hspeed, hgerm⟩ :=
    exists_positive_height_rescaling hf hV hχ
      (fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
      (fun x hx => hdesc x (hχsupport hx))
  refine ⟨ρ, U, hU, hAU, hρ, hpos, hW, hzero, fun x hx => hneg x (hdesc x hx), ?_, ?_⟩
  · intro x hx
    apply hspeed
    simp only [χ, Function.comp_apply, hφU hx, Real.smoothTransition.one]
  · intro x hx
    exact hgerm x (fun h => hχsupport h hx)

end

/-! ### Flow time changes -/

/-- A local affine height germ exists. -/
theorem FlowTimeChange.local_affine_height_germ {γ : ℝ → ℝ} (hγ : Continuous γ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ t, γ t ∈ U → HasDerivAt γ (-1) t) {t : ℝ} (ht : γ t ∈ U) :
    ∀ᶠ s in 𝓝 t, γ s + s = γ t + t := by
  obtain ⟨l, u, htu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((hU.preimage hγ).mem_nhds ht)
  have hder (s : ℝ) (hs : s ∈ Set.Ioo l u) : HasDerivAt (fun r => γ r + r) 0 s := by
    convert! (hd s (hsub hs)).add (hasDerivAt_id s) using 1
    norm_num
  filter_upwards [Ioo_mem_nhds htu.1 htu.2] with s hs
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv) hs htu

/-- The scalar local height translation. -/
theorem FlowTimeChange.scalar_local_height_translation {γ : ℝ → ℝ} (hγ : Continuous γ)
    {U : Set ℝ} (hU : IsOpen U) {a b c t : ℝ} (hIU : Set.Icc a b ⊆ U)
    (hd : ∀ s, γ s ∈ U → HasDerivAt γ (-1) s) (hzero : γ 0 = c) (hc : c ∈ Set.Icc a b)
    (ht : c - t ∈ Set.Icc a b) : γ t = c - t := by
  let J := Set.Icc (c - b) (c - a)
  let _ : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let P : J → Prop := fun s => γ s = c - s
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro s
    by_cases hs : P s
    · have hsU : γ s ∈ U := by
        rw [show γ s = c - s from hs]
        exact hIU ⟨by linarith [s.property.2], by linarith [s.property.1]⟩
      have heq := local_affine_height_germ hγ hU hd hsU
      filter_upwards [continuous_subtype_val.continuousAt heq] with r hr
      apply propext
      constructor
      · intro _
        exact hs
      · intro _
        change γ r = c - r
        change γ s = c - s at hs
        change γ r + r = γ s + s at hr
        linarith
    · have hn : (s : ℝ) ∈ {r : ℝ | γ r = c - r}ᶜ := hs
      have hopen : IsOpen {r : ℝ | γ r = c - r}ᶜ :=
        (isClosed_eq hγ ((continuous_const (y := c)).sub continuous_id)).isOpen_compl
      filter_upwards [continuous_subtype_val.continuousAt (hopen.mem_nhds hn)] with r hr
      exact propext ⟨fun h => (hr h).elim, fun h => (hs h).elim⟩
  let s₀ : J := ⟨0, ⟨by linarith [hc.2], by linarith [hc.1]⟩⟩
  let s₁ : J := ⟨t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have hinit : P s₀ := by simpa only [P, s₀, sub_zero] using hzero
  have heq : P s₀ = P s₁ := hloc.apply_eq_of_preconnectedSpace s₀ s₁
  have hfinish : P s₁ := heq ▸ hinit
  exact hfinish

/-- The native local height translation. -/
theorem FlowTimeChange.native_local_height_translation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} (hIU : Set.Icc a b ⊆ U) (hspeed : ∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (V x) = -1)
    (x : M) (t : ℝ) (hx : f x ∈ Set.Icc a b) (ht : f x - t ∈ Set.Icc a b) : f (F t x) = f x - t :=
  by
  apply
    scalar_local_height_translation
      (hf.continuous.comp (F.continuous continuous_id continuous_const)) hU hIU (γ := fun s =>
      f (F s x)) ?_ (by rw [F.map_zero_apply]) hx ht
  intro s hs
  have hd := FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) s
  rw [hspeed (F s x) hs] at hd
  exact hd

/-- The normalized flow's level image. -/
theorem FlowTimeChange.normalized_flow_level_image {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Set.Icc a b → f x - t ∈ Set.Icc a b → f (F t x) = f x - t) :
    F (a - b) '' {x : X | f x = a} = {x : X | f x = b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f x = a at hx
    have hh :=
      hshift x (a - b) (by rw [hx]; exact ⟨le_rfl, hab⟩) (by rw [hx]; constructor <;> linarith)
    change f (F (a - b) x) = b
    linarith
  · intro hy
    change f y = b at hy
    have hh :=
      hshift y (b - a) (by rw [hy]; exact ⟨hab, le_rfl⟩) (by rw [hy]; constructor <;> linarith)
    refine ⟨F (b - a) y, ?_, ?_⟩
    · change f (F (b - a) y) = a
      linarith
    · rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]

/-- The normalized flow's sublevel membership. -/
theorem FlowTimeChange.normalized_flow_sublevel_iff {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Set.Icc a b → f x - t ∈ Set.Icc a b → f (F t x) = f x - t) (x : X) :
    f (F (a - b) x) ≤ b ↔ f x ≤ a := by
  let γ : ℝ → ℝ := fun s => f (F (-s) x) - (a + s)
  have hγ : Continuous γ :=
    (hf.comp (F.continuous ContinuousNeg.continuous_neg continuous_const)).sub
      (continuous_const.add continuous_id)
  have hstart : γ 0 = f x - a := by simp only [γ, neg_zero, F.map_zero_apply, add_zero]
  have hend : γ (b - a) = f (F (a - b) x) - b := by
    dsimp [γ]
    rw [neg_sub, show a + (b - a) = b by ring]
  have hzero (s : ℝ) (hs : s ∈ Set.Icc 0 (b - a)) (hgs : γ s = 0) : f x = a := by
    have hz : f (F (-s) x) = a + s := by dsimp [γ] at hgs; linarith
    have hh :=
      hshift (F (-s) x) s (by rw [hz]; constructor <;> linarith [hs.1, hs.2])
        (by rw [hz]; constructor <;> linarith)
    rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
    linarith
  have hzeroEnd (hx : f x = a) : γ (b - a) = 0 := by
    have hh :=
      hshift x (a - b) (by rw [hx]; exact ⟨le_rfl, hab⟩) (by rw [hx]; constructor <;> linarith)
    rw [hend]
    linarith
  constructor
  · intro hy
    by_contra hx
    have hx' : a < f x := lt_of_not_ge hx
    obtain ⟨s, hs, hgs⟩ :=
      intermediate_value_Icc' (sub_nonneg.mpr hab) hγ.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (γ (b - a)) (γ 0) by rw [hstart, hend]; constructor <;> linarith)
    linarith [hzero s hs hgs]
  · intro hx
    by_contra hy
    have hy' : b < f (F (a - b) x) := lt_of_not_ge hy
    obtain ⟨s, hs, hgs⟩ :=
      intermediate_value_Icc (sub_nonneg.mpr hab) hγ.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (γ 0) (γ (b - a)) by rw [hstart, hend]; constructor <;> linarith)
    have hh := hzeroEnd (hzero s hs hgs)
    rw [hend] at hh
    linarith

/-- The normalized flow's sublevel image. -/
theorem FlowTimeChange.normalized_flow_sublevel_image {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Set.Icc a b → f x - t ∈ Set.Icc a b → f (F t x) = f x - t) :
    F (a - b) '' {x : X | f x ≤ a} = {x : X | f x ≤ b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (normalized_flow_sublevel_iff F hf hab hshift x).mpr hx
  · intro hy
    have hi : F (a - b) (F (b - a) y) = y := by
      rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
    refine ⟨F (b - a) y, ?_, hi⟩
    apply (normalized_flow_sublevel_iff F hf hab hshift _).mp
    rw [hi]
    exact hy

/-- A positive integral clock for the flow exists. -/
theorem FlowTimeChange.exists_positive_integral_clock {a : ℝ → ℝ} (ha : Continuous a)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ t, δ ≤ a t) :
    ∃ c : ℝ ≃o ℝ,
      c 0 = 0 ∧
        (∀ t, c t = ∫ s in (0 : ℝ)..t, a s) ∧
          (∀ t, HasDerivAt c (a t) t) ∧ ∀ t, HasDerivAt c.symm (a (c.symm t))⁻¹ t := by
  let g : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s
  have hd (t : ℝ) : HasDerivAt g (a t) t :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hg : Differentiable ℝ g := fun t => (hd t).differentiableAt
  have hzero : g 0 = 0 := by simp [g]
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd (fun t => hδ.trans_le (hlower t))
  have hbound {s t : ℝ} (hst : s ≤ t) : δ * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv hg (fun t => by rw [(hd t).deriv]; exact hlower t) hst
  have hsurj : Function.Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨Min.min 0 (y / δ), ?_⟩
      have hh := hbound (min_le_left 0 (y / δ))
      have hm : δ * Min.min 0 (y / δ) ≤ y := by
        calc
          δ * Min.min 0 (y / δ) ≤ δ * (y / δ) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨Max.max 0 (y / δ), ?_⟩
      have hh := hbound (le_max_left 0 (y / δ))
      have hm : y ≤ δ * Max.max 0 (y / δ) := by
        calc
          y = δ * (y / δ) := by field_simp
          _ ≤ δ * Max.max 0 (y / δ) := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  refine ⟨c, hzero, fun _ => rfl, hd, ?_⟩
  intro t
  exact
    HasDerivAt.of_local_left_inverse c.symm.continuous.continuousAt (hd (c.symm t))
      (ne_of_gt (hδ.trans_le (hlower _))) (Filter.Eventually.of_forall c.apply_symm_apply)

/-- A native curve's positive reparametrization. -/
theorem FlowTimeChange.native_curve_positive_reparametrization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ρ : M → ℝ} {γ : ℝ → M} (hγ : IsMIntegralCurve γ V)
    {c : ℝ → ℝ} (hc : ∀ t, HasDerivAt c (ρ (γ (c t))) t) :
    IsMIntegralCurve (γ ∘ c) (fun x => ρ x • V x) := by
  intro t
  have hh := (hγ (c t)).comp t (hc t).hasFDerivAt.hasMFDerivAt
  have he :
    (1 : ℝ →L[ℝ] ℝ).smulRight (ρ (γ (c t)) • V (γ (c t))) =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ (c t)))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (ρ (γ (c t)))) := by
    ext
    simp [smul_smul, mul_comm]
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ c) t ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (γ (c t)) • V (γ (c t))))
  rw [he]
  exact hh

/-- A native flow time change exists. -/
theorem FlowTimeChange.exists_native_flow_time_change {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {ρ : M → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hW :
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) (fun y => ρ y • V y)) (x : M) :
    ∃ c : ℝ ≃o ℝ,
      c 0 = 0 ∧
        (∀ t, c t = ∫ s in (0 : ℝ)..t, (ρ (F s x))⁻¹) ∧
          (∀ t, HasDerivAt c.symm (ρ (F (c.symm t) x)) t) ∧ ∀ t, G t x = F (c.symm t) x := by
  obtain ⟨R, hR⟩ := (isCompact_univ.image hρ).bddAbove
  have hbound (y : M) : ρ y ≤ R := hR ⟨y, Set.mem_univ _, rfl⟩
  have hRpos : 0 < R := (hρpos x).trans_le (hbound x)
  have ha : Continuous (fun t => (ρ (F t x))⁻¹) :=
    (hρ.comp (F.continuous continuous_id continuous_const)).inv₀ (fun t => (hρpos _).ne')
  have hlower (t : ℝ) : R⁻¹ ≤ (ρ (F t x))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hρpos (F t x)) (hbound (F t x))
  obtain ⟨c, hc0, hcint, -, hcinv⟩ := exists_positive_integral_clock ha (inv_pos.mpr hRpos) hlower
  have hcinv' (t : ℝ) : HasDerivAt c.symm (ρ (F (c.symm t) x)) t := by
    simpa only [inv_inv] using hcinv t
  have hcurve := native_curve_positive_reparametrization (hF x) hcinv'
  have hc0' : c.symm 0 = 0 := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact hc0.symm
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hW (hG x) hcurve (t₀ := 0)
      (by simp only [Function.comp_apply, hc0', F.map_zero_apply, G.map_zero_apply])
  exact ⟨c, hc0, hcint, hcinv', fun t => congrFun heq t⟩

/-- The time-changed flow has the same orbits. -/
theorem FlowTimeChange.native_flow_time_change_orbits {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {ρ : M → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hW :
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) (fun y => ρ y • V y)) (x : M) :
    Set.range (fun t => G t x) = Set.range (fun t => F t x) ∧
      (∀ p,
          Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) ↔
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) ∧
        ∀ p,
          Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
            Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  obtain ⟨c, -, -, -, heq⟩ := exists_native_flow_time_change hρ hρpos hW F G hF hG x
  have heq' (t : ℝ) : F t x = G (c t) x := by rw [heq, c.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨c.symm t, (heq t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨c t, (heq' t).symm⟩
  · intro p
    constructor
    · intro h
      exact (h.comp c.tendsto_atTop).congr (fun t => (heq' t).symm)
    · intro h
      exact (h.comp c.symm.tendsto_atTop).congr (fun t => (heq t).symm)
  · intro p
    constructor
    · intro h
      exact (h.comp c.tendsto_atBot).congr (fun t => (heq' t).symm)
    · intro h
      exact (h.comp c.symm.tendsto_atBot).congr (fun t => (heq t).symm)

/-- An orbit-preserving band normalization exists. -/
theorem FlowTimeChange.exists_orbit_preserving_band_normalization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (U : Set ℝ) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M),
      IsOpen U ∧
        Set.Icc a b ⊆ U ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ x,
                    x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
                  (∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (W x) = -1) ∧
                    (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                      (∀ x, ∃ c : ℝ ≃o ℝ, c 0 = 0 ∧ ∀ t, G t x = F (c.symm t) x) ∧
                        ∀ x,
                          Set.range (fun t => G t x) = Set.range (fun t => F t x) ∧
                            (∀ p,
                                Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) ↔
                                  Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) ∧
                              ∀ p,
                                Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
                                  Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  obtain ⟨ρ, U, hU, hAU, hρ, hpos, hW, hzeros, hneg, hspeed, hgerm⟩ :=
    MorseCancellation.exists_positive_band_normalization hf hV hdesc hband
  have hW₁ := hW.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let W : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => ρ x • V x
  let G := FlowConstruction.compactFlow hW₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) W :=
    FlowConstruction.isMIntegralCurve_compactFlow hW₁ x
  refine ⟨U, W, G, hU, hAU, hW, hG, hzeros, hneg, hspeed, ?_, ?_, ?_⟩
  · intro x hx
    filter_upwards [hgerm x hx] with y hy
    simp only [W, hy, one_smul]
  · intro x
    obtain ⟨c, hc0, -, -, heq⟩ :=
      exists_native_flow_time_change hρ.continuous hpos hW₁ F G hF hG x
    exact ⟨c, hc0, heq⟩
  · exact native_flow_time_change_orbits hρ.continuous hpos hW₁ F G hF hG

/-- An orbit-preserving ambient band bridge exists. -/
theorem FlowTimeChange.exists_orbit_preserving_ambient_band_bridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧
        D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} ∧ ∀ x, ∃ t, F t x = D x := by
  obtain ⟨U, W, G, hU, hIU, hW, hG, -, -, hspeed, -, -, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hf hV hdesc F hF hband
  have hshift := native_local_height_translation hf G hG hU hIU hspeed
  let D := SmoothODE.nativeFlowTimeDiffeomorph_of_field hW G hG (a - b)
  refine
    ⟨D, normalized_flow_level_image G hab hshift,
      normalized_flow_sublevel_image G hf.continuous hab hshift, ?_⟩
  intro x
  have hm : D x ∈ Set.range (fun t => G t x) := ⟨a - b, rfl⟩
  rw [(hgeometry x).1] at hm
  exact hm

/-- An orbit-preserving native band bridge exists. -/
theorem FlowTimeChange.exists_orbit_preserving_native_band_bridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f)
    (ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf ha
    letI := RegularLevel.chartedSpace hf hb
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          { x : M // f x = a } { x : M // f x = b } ∞,
        D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} ∧
          (∀ x, (e x : M) = D x) ∧ ∀ x, ∃ t, F t x = D x := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨D, hlevel, hsublevel, horbit⟩ :=
    exists_orbit_preserving_ambient_band_bridge hf hV hdesc F hF hab hband
  obtain ⟨e, he⟩ := RegularLevel.exists_levelDiffeomorph_of_ambient hf ha hb D hlevel
  exact ⟨D, e, hsublevel, he, horbit⟩

end
