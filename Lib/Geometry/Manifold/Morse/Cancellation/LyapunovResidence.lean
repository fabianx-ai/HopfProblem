/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.NoReturn

/-!
# Lyapunov residence bounds and uniform band crossings

A flow line of a vector field `V` cannot stay in a compact set `C` on which a
smooth function `f` strictly decreases along `V`: the time spent in `C` is
bounded by `(max_C f - min_C f + 1) / δ`, where `-δ` bounds the directional
derivative (`FlowCancellation.exists_native_lyapunov_residence` on a manifold,
`MorseCancellation.exists_compact_lyapunov_residence` in a normed space, and
its chart transport `exists_native_compact_lyapunov_residence`).

Two residence bounds combine when orbits cannot leave and re-enter an inner set
(`combine_native_residence_bounds`), which gives a residence bound in a band
`f ⁻¹' (Icc c d)` for a field perturbed inside a closed set
(`exists_perturbed_band_residence`).

If moreover `f` decreases along `V` on the two boundary levels, a uniform
residence bound yields a time `T` after which every point below `d` lies
strictly below `c` and before which every point above `c` lay strictly above
`d` (`exists_uniform_directed_band_crossing`); the entry time into the
sublevel `{f ≤ c}` is then continuous on `{f ≤ d}`
(`continuousOn_band_entryTime`, `exists_native_flow_band_crossing`).

This is the quantitative form of the gradient-like flow estimates used in
Milnor, *Lectures on the h-cobordism theorem*, §4 and §5.

## Tags

gradient-like-flow, lyapunov-function, band-crossing
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Lyapunov residence bounds -/

/-- A native Lyapunov residence bound exists. -/
theorem FlowCancellation.exists_native_lyapunov_residence {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {C : Set M} (hC : IsCompact C) (hneg : ∀ x ∈ C, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ => ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -mvfderiv 𝓘(ℝ, E) f v (V v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
    have hh : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f v (V v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hf.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hf.continuous.continuousOn
  let T := (f q - f p + 1) / δ
  have hpq : f p ≤ f q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = f q - f p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf hγ t
  have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
      hdiff.differentiableOn
      (fun t ht => by
        rw [(hd t).deriv]
        exact hbound (γ t) (hstay t (interior_subset ht)))
      0 h0 T hlast hT.le
  simp only [Function.comp_apply, sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
  have hhi : f (γ 0) ≤ f q := hmax (hstay 0 h0)
  linarith

/-- Native residence bounds combine. -/
theorem FlowCancellation.combine_native_residence_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {B N U : Set M}
    (houter :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ B \ N)
    (hinner :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U)
    (hnoreturn :
      ∀ γ : ℝ → M,
        IsMIntegralCurve γ V → ∀ a b : ℝ, γ a ∈ N → γ b ∈ N → ∀ t ∈ Set.Icc a b, γ t ∈ U) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ B := by
  obtain ⟨T₀, hT₀, hout⟩ := houter
  obtain ⟨T₁, hT₁, hin⟩ := hinner
  refine ⟨2 * T₀ + T₁, by linarith, ?_⟩
  intro γ hγ
  by_contra! hstay
  obtain ⟨a, ha, haout⟩ := hout γ hγ
  have haN : γ a ∈ N := by
    by_contra haN
    exact haout ⟨hstay a ⟨ha.1, by linarith [ha.2]⟩, haN⟩
  obtain ⟨b, hb, hbout⟩ := hout (γ ∘ (· + (T₀ + T₁))) (hγ.comp_add (T₀ + T₁))
  have hbN : γ (b + (T₀ + T₁)) ∈ N := by
    by_contra hbN
    exact hbout ⟨hstay (b + (T₀ + T₁)) ⟨by linarith [hb.1], by linarith [hb.2]⟩, hbN⟩
  obtain ⟨t, ht, htout⟩ := hin (γ ∘ (· + T₀)) (hγ.comp_add T₀)
  exact
    htout
      (hnoreturn γ hγ a (b + (T₀ + T₁)) haN hbN (t + T₀)
        ⟨by linarith [ha.2, ht.1], by linarith [hb.1, ht.2]⟩)

/-- A perturbed band residence bound exists. -/
theorem FlowCancellation.exists_perturbed_band_residence {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
    {V' : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hV' : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} {K N U : Set M}
    (hK : IsClosed K) (hN : IsOpen N) (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hneg : ∀ x, f x ∈ Set.Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U)
    (hinner :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U) :
    ∃ T : ℝ,
      0 < T ∧
        ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d := by
  have hcompact : IsCompact (f ⁻¹' Set.Icc c d \ N) :=
    ((isClosed_Icc.preimage hf.continuous).inter hN.isClosed_compl).isCompact
  have houter :=
    exists_native_lyapunov_residence hf hV' hcompact
      (by
        intro x hx
        rw [hoff x (fun h => hx.2 (hKN h))]
        exact hneg x hx.1 hx.2)
  exact
    combine_native_residence_bounds houter hinner
      (fun γ hγ a b ha hb =>
        native_no_return_of_supported_perturbation (hV.of_le (by simp)) F hcurve hK hKN hNU hoff
          hnoreturn hγ ha hb)

/-! ### Compact Lyapunov residence -/

/-- A compact Lyapunov residence bound exists. -/
theorem MorseCancellation.exists_compact_lyapunov_residence {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W)
    {C : Set D} (hC : IsCompact C) (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0) :
    ∃ T : ℝ,
      0 < T ∧
        ∀ γ : ℝ → D,
          (∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∈ C → HasDerivAt γ (W (γ t)) t) →
            ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ => ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed : Continuous (fun x => fderiv ℝ L x (W x)) :=
    (hL.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk hW)
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -fderiv ℝ L v (W v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : D) (hx : x ∈ C) : fderiv ℝ L x (W x) ≤ -δ := by
    have hh : fderiv ℝ L x (W x) ≤ fderiv ℝ L v (W v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hL.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hL.continuous.continuousOn
  let T := (L q - L p + 1) / δ
  have hpq : L p ≤ L q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = L q - L p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun u => L (γ u)) (fderiv ℝ L (γ t) (W (γ t))) t :=
    (hL.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t ht (hstay t ht))
  have hcont : ContinuousOn (fun t => L (γ t)) (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t => L (γ t)) (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hd t ht).differentiableAt.differentiableWithinAt
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hcont (hdiff.mono interior_subset)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        exact hbound (γ t) (hstay t (interior_subset ht)))
      0 h0 T hlast hT.le
  simp only [sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : L p ≤ L (γ T) := hmin (hstay T hlast)
  have hhi : L (γ 0) ≤ L q := hmax (hstay 0 h0)
  linarith

/-- A partial chart integral curve's derivative. -/
theorem MorseCancellation.hasDerivAt_partialChart_integralCurve {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, D) M D ∞) (W : D → D)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ}
    (ht : γ t ∈ e.source) (hV : V (γ t) = FlowConstruction.partialChartField e W (γ t)) :
    HasDerivAt (e ∘ γ) (W (e (γ t))) t := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, D) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hinv := he.comp_symm_deriv (e'.map_source ht)
  rw [e'.left_inv ht] at hinv
  have hd := (he.mdifferentiableAt ht).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D) e (γ t) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) •
        (NormedSpace.fromTangentSpace (e (γ t))).symm (W (e (γ t)))
  rw [map_smul, hV, FlowConstruction.partialChartField_eq_mfderiv_symm e W ht]
  have hv := congrArg (fun A : D →L[ℝ] D => A (W (e (γ t)))) hinv
  exact congrArg (fun v => (NormedSpace.fromTangentSpace t r) • v) hv

/-- A native compact Lyapunov residence bound exists. -/
theorem MorseCancellation.exists_native_compact_lyapunov_residence {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W) {C : Set D}
    (hC : IsCompact C) (hsource : C ⊆ Φ.source) (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ∀ x ∈ Φ '' C, V x = FlowConstruction.partialChartField Φ.symm W x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨T, hT, hTbound⟩ := exists_compact_lyapunov_residence hL hW hC hneg
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hcoords (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : Φ.symm (γ t) ∈ C := by
    obtain ⟨z, hz, he⟩ := hstay t ht
    have hh : Φ.symm (Φ z) = z := Φ.left_inv' (hsource hz)
    rw [← he, hh]
    exact hz
  obtain ⟨t, ht, hout⟩ :=
    hTbound (Φ.symm ∘ γ)
      (fun t ht _ =>
        hasDerivAt_partialChart_integralCurve Φ.symm W hγ
          (by
            obtain ⟨z, hz, he⟩ := hstay t ht
            exact he ▸ Φ.map_source' (hsource hz))
          (hV (γ t) (hstay t ht)))
  exact hout (hcoords t ht)

/-! ### Band crossings -/

/-- A uniform directed band crossing exists. -/
theorem FlowCancellation.exists_uniform_directed_band_crossing {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d) :
    ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x) := by
  obtain ⟨T, hT, hexit⟩ := hres
  have hforward : ∀ x, f x ≤ d → f (F T x) < c := by
    intro x hx
    obtain ⟨t, ht, hout⟩ := hexit x
    have hhi := forwardInvariant_sublevel_of_boundary F hf hD hder hupper x hx t ht.1
    have hlo : f (F t x) < c := lt_of_not_ge (fun h => hout ⟨h, hhi⟩)
    rcases ht.2.eq_or_lt with he | he
    · simpa only [he] using hlo
    · have hh :=
        strict_sublevel_entry_of_boundary F hf hD hder hlower (F t x) hlo.le (T - t)
          (sub_pos.mpr he)
      simpa only [← F.map_add, sub_add_cancel] using hh
  refine ⟨T, hT, hforward, ?_⟩
  intro x hx
  apply lt_of_not_ge
  intro hback
  have hh := hforward (F (-T) x) hback
  rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
  exact (not_lt_of_ge hx) hh

/-- The band entry time is continuous. -/
theorem FlowCancellation.continuousOn_band_entryTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d) :
    ContinuousOn (FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  obtain ⟨T, hT, hforward, -⟩ :=
    exists_uniform_directed_band_crossing F hf hD hder hlower hupper hres
  have hclosed : IsClosed {x | f x ≤ c} := isClosed_le hf continuous_const
  have hentry : ∀ x ∈ {y | f y ≤ c}, ∀ t : ℝ, 0 < t → F t x ∈ interior {y | f y ≤ c} := by
    intro x hx t ht
    have hh := strict_sublevel_entry_of_boundary F hf hD hder hlower x hx t ht
    exact
      Eq.mpr
        (congrArg (fun S : Set X => F t x ∈ S)
          (interior_sublevel_eq_of_boundary F hf hder hlower))
        hh
  exact
    FlowConstruction.continuousOn_entryTime F hclosed
      (forwardInvariant_sublevel_of_boundary F hf hD hder hlower) hentry
      (fun x hx => ⟨T, hT.le, (hforward x hx).le⟩)

/-- A native flow band crossing exists. -/
theorem FlowCancellation.exists_native_flow_band_crossing {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {c d : ℝ} (hlower : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hupper : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hres :
      ∃ T : ℝ,
        0 < T ∧
          ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d) :
    ∃ F : Flow ℝ M,
      (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
        (∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) ∧
          ContinuousOn (FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let F := FlowConstruction.compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V :=
    FlowConstruction.isMIntegralCurve_compactFlow hV₁ x
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hres' : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d := by
    obtain ⟨T, hT, hbound⟩ := hres
    exact ⟨T, hT, fun x => hbound (fun t => F t x) (hcurve x)⟩
  exact
    ⟨F, hcurve, exists_uniform_directed_band_crossing F hf.continuous hD hder hlower hupper hres',
      continuousOn_band_entryTime F hf.continuous hD hder hlower hupper hres'⟩

end
