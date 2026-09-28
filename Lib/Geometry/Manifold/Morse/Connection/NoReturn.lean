/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement

/-!
# No-return neighbourhoods of an isolated connecting orbit

For a flow `F` on a compact space decreasing a continuous height `f`:

* `exists_uniform_flow_escape`: if every point of a compact set leaves a band `[c, d]` in finite
  time, it does so uniformly and by a definite margin;
* `exists_flow_no_return_neighborhood`: a compact invariant set `K ⊆ U` filling the band has an
  open neighbourhood `N ⊆ U` such that an orbit leaving `N` and re-entering it stays in `U` in
  between;
* `invariant_band_subset_connection`, `exists_isolated_connection_no_return`,
  `exists_native_connection_no_return`: if the critical points `p`, `q` are the only ones in the
  band `[f p, f q]` and `z` is the unique orbit from `q` to `p`, then everything staying in the
  band is `p`, `q` or the orbit of `z`, and `{p, q} ∪ orbit z` has such a no-return
  neighbourhood.

Stability under perturbation: an integral curve of a field `V'` that agrees with `V` outside a
closed set `K ⊆ N` stays in `U` between two visits to `N`
(`native_no_return_of_supported_perturbation`, via `exists_excursion_interval` and
`native_curve_eq_flow_on_closed_interval`); `contMDiff_supported_division` is the smoothness of
a quotient `χ / D` with `D ≠ 0` on the support of `χ`.

cf. Milnor, *Lectures on the h-cobordism theorem*, §5 (the alteration of the gradient-like field
is supported near the single trajectory).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Omega limits and connections -/

/-- A uniform flow escape time exists. -/
theorem FlowCancellation.exists_uniform_flow_escape {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {C : Set X} (hC : IsCompact C) {c d : ℝ}
    (hescape : ∀ x ∈ C, ∃ t : ℝ, f (F t x) ∉ Set.Icc c d) :
    ∃ T : ℝ,
      0 < T ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∃ t ∈ Set.Icc (-T) T, f (F t x) < c - δ ∨ d + δ < f (F t x) := by
  classical
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, by norm_num, 1, by norm_num, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let J := { p : ℝ × ℝ // 0 < p.2 }
  let O : J → Set X := fun p =>
    {x | f (F p.val.1 x) < c - p.val.2 ∨ d + p.val.2 < f (F p.val.1 x)}
  have hO (p : J) : IsOpen (O p) :=
    (isOpen_lt (hf.comp (F.continuous_toFun p.val.1)) continuous_const).union
      (isOpen_lt continuous_const (hf.comp (F.continuous_toFun p.val.1)))
  have hcover : C ⊆ ⋃ p, O p := by
    intro x hx
    obtain ⟨t, ht⟩ := hescape x hx
    by_cases hl : c ≤ f (F t x)
    · have hr : d < f (F t x) := lt_of_not_ge (fun h => ht ⟨hl, h⟩)
      have hδ : 0 < (f (F t x) - d) / 2 := by linarith
      apply Set.mem_iUnion.mpr
      refine ⟨⟨(t, (f (F t x) - d) / 2), hδ⟩, Or.inr ?_⟩
      change d + (f (F t x) - d) / 2 < f (F t x)
      linarith
    · have hl' : f (F t x) < c := lt_of_not_ge hl
      have hδ : 0 < (c - f (F t x)) / 2 := by linarith
      apply Set.mem_iUnion.mpr
      refine ⟨⟨(t, (c - f (F t x)) / 2), hδ⟩, Or.inl ?_⟩
      change f (F t x) < c - (c - f (F t x)) / 2
      linarith
  obtain ⟨S, hScover⟩ := hC.elim_finite_subcover O hO hcover
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, -⟩ := Set.mem_iUnion₂.mp (hScover hx)
    exact ⟨p, hp⟩
  let T := S.sup' hS (fun p => |p.val.1|) + 1
  let δ := S.inf' hS (fun p => p.val.2) / 2
  have hmin : 0 < S.inf' hS (fun p => p.val.2) :=
    (Finset.lt_inf'_iff hS).mpr (fun p _ => p.property)
  have hT : 0 < T := by
    obtain ⟨p, hp⟩ := hS
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    have habs := abs_nonneg p.val.1
    dsimp [T]
    linarith
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  refine ⟨T, hT, δ, hδ, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.mp (hScover hx)
  have ht : |p.val.1| ≤ T := by
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    dsimp [T]
    linarith
  have hd : δ ≤ p.val.2 := by
    have hh := Finset.inf'_le (fun p : J => p.val.2) hp
    dsimp [δ]
    linarith
  refine ⟨p.val.1, abs_le.mp ht, ?_⟩
  rcases hpx with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- A no-return neighborhood of an orbit exists. -/
theorem FlowCancellation.exists_flow_no_return_neighborhood {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {c d : ℝ} {K U : Set X} (hU : IsOpen U)
    (hKU : K ⊆ U) (hband : ∀ x ∈ K, f x ∈ Set.Icc c d) (hinvariant : ∀ t x, x ∈ K → F t x ∈ K)
    (hmaximal : ∀ x, (∀ t : ℝ, f (F t x) ∈ Set.Icc c d) → x ∈ K) :
    ∃ N : Set X,
      IsOpen N ∧
        K ⊆ N ∧
          N ⊆ U ∧ ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  have hescape : ∀ x ∈ Uᶜ, ∃ t : ℝ, f (F t x) ∉ Set.Icc c d := by
    intro x hx
    by_contra hh
    apply hx
    apply hKU
    apply hmaximal x
    intro t
    by_contra ht
    exact hh ⟨t, ht⟩
  obtain ⟨T, hT, δ, hδ, hEsc⟩ :=
    exists_uniform_flow_escape F hf hU.isClosed_compl.isCompact hescape
  let N : Set X := {x | ∀ s ∈ Set.Icc (-T) T, F s x ∈ U} ∩ f ⁻¹' Set.Ioo (c - δ) (d + δ)
  have hN : IsOpen N :=
    (MorsePerturbation.isOpen_forall_mem_compact CompactIccSpace.isCompact_Icc
          (hU.preimage (F.continuous continuous_snd continuous_fst))).inter
      (isOpen_Ioo.preimage hf)
  have hKN : K ⊆ N := by
    intro x hx
    refine ⟨fun s _ => hKU (hinvariant s x hx), ?_⟩
    have hh := hband x hx
    constructor <;> linarith [hh.1, hh.2]
  have hNU : N ⊆ U := by
    intro x hx
    have hh := hx.1 0 (show (0 : ℝ) ∈ Set.Icc (-T) T from ⟨by linarith, hT.le⟩)
    simpa only [F.map_zero_apply] using hh
  refine ⟨N, hN, hKN, hNU, ?_⟩
  intro x hx t ht htx s hs
  by_cases hshort : s ≤ T
  · exact hx.1 s ⟨by linarith [hs.1], hshort⟩
  have hTs : T < s := lt_of_not_ge hshort
  by_cases hshort' : t - s ≤ T
  · have hh := htx.1 (s - t) (show s - t ∈ Set.Icc (-T) T from ⟨by linarith, by linarith [hs.2]⟩)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  have hTs' : T < t - s := lt_of_not_ge hshort'
  by_contra hout
  obtain ⟨v, hv, hleave⟩ := hEsc (F s x) hout
  have htime : s + v ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hlo := hmono x htime.1
  have hhi := hmono x htime.2
  change f (F (s + v) x) ≤ f (F 0 x) at hlo
  change f (F t x) ≤ f (F (s + v) x) at hhi
  rw [F.map_zero_apply] at hlo
  rw [← F.map_add, add_comm v s] at hleave
  have hxheight : f x ∈ Set.Ioo (c - δ) (d + δ) := hx.2
  have htheight : f (F t x) ∈ Set.Ioo (c - δ) (d + δ) := htx.2
  rcases hleave with h | h
  · linarith [htheight.1]
  · linarith [hxheight.2]

/-- An invariant band lies in the connection. -/
theorem FlowCancellation.invariant_band_subset_connection {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {S : Set X}
    (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q z : X}
    (hpair : ∀ x ∈ S, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hunique :
      ∀ x ∉ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {x : X} (hstay : ∀ t : ℝ, f (F t x) ∈ Set.Icc (f p) (f q)) :
    x ∈ ({ p, q } : Set X) ∪ Set.range (fun t : ℝ => F t z) := by
  have hxband : f x ∈ Set.Icc (f p) (f q) := by simpa only [F.map_zero_apply] using hstay 0
  by_cases hxS : x ∈ S
  · rcases hpair x hxS hxband with rfl | rfl <;> exact Or.inl (by simp)
  obtain ⟨r, hr, s, hs, hrlim, hslim, hsep⟩ :=
    exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrband : f r ∈ Set.Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hrlim)
      (Filter.Eventually.of_forall hstay)
  have hsband : f s ∈ Set.Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hslim)
      (Filter.Eventually.of_forall hstay)
  have hsep' := hsep hxS
  have hrq : r = q :=
    (hpair r hr hrband).resolve_left
      (by
        intro he
        rw [he] at hsep'
        linarith [hxband.1])
  have hsp : s = p :=
    (hpair s hs hsband).resolve_right
      (by
        intro he
        rw [he] at hsep'
        linarith [hxband.2])
  obtain ⟨t, ht⟩ :=
    hunique x hxS (by simpa only [hrq] using hrlim) (by simpa only [hsp] using hslim)
  exact Or.inr ⟨t, ht⟩

/-- An isolated connection has a no-return neighborhood. -/
theorem FlowCancellation.exists_isolated_connection_no_return {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {S : Set X} (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    (hfixed : ∀ x ∈ S, ∀ t : ℝ, F t x = x) {p q z : X} (hp : p ∈ S) (hq : q ∈ S) (hpq : f p < f q)
    (hpair : ∀ x ∈ S, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Set.Icc (f p) (f q))
    (hunique :
      ∀ x ∉ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U) (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set X,
      IsOpen N ∧
        N ⊆ U ∧
          p ∈ N ∧
            q ∈ N ∧
              (∀ t : ℝ, F t z ∈ N) ∧
                ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  let K : Set X := {x | ∀ t : ℝ, f (F t x) ∈ Set.Icc (f p) (f q)}
  have hKU : K ⊆ U := by
    intro x hx
    rcases invariant_band_subset_connection F hf hinj hmono hstrict hpair hunique hx with h |
      ⟨t, rfl⟩
    · rcases h with h | h
      · exact h ▸ hpU
      · exact (show x = q from h) ▸ hqU
    · exact hzU t
  have hKband (x : X) (hx : x ∈ K) : f x ∈ Set.Icc (f p) (f q) := by
    simpa only [F.map_zero_apply] using hx 0
  have hKi (t : ℝ) (x : X) (hx : x ∈ K) : F t x ∈ K := by
    intro s
    rw [← F.map_add]
    exact hx (s + t)
  obtain ⟨N, hN, hKN, hNU, hreturn⟩ :=
    exists_flow_no_return_neighborhood F hf hmono hU hKU hKband hKi (fun _ h => h)
  have hpK : p ∈ K := by
    intro t
    rw [hfixed p hp t]
    exact ⟨le_rfl, hpq.le⟩
  have hqK : q ∈ K := by
    intro t
    rw [hfixed q hq t]
    exact ⟨hpq.le, le_rfl⟩
  exact ⟨N, hN, hNU, hKN hpK, hKN hqK, fun t => hKN (hKi t z hzband), hreturn⟩

/-- A native connection has a no-return neighborhood. -/
theorem FlowCancellation.exists_native_connection_no_return {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) {p q z : M}
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hpair :
      ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Set.Icc (f p) (f q))
    (hunique :
      ∀ x ∉ ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U) (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set M,
      IsOpen N ∧
        N ⊆ U ∧
          p ∈ N ∧
            q ∈ N ∧
              (∀ t : ℝ, F t z ∈ N) ∧
                ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  exact
    exists_isolated_connection_no_return F hf.continuous hinj
      (FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
      (fun x hx => FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx)
      (fun x hx t => FlowConstruction.flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t) hp hq
      hpq hpair hzband hunique hU hpU hqU hzU

section

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2

/-! ### Supported divisions and no-return perturbations -/

/-- A supported division of smooth functions is smooth. -/
theorem MorseCancellation.contMDiff_supported_division {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {χ D : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ) (hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D)
    (hsupp : ∀ x ∈ tsupport χ, D x ≠ 0) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => χ x / D x) := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ x).div₀ (hD x) (hsupp x hx)
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_div]

/-- An excursion interval outside a no-return set exists. -/
theorem FlowCancellation.exists_excursion_interval {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} (hγ : Continuous γ) {K N : Set X} (hK : IsClosed K) (hKN : K ⊆ N) {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) (ha : γ a ∈ N) (hb : γ b ∈ N) (hout : γ t ∉ N) :
    ∃ s u : ℝ, a ≤ s ∧ s < t ∧ t < u ∧ u ≤ b ∧ γ s ∈ N ∧ γ u ∈ N ∧ ∀ r ∈ Set.Ioo s u, γ r ∉ K := by
  let A := Insert.insert a (Set.Icc a t ∩ γ ⁻¹' K)
  let B := Insert.insert b (Set.Icc t b ∩ γ ⁻¹' K)
  have hA : IsCompact A := (CompactIccSpace.isCompact_Icc.inter_right (hK.preimage hγ)).insert a
  have hB : IsCompact B := (CompactIccSpace.isCompact_Icc.inter_right (hK.preimage hγ)).insert b
  obtain ⟨s, hs⟩ := hA.exists_isGreatest (Set.insert_nonempty _ _)
  obtain ⟨u, hu⟩ := hB.exists_isLeast (Set.insert_nonempty _ _)
  have has : a ≤ s := hs.2 (Set.mem_insert _ _)
  have hub : u ≤ b := hu.2 (Set.mem_insert _ _)
  have hst : s ≤ t := by
    rcases hs.1 with he | hh
    · exact he ▸ ht.1
    · exact hh.1.2
  have htu : t ≤ u := by
    rcases hu.1 with he | hh
    · exact he ▸ ht.2
    · exact hh.1.1
  have hsN : γ s ∈ N := by
    rcases hs.1 with he | hh
    · exact he ▸ ha
    · exact hKN hh.2
  have huN : γ u ∈ N := by
    rcases hu.1 with he | hh
    · exact he ▸ hb
    · exact hKN hh.2
  have hst' : s < t := lt_of_le_of_ne hst (fun he => hout (he ▸ hsN))
  have htu' : t < u := lt_of_le_of_ne htu (fun he => hout (he ▸ huN))
  refine ⟨s, u, has, hst', htu', hub, hsN, huN, ?_⟩
  intro r hr hrK
  by_cases hrt : r ≤ t
  · have hrA : r ∈ A := Or.inr ⟨⟨le_trans has hr.1.le, hrt⟩, hrK⟩
    exact (not_le_of_gt hr.1) (hs.2 hrA)
  · have hrB : r ∈ B := Or.inr ⟨⟨(lt_of_not_ge hrt).le, le_trans hr.2.le hub⟩, hrK⟩
    exact (not_le_of_gt hr.2) (hu.2 hrB)

/-- A native curve equals the flow on a closed interval. -/
theorem FlowCancellation.native_curve_eq_flow_on_closed_interval {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {γ : ℝ → M}
    (hγcont : Continuous γ) {a b c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hγ : IsMIntegralCurveOn γ V (Set.Ioo a b)) : ∀ t ∈ Set.Icc a b, γ t = F (t - c) (γ c) := by
  have hF : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have he : (fun t => F (t - c) (γ c)) = ((fun t => F t (γ c)) ∘ (· + -c)) := by
      funext t
      simp only [Function.comp_apply, sub_eq_add_neg]
    rw [he]
    exact (hcurve (γ c)).comp_add (-c)
  have heq : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ (hF.isMIntegralCurveOn _)
      (by simp)
  have heqclosed := heq.closure hγcont hF.continuous
  rw [closure_Ioo (lt_trans hc.1 hc.2).ne] at heqclosed
  exact heqclosed

/-- A supported perturbation preserves the no-return property. -/
theorem FlowCancellation.native_no_return_of_supported_perturbation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {K N U : Set M}
    (hK : IsClosed K) (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V') {a b : ℝ} (ha : γ a ∈ N) (hb : γ b ∈ N) :
    ∀ t ∈ Set.Icc a b, γ t ∈ U := by
  intro t ht
  by_contra hout
  obtain ⟨s, u, -, hst, htu, -, hsN, huN, havoid⟩ :=
    exists_excursion_interval hγ.continuous hK hKN ht ha hb (fun hh => hout (hNU hh))
  have hold : IsMIntegralCurveOn γ V (Set.Ioo s u) := by
    intro r hr
    have hd := (hγ r).hasMFDerivWithinAt (s := Set.Ioo s u)
    rw [hoff (γ r) (havoid r hr)] at hd
    exact hd
  have heq :=
    native_curve_eq_flow_on_closed_interval hV F hcurve hγ.continuous
      (show t ∈ Set.Ioo s u from ⟨hst, htu⟩) hold
  have hs : γ s = F (s - t) (γ t) := heq s ⟨le_rfl, (lt_trans hst htu).le⟩
  have hu : γ u = F (u - t) (γ t) := heq u ⟨(lt_trans hst htu).le, le_rfl⟩
  have hend : F (u - s) (γ s) = γ u := by
    rw [hs, ← F.map_add, show u - s + (s - t) = u - t by ring, ← hu]
  have hmid : F (t - s) (γ s) = γ t := by
    rw [hs, ← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply]
  have hh :=
    hnoreturn (γ s) hsN (u - s) (sub_nonneg.mpr (lt_trans hst htu).le) (hend ▸ huN) (t - s)
      ⟨sub_nonneg.mpr hst.le, sub_le_sub_right htu.le s⟩
  exact hout (hmid ▸ hh)

end

end
