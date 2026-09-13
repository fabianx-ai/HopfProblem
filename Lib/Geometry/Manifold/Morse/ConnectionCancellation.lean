/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement

/-!
# Cancellation along a transverse connection

The first cancellation theorem with explicit flow and germ control. The
headline `MorseCancellation.cancel_of_transverse_level_isotopy` starts with
an excellent Morse function on a compact finite-dimensional smooth manifold,
a pair of critical points of adjacent index, and an isotopy of a regular
level giving one transverse connecting orbit. It produces a smooth Morse
function whose critical set is precisely the old set minus the chosen pair,
whose critical-point count drops by two, and whose germ is unchanged outside
the isolating band. Its declaration states the full chart, flow, separation,
and transversality hypotheses.

## Outline of the proof

1. Positive clocks, phase charts and isotopy suspension control the regular
   level cylinder (`FlowTimeChange`, `FlowSuspension`, `TransverseGerms`).
2. Endpoint matching and three-chart gluing construct the full cubic field
   chart (`MorseCancellation.exists_full_cubic_chart_from_corrected_cylinder`).
3. Finite residence estimates give a replacement band Lyapunov function
   (`FlowCancellation.exists_global_band_lyapunov`).
4. `MorseCancellation.NativeConnectionCancellationData.cancel` removes the
   pair while preserving the remaining critical germs.
5. Native basin-sheet transversality and the regular-level isotopy realization
   supply that cancellation data to `cancel_of_transverse_level_isotopy`.

The clock, chart-overlap and germ lemmas make explicit the coordinate
bookkeeping in the textbook cancellation argument. The cubic core already
in `Cancellation.lean` is imported, not duplicated. The shared Hessian and
critical-point counting lemmas at the end also support the birth construction.

## Main definitions and results

* `MorseCancellation.NativeConnectionCancellationData.Transverse`.
* `MorseCancellation.NativeConnectionCancellationData.cancel`.
* `MorseCancellation.cancel_of_transverse_level_isotopy`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4.

## Tags

morse-theory, cancellation, gradient-like-flow, h-cobordism
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

section

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2

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

end

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

theorem FlowSuspension.flow_complement_invariant {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S : Set X} (hS : ∀ x ∈ S, ∀ t, F t x ∈ S) : ∀ x ∉ S, ∀ t, F t x ∉ S := by
  intro x hx t ht
  have hh := hS (F t x) ht (-t)
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  exact hx hh

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

theorem FlowSuspension.nativeSuspensionFlow_chart {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) (t : ℝ)
    (p : N × ℝ) : nativeSuspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

def FlowSuspension.nativeVerticalField {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N] (p : N × ℝ) :
    TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p :=
  (show Z × ℝ from (0, 1))

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

def FlowSuspension.nativeSuspensionField {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (p : N × ℝ) : TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p :=
  mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (Ψ.symm p)
    (nativeVerticalField (Ψ.symm p))

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

theorem FlowTimeChange.mfderiv_height_div_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (r : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y / r) x = r⁻¹ • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : (fun y => f y / r) = r⁻¹ • f := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact (hf.hasMFDerivAt.const_smul r⁻¹).mfderiv

theorem FlowTimeChange.mvfderiv_height_div_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (r : ℝ) (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => f y / r) x v = mvfderiv 𝓘(ℝ, E) f x v / r := by
  have heq : (fun y => f y / r) = (fun y => r⁻¹ * f y) := by
    ext y
    simp only [div_eq_mul_inv, mul_comm]
  rw [heq, mvfderiv_fun_mul mdifferentiableAt_const hf]
  have hconst : mvfderiv 𝓘(ℝ, E) (fun _ : M => r⁻¹) x = 0 := by simp [mvfderiv, mfderiv_const]
  simp [hconst, div_eq_mul_inv, mul_comm]

theorem FlowTimeChange.criticalPoints_height_div_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {r : ℝ} (hr : r ≠ 0) :
    ManifoldMorse.criticalPoints E (fun y => f y / r) =
      ManifoldMorse.criticalPoints E f := by
  ext x
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y / r) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
  rw [mfderiv_height_div_const (hf.mdifferentiableAt (by simp))]
  exact smul_eq_zero.trans (or_iff_right (inv_ne_zero hr))

theorem FlowTimeChange.descending_height_div_const_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) {r : ℝ} (hr : 0 < r)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => f y / r) x v < 0 ↔ mvfderiv 𝓘(ℝ, E) f x v < 0 := by
  rw [mvfderiv_height_div_const hf r]
  rw [div_lt_iff₀ hr, MulZeroClass.zero_mul]

theorem FlowTimeChange.exists_normalized_whole_level_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ (r : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M) (A :
      PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ y : M // f y = c } × ℝ) M ∞),
      0 < r ∧
        r < c - a ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
              (∀ y, W y = 0 ↔ V y = 0) ∧
                (∀ y,
                    y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
                  (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 y, W x = V x) ∧
                    (∀ y,
                        Set.range (fun t => G t y) = Set.range (fun t => F t y) ∧
                          (∀ p,
                              Filter.Tendsto (fun t => G t y) Filter.atTop (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                            ∀ p,
                              Filter.Tendsto (fun t => G t y) Filter.atBot (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                      A.source = Set.univ ∧
                        A.target = FlowCancellation.levelBasin G f c ∧
                          (∀ p, A p = G p.2 p.1) ∧
                            (∀ p, p.2 ∈ Set.Icc (0 : ℝ) 1 → f (A p) = c - r * p.2) ∧
                              ∀ y ∈ A.target,
                                W y =
                                  VectorField.mpullback 𝓘(ℝ, E)
                                    (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) A.symm
                                    FlowSuspension.nativeVerticalField y := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let r : ℝ := (c - a) / 2
  have hr : 0 < r := div_pos (sub_pos.mpr ha) (by norm_num)
  have hrbound : r < c - a := by dsimp [r]; linarith
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
  obtain ⟨U, W, G, hU, hIU, hW, hG, hzero, hneg, hspeed, hgerm, -, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hg hV hdescent F hF hregular
  have hnegf (y : M) (hy : y ∉ ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f y (W y) < 0 :=
    (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (W y)).mp
      (hneg y (hcrit ▸ hy))
  obtain ⟨A, hsource, htarget, hformula, hfield⟩ :=
    FlowSuspension.exists_native_level_flow_cylinder_with_field hf hreg hW G hG
      (fun y hy => hnegf y (hreg y hy)) z
  have hc : c / r ∈ Set.Icc (a / r) (b / r) :=
    ⟨div_le_div_of_nonneg_right ha.le hr.le, div_le_div_of_nonneg_right hb.le hr.le⟩
  refine
    ⟨r, W, G, A, hr, hrbound, hW, hG, hzero, hnegf, (fun y hy => hgerm y (hcrit ▸ hy)), hgeometry,
      hsource, htarget, hformula, ?_, hfield⟩
  intro p ht
  have hi : g p.1 = c / r := by change f p.1 / r = c / r; rw [p.1.property]
  have he : c / r - p.2 = (c - r * p.2) / r := by field_simp
  have hend : g p.1 - p.2 ∈ Set.Icc (a / r) (b / r) := by
    rw [hi, he]
    constructor
    · apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [ht.2]
    · apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [mul_nonneg hr.le ht.1]
  have hh := native_local_height_translation hg G hG hU hIU hspeed p.1 p.2 (hi ▸ hc) hend
  rw [hi, he] at hh
  rw [hformula]
  exact (div_left_inj' hr.ne').mp hh

theorem FlowSuspension.nativeSuspensionField_height {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : N × ℝ) : (nativeSuspensionField Ψ p).2 = 1 := by
  let q := Ψ.symm p
  have hproj : (Prod.snd : N × ℝ → ℝ) ∘ Ψ = Prod.snd := funext hheight
  have hc :=
    mfderiv_comp q
      (show MDifferentiableAt (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : N × ℝ → ℝ) (Ψ q) from
        mdifferentiableAt_snd)
      (Ψ.contMDiff.mdifferentiableAt (by simp))
  rw [hproj, mfderiv_snd, mfderiv_snd] at hc
  have hv := congrArg (fun L : (Z × ℝ) →L[ℝ] ℝ => L (0, 1)) hc
  change (1 : ℝ) = (nativeSuspensionField Ψ p).2 at hv
  exact hv.symm

theorem FlowSuspension.nativeSuspensionField_ne_zero {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : N × ℝ) : nativeSuspensionField Ψ p ≠ 0 := by
  intro hz
  have hh := congrArg (fun v : Z × ℝ => v.2) hz
  rw [nativeSuspensionField_height Ψ hheight p] at hh
  exact one_ne_zero hh

theorem FlowSuspension.nativeSuspensionField_eq_vertical_of_flow_germ {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) (p : N × ℝ)
    (heq : (fun t : ℝ => nativeSuspensionFlow Ψ t p) =ᶠ[𝓝 0] (fun t : ℝ => (p.1, p.2 + t))) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hw := nativeSuspensionFlow_integralCurve Ψ p 0
  have hv := nativeVerticalField_integralCurve (Z := Z) p 0
  have hh := hw.mfderiv.symm.trans (heq.mfderiv_eq.trans hv.mfderiv)
  have hval := congrArg (fun L : ℝ →L[ℝ] (Z × ℝ) => L 1) hh
  change
    (1 : ℝ) • nativeSuspensionField Ψ (nativeSuspensionFlow Ψ 0 p) =
      (1 : ℝ) • nativeVerticalField (p.1, p.2 + 0) at hval
  have h0 : nativeSuspensionFlow Ψ (0 : ℝ) p = p := by
    change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + 0) = p
    rw [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  rw [one_smul, one_smul, h0] at hval
  convert! hval using 1

theorem FlowSuspension.nativeSuspensionField_eq_vertical_off_base {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) {K : Set N}
    (hfix : ∀ p, p.1 ∉ K → Ψ p = p) (p : N × ℝ) (hp : p.1 ∉ K) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hi : Ψ.symm p = p := by
    have hh := congrArg Ψ.symm (hfix p hp)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  apply Filter.Eventually.of_forall
  intro t
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = (p.1, p.2 + t)
  rw [hi]
  exact hfix (p.1, p.2 + t) hp

theorem FlowSuspension.nativeSuspensionField_eq_vertical_below {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) {a : ℝ}
    (hleft : ∀ p, p.2 ≤ a → Ψ p = p) (p : N × ℝ) (hp : p.2 < a) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hi : Ψ.symm p = p := by
    have hh := congrArg Ψ.symm (hleft p hp.le)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  filter_upwards [eventually_lt_nhds (sub_pos.mpr hp)] with t ht
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = (p.1, p.2 + t)
  rw [hi]
  exact hleft (p.1, p.2 + t) (by dsimp; linarith)

theorem FlowSuspension.nativeSuspensionField_eq_vertical_above {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) (D : N → N)
    {b : ℝ} (hheight : ∀ p, (Ψ p).2 = p.2) (hright : ∀ p, b ≤ p.2 → Ψ p = (D p.1, p.2))
    (p : N × ℝ) (hp : b < p.2) : nativeSuspensionField Ψ p = nativeVerticalField p := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have htime : q.2 = p.2 := (hheight q).symm.trans (congrArg Prod.snd hq)
  have hbase : D q.1 = p.1 := by
    have hh := hright q (by rw [htime]; exact hp.le)
    rw [hq] at hh
    exact (congrArg Prod.fst hh).symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  filter_upwards [eventually_gt_nhds (show b - p.2 < (0 : ℝ) by linarith)] with t ht
  change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
  rw [hright (q.1, q.2 + t) (by dsimp; rw [htime]; linarith), hbase, htime]

theorem FlowSuspension.nativeSuspensionFlow_fixed_line {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N]
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞) {x : N}
    (hfix : ∀ s : ℝ, Ψ (x, s) = (x, s)) (s t : ℝ) :
    nativeSuspensionFlow Ψ t (x, s) = (x, s + t) := by
  have hi : Ψ.symm (x, s) = (x, s) := by
    have hh := congrArg Ψ.symm (hfix s)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  change Ψ ((Ψ.symm (x, s)).1, (Ψ.symm (x, s)).2 + t) = _
  rw [hi]
  exact hfix (s + t)

theorem FlowSuspension.exists_compact_native_level_suspension {Z N : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N] [T2Space N]
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N} (hK : IsCompact K)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞,
      IsCompact (K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) ∧
        (∀ p, (Ψ p).2 = p.2) ∧
          (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
            (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
              ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
                  (fun p : N × ℝ =>
                    (⟨p, nativeSuspensionField Ψ p⟩ :
                      TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) ∧
                (∀ p,
                    IsMIntegralCurve (fun t : ℝ => nativeSuspensionFlow Ψ t p)
                      (nativeSuspensionField Ψ)) ∧
                  (∀ p, (nativeSuspensionField Ψ p).2 = 1) ∧
                    (∀ p, nativeSuspensionField Ψ p ≠ 0) ∧
                      (∀ p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3),
                          nativeSuspensionField Ψ p = nativeVerticalField p) ∧
                        (∀ p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3),
                            ∀ᶠ q in 𝓝 p, nativeSuspensionField Ψ q = nativeVerticalField q) ∧
                          (∀ x, nativeSuspensionFlow Ψ 1 (x, 0) = (D x, 1)) ∧
                            (∀ t p, (nativeSuspensionFlow Ψ t p).2 = p.2 + t) ∧
                              (∀ x ∉ K, ∀ s t : ℝ, nativeSuspensionFlow Ψ t (x, s) = (x, s + t)) ∧
                                ∀ x ∈ S,
                                  ∀ s t : ℝ, nativeSuspensionFlow Ψ t (x, s) = (x, s + t) := by
  obtain ⟨Ψ, hheight, hleft, hright, hout, hfixed⟩ := exists_native_base_suspension D I
  have hC : IsCompact (K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) := hK.prod CompactIccSpace.isCompact_Icc
  have hfield (p : N × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Set.Icc (1 / 3 : ℝ) (2 / 3) := fun ht => hp ⟨hx, ht⟩
      by_cases hlo : p.2 < 1 / 3
      · exact nativeSuspensionField_eq_vertical_below Ψ hleft p hlo
      · have hhi : 2 / 3 < p.2 := lt_of_not_ge (fun hh => ht ⟨le_of_not_gt hlo, hh⟩)
        exact nativeSuspensionField_eq_vertical_above Ψ D hheight hright p hhi
    · exact nativeSuspensionField_eq_vertical_off_base Ψ hout p hx
  have hgerm (p : N × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    ∀ᶠ q in 𝓝 p, nativeSuspensionField Ψ q = nativeVerticalField q := by
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hfield q hq
  refine
    ⟨Ψ, hC, hheight, hleft, hright, contMDiff_nativeSuspensionField Ψ,
      nativeSuspensionFlow_integralCurve Ψ, nativeSuspensionField_height Ψ hheight,
      nativeSuspensionField_ne_zero Ψ hheight, hfield, hgerm, ?_,
      nativeSuspensionFlow_height Ψ hheight, ?_, ?_⟩
  · intro x
    have hzero : Ψ (x, (0 : ℝ)) = (x, 0) := hleft (x, 0) (by norm_num)
    rw [← hzero, nativeSuspensionFlow_chart, zero_add]
    exact hright (x, 1) (by norm_num)
  · intro x hx s t
    exact nativeSuspensionFlow_fixed_line Ψ (fun u => hout (x, u) hx) s t
  · intro x hx s t
    exact nativeSuspensionFlow_fixed_line Ψ (fun u => hfixed (x, u) hx) s t

theorem FlowSuspension.mvfderiv_native_model_pullback {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (W : (z : X) → TangentSpace I z) {x : M}
    (hx : x ∈ A.target) :
    mvfderiv 𝓘(ℝ, E) f x (VectorField.mpullback 𝓘(ℝ, E) I A.symm W x) =
      mvfderiv I (f ∘ A) (A.symm x) (W (A.symm x)) := by
  rw [native_model_pullback_eq_mfderiv_symm A.symm W hx]
  exact
    (mvfderiv_comp_apply_of_eq (A.symm x) (hf.mdifferentiableAt (by simp))
        ((A.contMDiffOn_toFun.contMDiffAt
              (A.open_source.mem_nhds (A.map_target' hx))).mdifferentiableAt
          (by simp))
        (A.right_inv' hx) (W (A.symm x))).symm

theorem FlowSuspension.mvfderiv_native_level_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {Z N : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {b s : ℝ}
    (hheight : ∀ p ∈ A.source, f (A p) = b - s * p.2)
    (W : (p : N × ℝ) → TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p) {x : M} (hx : x ∈ A.target) :
    mvfderiv 𝓘(ℝ, E) f x (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm W x) =
      -s * (W (A.symm x)).2 := by
  let q := A.symm x
  have heq : (f ∘ A) =ᶠ[𝓝 q] (fun p : N × ℝ => b - s * p.2) := by
    filter_upwards [A.open_source.mem_nhds (A.map_target' hx)] with p hp
    exact hheight p hp
  have hd :
    mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ A) q =
      mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : N × ℝ => b - s * p.2) q :=
    heq.mfderiv_eq
  rw [mvfderiv_native_model_pullback A hf W hx]
  change mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ A) q (W q) = _
  rw [hd]
  have hsnd :
    HasMFDerivAt (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : N × ℝ → ℝ) q
      (ContinuousLinearMap.snd ℝ Z ℝ) :=
    hasMFDerivAt_snd q
  have hh :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) b q).sub
      ((hasMFDerivAt_const (I := 𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) s q).mul hsnd)
  have hh' :
    mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : N × ℝ => b - s * p.2) q =
      (0 : (Z × ℝ) →L[ℝ] ℝ) - (s • ContinuousLinearMap.snd ℝ Z ℝ + q.2 • (0 : (Z × ℝ) →L[ℝ] ℝ)) :=
    hh.mfderiv
  rw [hh']
  change (0 : ℝ) - (s * (W q).2 + q.2 * (0 : ℝ)) = -s * (W q).2
  ring

theorem FlowSuspension.exists_native_whole_level_holonomy {Z E N M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace Z N]
    [IsManifold 𝓘(ℝ, Z) ∞ N] [T2Space N] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {b s : ℝ}
    (hs : 0 < s) (hheight : ∀ p, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A p) = b - s * p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ A.target,
        V x = VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N} (hK : IsCompact K)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (C : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (Ψ :
      Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞),
      IsCompact C ∧
        C ⊆ A.target ∩ f ⁻¹' Set.Ioo (b - s) b ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
              (∀ x, V' x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (V' x) < 0) ∧
                  (∀ x ∉ C, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                    (∀ x ∈ A.target, ∀ t, G t x ∈ A.target) ∧
                      (∀ x ∉ A.target, ∀ t, G t x = H t x) ∧
                        (∀ p t, G t (A p) = A (nativeSuspensionFlow Ψ t p)) ∧
                          (∀ x, G 1 (A (x, 0)) = A (D x, 1)) ∧
                            (∀ x ∈ S, ∀ u t : ℝ, G t (A (x, u)) = A (x, u + t)) ∧
                              (∀ p, (Ψ p).2 = p.2) ∧
                                (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
                                  (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
                                    ∀ x ∈ A.target,
                                      V' x =
                                        VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
                                          A.symm (nativeSuspensionField Ψ) x := by
  obtain
    ⟨Ψ, hL, hΨheight, hleft, hright, hW, hF, hWheight, hWzero, hfix, -, hend, -, -, hfixed⟩ :=
    exists_compact_native_level_suspension D hK I
  let L : Set (N × ℝ) := K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)
  have hLA : L ⊆ A.source := by rw [hsource]; exact Set.subset_univ L
  have hvertical (p : N × ℝ) (_ : p ∈ A.source) : nativeVerticalField (Z := Z) p ≠ 0 := by
    intro hz
    have hh := congrArg (fun v : Z × ℝ => v.2) hz
    exact one_ne_zero hh
  obtain ⟨V', hV', hnew, hzero, hgerm⟩ :=
    exists_native_model_field_replacement A V hV nativeVerticalField (nativeSuspensionField Ψ) hW
      hmodel hvertical (fun p _ => hWzero p) hL hLA hfix
  let C := A '' L
  have hC : IsCompact C := hL.image_of_continuousOn (A.contMDiffOn_toFun.continuousOn.mono hLA)
  have hslab (p : N × ℝ) (hp : p ∈ L) : p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hCsub : C ⊆ A.target ∩ f ⁻¹' Set.Ioo (b - s) b := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨A.map_source' (hLA hp), ?_⟩
    change f (A p) ∈ Set.Ioo (b - s) b
    rw [hheight p (hslab p hp)]
    constructor <;> nlinarith [(hslab p hp).1, (hslab p hp).2]
  let R :=
    PartialChart.restrictSource A
      (isOpen_univ.prod (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)))
  have hRheight (p : N × ℝ) (hp : p ∈ R.source) : f (R p) = b - s * p.2 := hheight p hp.2.2
  have hnegC (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V' x) = -s := by
    rcases hx with ⟨p, hp, rfl⟩
    have hpR : p ∈ R.source := ⟨hLA hp, Set.mem_univ _, hslab p hp⟩
    rw [hnew (A p) (A.map_source' (hLA hp))]
    change
      mvfderiv 𝓘(ℝ, E) f (R p)
          (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) R.symm (nativeSuspensionField Ψ)
            (R p)) =
        -s
    rw [mvfderiv_native_level_height R hf hRheight _ (R.map_source' hpR), hWheight, mul_one]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : N × ℝ) (t : ℝ) : nativeSuspensionFlow Ψ t p ∈ A.source := by
    rw [hsource]
    exact Set.mem_univ _
  have hfull (p : N × ℝ) (t : ℝ) : G t (A p) = A (nativeSuspensionFlow Ψ t p) :=
    native_model_flow_all_time A hV'₁ G hG (nativeSuspensionFlow Ψ) (nativeSuspensionField Ψ) hF
      hnew (hstay p) t
  have hinv :=
    native_model_target_invariant A hV'₁ G hG (nativeSuspensionFlow Ψ) (nativeSuspensionField Ψ)
      hF hnew (fun p _ => hstay p)
  have hcomp := flow_complement_invariant G hinv
  refine
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, ?_, hgerm, hinv, ?_, hfull, ?_, ?_, hΨheight, hleft,
      hright, hnew⟩
  · intro x hx
    by_cases hc : x ∈ C
    · rw [hnegC x hc]
      exact neg_neg_of_pos hs
    · rw [(hgerm x hc).self_of_nhds]
      exact hx
  · intro x hx t
    have hagree (u : ℝ) : V' (G u x) = V (G u x) :=
      (hgerm (G u x) (fun h => hcomp x hx u (hCsub h).1)).self_of_nhds
    rcases le_total 0 t with ht | ht
    · exact
        FlowCancellation.native_flow_eq_on_positive_halfline (hV.of_le (by simp)) H G hH hG
          (fun u _ => hagree u) t ht
    · exact
        FlowCancellation.native_flow_eq_on_negative_halfline (hV.of_le (by simp)) H G hH hG
          (fun u _ => hagree u) t ht
  · intro x
    rw [hfull, hend]
  · intro x hx u t
    rw [hfull, hfixed x hx u t]

theorem FlowSuspension.native_whole_level_exterior_tails {Z N M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N] [TopologicalSpace M] (A : N × ℝ → M) (ι : N → M)
    (H G : Flow ℝ M) (hformula : ∀ p, A p = H p.2 (ι p.1)) (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞)
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞)
    (hleft : ∀ p, p.2 ≤ 1 / 3 → Ψ p = p) (hright : ∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2))
    (hfull : ∀ p t, G t (A p) = A (nativeSuspensionFlow Ψ t p)) :
    (∀ x, ∀ t : ℝ, t ≤ 0 → G t (A (x, 0)) = H t (A (x, 0))) ∧
      ∀ x, ∀ t : ℝ, 0 ≤ t → G t (A (x, 1)) = H t (A (x, 1)) := by
  constructor
  · intro x t ht
    have h0 : Ψ (x, (0 : ℝ)) = (x, 0) := hleft (x, 0) (by norm_num)
    have hf : nativeSuspensionFlow Ψ t (x, 0) = (x, t) := by
      rw [← h0, nativeSuspensionFlow_chart, zero_add]
      exact hleft (x, t) (by linarith)
    rw [hfull, hf, hformula, hformula, H.map_zero_apply]
  · intro x t ht
    have h1 : Ψ (D.symm x, (1 : ℝ)) = (x, 1) := by
      rw [hright (D.symm x, 1) (by norm_num), D.apply_symm_apply]
    have hf : nativeSuspensionFlow Ψ t (x, 1) = (x, 1 + t) := by
      rw [← h1, nativeSuspensionFlow_chart]
      rw [hright (D.symm x, 1 + t) (by linarith), D.apply_symm_apply]
    rw [hfull, hf, hformula, hformula, ← H.map_add]
    congr 1
    ring

theorem FlowSuspension.exists_native_regular_level_isotopy_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = c } { y : M // f y = c } ∞,
      SupportedDiffeomorph.IsotopicToIdentity D →
        ∃ (r : ℝ) (C : Set M) (W V' : (y : M) → TangentSpace 𝓘(ℝ, E) y) (H G : Flow ℝ M),
          0 < r ∧
            r < c - a ∧
              IsCompact C ∧
                C ⊆ f ⁻¹' Set.Ioo a b ∧
                  ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                      (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                    (∀ y, IsMIntegralCurve (fun t => H t y) W) ∧
                      (∀ y,
                          Set.range (fun t => H t y) = Set.range (fun t => F t y) ∧
                            (∀ p,
                                Filter.Tendsto (fun t => H t y) Filter.atTop (𝓝 p) ↔
                                  Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                              ∀ p,
                                Filter.Tendsto (fun t => H t y) Filter.atBot (𝓝 p) ↔
                                  Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                            (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                          (∀ y, IsMIntegralCurve (fun t => G t y) V') ∧
                            (∀ y, V' y = 0 ↔ V y = 0) ∧
                              (∀ y,
                                  y ∉ ManifoldMorse.criticalPoints E f →
                                    mvfderiv 𝓘(ℝ, E) f y (V' y) < 0) ∧
                                (∀ y ∈ ManifoldMorse.criticalPoints E f,
                                    ∀ᶠ x in 𝓝 y, V' x = V x) ∧
                                  (∀ y ∉ C, ∀ᶠ x in 𝓝 y, V' x = W x) ∧
                                    (∀ x : { y : M // f y = c }, G 1 x = H 1 (D x)) ∧
                                      (∀ x : { y : M // f y = c }, f (H 1 x) = c - r) ∧
                                        (∀ x : { y : M // f y = c },
                                            ∀ t : ℝ, t ≤ 0 → G t x = H t x) ∧
                                          ∀ x : { y : M // f y = c },
                                            ∀ t : ℝ, 0 ≤ t → G t (H 1 x) = H t (H 1 x) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let L := { y : M // f y = c }
  let _ : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro D hD
  obtain ⟨B, hB, hBzero, hBone, hBslices⟩ := hD
  let I : SupportedDiffeomorph.SupportedRelativeIsotopy D Set.univ ∅ :=
    { family := B
      smooth := hB
      zero := hBzero
      one := hBone
      slices := fun t => by
        obtain ⟨d, hd⟩ := hBslices t
        exact ⟨d, fun x => (hd x).symm⟩
      fixedOutside := fun _ x hx => (hx (Set.mem_univ x)).elim
      fixedOn := fun _ _ hx => hx.elim }
  obtain
    ⟨r, W, H, A, hr, hrbound, hW, hH, hWzero, hWneg, hWgerm, hgeometry, hsource, -, hformula,
      hheight, hmodel⟩ :=
    FlowTimeChange.exists_normalized_whole_level_cylinder hf hV hdesc F hF ha hb hband hreg
      z
  obtain
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, hneg, hgerm, -, -, hfull, hend, -, -, hleft, hright,
      -⟩ :=
    exists_native_whole_level_holonomy A hsource hf hr (fun p hp => hheight p ⟨hp.1.le, hp.2.le⟩)
      W hW hmodel H hH D isCompact_univ I
  have hCband : C ⊆ f ⁻¹' Set.Ioo a b := by
    intro y hy
    have hh := (hCsub hy).2
    change f y ∈ Set.Ioo (c - r) c at hh
    exact ⟨by linarith [hh.1], lt_trans hh.2 hb⟩
  have hcritical (y : M) (hy : y ∈ ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 y, V' x = V x := by
    have hout : y ∉ C := fun hc => hband y ⟨(hCband hc).1.le, (hCband hc).2.le⟩ hy
    filter_upwards [hgerm y hout, hWgerm y hy] with x hx hx'
    exact hx.trans hx'
  obtain ⟨htailLeft, htailRight⟩ :=
    native_whole_level_exterior_tails A Subtype.val H G hformula D Ψ hleft hright hfull
  have hA0 (x : L) : A (x, 0) = (x : M) := by rw [hformula, H.map_zero_apply]
  have hA1 (x : L) : A (x, 1) = H 1 x := hformula (x, 1)
  refine
    ⟨r, C, W, V', H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV', hG, fun y =>
      (hzero y).trans (hWzero y), fun y hy => hneg y (hWneg y hy), hcritical, hgerm, ?_, ?_, ?_,
      ?_⟩
  · intro x
    rw [← hA0 x, hend, hA1]
  · intro x
    have hh := hheight (x, 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [hA1, mul_one] at hh
    exact hh
  · intro x t ht
    simpa only [hA0] using htailLeft x t ht
  · intro x t ht
    simpa only [hA1] using htailRight x t ht

theorem FlowSuspension.whole_level_basins_of_holonomy {X M : Type*} [TopologicalSpace M]
    (F H G : Flow ℝ M) (ι : X → M) (D : X → X)
    (hHtop :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hHbot :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hend : ∀ x, G 1 (ι x) = H 1 (ι (D x))) (hleft : ∀ x, ∀ t : ℝ, t ≤ 0 → G t (ι x) = H t (ι x))
    (hright : ∀ x, ∀ t : ℝ, 0 ≤ t → G t (H 1 (ι x)) = H t (H 1 (ι x))) :
    (∀ x p,
        Filter.Tendsto (fun t => G t (ι x)) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t (ι x)) Filter.atBot (𝓝 p)) ∧
      ∀ x p,
        Filter.Tendsto (fun t => G t (ι x)) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => F t (ι (D x))) Filter.atTop (𝓝 p) := by
  constructor
  · intro x p
    have heq : (fun t => G t (ι x)) =ᶠ[Filter.atBot] (fun t => H t (ι x)) := by
      filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
      exact hleft x t ht
    exact (Filter.tendsto_congr' heq).trans (hHbot (ι x) p)
  · intro x p
    have heq : (fun t => G t (H 1 (ι (D x)))) =ᶠ[Filter.atTop] (fun t => H t (H 1 (ι (D x)))) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact hright (D x) t ht
    calc
      Filter.Tendsto (fun t => G t (ι x)) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => G t (G 1 (ι x))) Filter.atTop (𝓝 p) :=
        (MorseCancellation.flow_time_atTop_limit_iff G 1 (ι x) p).symm
      _ ↔ Filter.Tendsto (fun t => G t (H 1 (ι (D x)))) Filter.atTop (𝓝 p) := by rw [hend]
      _ ↔ Filter.Tendsto (fun t => H t (H 1 (ι (D x)))) Filter.atTop (𝓝 p) :=
        (Filter.tendsto_congr' heq)
      _ ↔ Filter.Tendsto (fun t => H t (ι (D x))) Filter.atTop (𝓝 p) :=
        (MorseCancellation.flow_time_atTop_limit_iff H 1 (ι (D x)) p)
      _ ↔ Filter.Tendsto (fun t => F t (ι (D x))) Filter.atTop (𝓝 p) := hHtop (ι (D x)) p

theorem FlowSuspension.unique_connection_of_level_basin_intersection {M : Type*}
    [TopologicalSpace M] (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c) (D : { x : M // f x = c } → { x : M // f x = c })
    (hback :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hforward :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) ↔
          Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q))
    (z : { y : M // f y = c }) (hzback : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 p))
    (hzforward : Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 q))
    (hunique :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) →
          Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q) → x = z) :
    Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 p) ∧
      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 q) ∧
        ∀ x,
          Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) →
            Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) → ∃ t, G t z = x := by
  refine ⟨(hback z).mpr hzback, (hforward z).mpr hzforward, ?_⟩
  intro x hxback hxforward
  obtain ⟨s, hs⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits G hf hxback hxforward hpc hqc
  let u : { y : M // f y = c } := ⟨G s x, hs⟩
  have hub : Filter.Tendsto (fun t => G t u) Filter.atBot (𝓝 p) :=
    (MorseCancellation.flow_time_atBot_limit_iff G s x p).mpr hxback
  have huf : Filter.Tendsto (fun t => G t u) Filter.atTop (𝓝 q) :=
    (MorseCancellation.flow_time_atTop_limit_iff G s x q).mpr hxforward
  have huz : u = z := hunique u ((hback u).mp hub) ((hforward u).mp huf)
  have hv : G s x = (z : M) := congrArg Subtype.val huz
  refine ⟨-s, ?_⟩
  rw [← hv, ← G.map_add, neg_add_cancel, G.map_zero_apply]

def TransverseGerms.timeLiftLinear {A Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : A →L[ℝ] Z) (α : A →L[ℝ] ℝ) :
    (A × ℝ) →L[ℝ] (Z × ℝ) :=
  (L.comp (ContinuousLinearMap.fst ℝ A ℝ)).prod
    (ContinuousLinearMap.snd ℝ A ℝ + α.comp (ContinuousLinearMap.fst ℝ A ℝ))

theorem TransverseGerms.surjective_time_lift_coprod {A B Z : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (L : A →L[ℝ] Z) (R : B →L[ℝ] Z) (α : A →L[ℝ] ℝ) (β : B →L[ℝ] ℝ)
    (h : Function.Surjective (L.coprod R)) :
    Function.Surjective ((timeLiftLinear L α).coprod (timeLiftLinear R β)) := by
  rintro ⟨z, t⟩
  obtain ⟨⟨a, b⟩, hab⟩ := h z
  refine ⟨((a, t - α a - β b), (b, 0)), ?_⟩
  apply Prod.ext
  · exact hab
  · change (t - α a - β b + α a) + (0 + β b) = t
    ring

theorem TransverseGerms.native_time_lift_derivative {A Z : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {HA HZ X N : Type*}
    [TopologicalSpace HA] [TopologicalSpace HZ] {I : ModelWithCorners ℝ A HA}
    {J : ModelWithCorners ℝ Z HZ} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace N]
    [ChartedSpace HZ N] {f : X → N} {v : X → ℝ} {x : X} (s : ℝ) (hf : MDifferentiableAt I J f x)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) :
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (fun p : X × ℝ => (f p.1, p.2 + v p.1)) (x, s) :
        (A × ℝ) →L[ℝ] (Z × ℝ)) =
      timeLiftLinear (A := A) (Z := Z) (mfderiv I J f x) (mvfderiv I v x) := by
  have hn := hf.hasMFDerivAt.comp (x, s) (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s))
  have hp := hv.hasMFDerivAt.comp (x, s) (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s))
  have ht := (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s)).add hp
  exact (hn.prodMk ht).mfderiv

theorem TransverseGerms.native_transversality_time_lifts {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {HA HB HZ X Y N : Type*} [TopologicalSpace HA]
    [TopologicalSpace HB] [TopologicalSpace HZ] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} {J : ModelWithCorners ℝ Z HZ} [TopologicalSpace X]
    [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y] [TopologicalSpace N]
    [ChartedSpace HZ N] {f : X → N} {g : Y → N} {v : X → ℝ} {w : Y → ℝ} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y) (s t : ℝ) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ))
      (fun p : X × ℝ => (f p.1, p.2 + v p.1)) (fun p : Y × ℝ => (g p.1, p.2 + w p.1)) (x, s)
      (y, t) := by
  intro _
  rw [native_time_lift_derivative s hf hv, native_time_lift_derivative t hg hw]
  exact surjective_time_lift_coprod _ _ _ _ (htrans hxy)

theorem TransverseGerms.native_transverse_sheets_of_level_maps
    {A B Z E HA HB HZ HE X Y N M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HA] [TopologicalSpace HB]
    [TopologicalSpace HZ] [TopologicalSpace HE] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} {J : ModelWithCorners ℝ Z HZ} {J' : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    [TopologicalSpace N] [ChartedSpace HZ N] [TopologicalSpace M] [ChartedSpace HE M]
    (C : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) J' (N × ℝ) M ∞) {f : X → N} {g : Y → N} {v : X → ℝ}
    {w : Y → ℝ} {x : X} {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y) {s t : ℝ}
    (hphase : t + w y = s + v x) (hsource : (f x, s + v x) ∈ C.source) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) J'
      (fun p : X × ℝ => C (f p.1, p.2 + v p.1)) (fun p : Y × ℝ => C (g p.1, p.2 + w p.1)) (x, s)
      (y, t) := by
  let F : X × ℝ → N × ℝ := fun p => (f p.1, p.2 + v p.1)
  let G : Y × ℝ → N × ℝ := fun p => (g p.1, p.2 + w p.1)
  have hF : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) F (x, s) :=
    (hf.comp (x, s) mdifferentiableAt_fst).prodMk
      (mdifferentiableAt_snd.add (hv.comp (x, s) mdifferentiableAt_fst))
  have hG : MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) G (y, t) :=
    (hg.comp (y, t) mdifferentiableAt_fst).prodMk
      (mdifferentiableAt_snd.add (hw.comp (y, t) mdifferentiableAt_fst))
  have hcross : G (y, t) = F (x, s) := Prod.ext hxy hphase
  exact
    (native_transversality_partial_diffeomorph_iff C hF hG hcross hsource).mp
      (native_transversality_time_lifts hf hg hv hw hxy htrans s t)

theorem FlowSuspension.native_transverse_basin_tubes_of_level_maps {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f)
    {V : (z : M) → TangentSpace 𝓘(ℝ, E) z}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hboundary : ∀ z, f z = c → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) {p q : M} :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ (α : X → { z : M // f z = c }) (β : Y → { z : M // f z = c }) (x : X) (y : Y),
      MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
        MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
          β y = α x →
            NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
              (∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (α u)) Filter.atBot (𝓝 q)) →
                (∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (β u)) Filter.atTop (𝓝 p)) →
                  let S : X × ℝ → M := fun w => F w.2 (α w.1)
                  let T : Y × ℝ → M := fun w => F w.2 (β w.1)
                  MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) S (x, 0) ∧
                    MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) T (y, 0) ∧
                      S (x, 0) = (α x : M) ∧
                        T (y, 0) = (α x : M) ∧
                          (∀ᶠ u in 𝓝 (x, (0 : ℝ)),
                              Filter.Tendsto (fun t => F t (S u)) Filter.atBot (𝓝 q)) ∧
                            (∀ᶠ u in 𝓝 (y, (0 : ℝ)),
                                Filter.Tendsto (fun t => F t (T u)) Filter.atTop (𝓝 p)) ∧
                              NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
                                𝓘(ℝ, E) S T (x, 0) (y, 0) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨C, hsource, -, hformula, -⟩ :=
    exists_native_level_flow_cylinder_with_field hf hreg hV F hF hboundary (α x)
  have hxC : (α x, (0 : ℝ)) ∈ C.source := by rw [hsource]; exact Set.mem_univ _
  have hyC : (β y, (0 : ℝ)) ∈ C.source := by rw [hsource]; exact Set.mem_univ _
  have hS : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (fun w : X × ℝ => C (α w.1, w.2)) (x, 0) :=
    (C.mdifferentiableAt (by simp) hxC).comp (x, 0)
      ((hα.comp (x, 0) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have hT :
    MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (fun w : Y × ℝ => C (β w.1, w.2)) (y, 0) :=
    (C.mdifferentiableAt (by simp) hyC).comp (y, 0)
      ((hβ.comp (y, 0) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have ht :=
    TransverseGerms.native_transverse_sheets_of_level_maps C hα hβ (v := fun _ : X =>
      (0 : ℝ)) (w := fun _ : Y => (0 : ℝ)) mdifferentiableAt_const mdifferentiableAt_const hcross
      htrans (s := 0) (t := 0) rfl (by simpa only [add_zero] using hxC)
  refine ⟨?_, ?_, F.map_zero_apply _, ?_, ?_, ?_, ?_⟩
  · simpa only [hformula] using hS
  · simpa only [hformula] using hT
  · change F 0 (β y) = (α x : M)
    rw [F.map_zero_apply, hcross]
  · filter_upwards [continuous_fst.continuousAt hαbasin] with u hu
    exact (MorseCancellation.flow_time_atBot_limit_iff F u.2 (α u.1) q).mpr hu
  · filter_upwards [continuous_fst.continuousAt hβbasin] with u hu
    exact (MorseCancellation.flow_time_atTop_limit_iff F u.2 (β u.1) p).mpr hu
  · simpa only [add_zero, hformula] using ht

theorem FlowSuspension.native_vertical_cylinder_flow {Z E M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (z : Z) (hz : z ∈ U)
    (s t : ℝ) : F t (Φ (z, s)) = Φ (z, s + t) := by
  let γ : ℝ → M := fun t => Φ (z, s + t)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hstay : (z, s + t) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    have hcoord : HasDerivAt (fun r : ℝ => (z, s + r)) (0, 1) t :=
      (hasDerivAt_const t z).prodMk ((hasDerivAt_id t).const_add s)
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm (fun _ : Z × ℝ => (0, 1))
        hcoord hstay
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) (γ t))) at hd
    rw [← hmodel (γ t) (Φ.map_source' hstay)] at hd
    exact hd
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hF (Φ (z, s))) hγ (t₀ := 0)
      (by simp only [γ, F.map_zero_apply, add_zero])
  exact congrFun heq t

theorem FlowSuspension.native_corrected_cylinder_tails {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hΦsource : Φ.source = U ×ˢ Set.univ) (hΩsource : Ω.source = U ×ˢ Set.univ)
    {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΦmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (hΩmodel :
      ∀ x ∈ Ω.target,
        W x = FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) (D : Z → Z) (hDU : Set.MapsTo D U U)
    (hleft : ∀ p, p.2 ≤ 0 → Ω p = Φ p) (hright : ∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) :
    (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0))) ∧
      (∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1))) := by
  constructor
  · intro z hz t ht
    rw [← hleft (z, 0) le_rfl, native_vertical_cylinder_flow Ω hΩsource hW hΩmodel G hG z hz 0 t,
      zero_add, hleft (z, t) ht, hleft (z, 0) le_rfl,
      native_vertical_cylinder_flow Φ hΦsource hV hΦmodel F hF z hz 0 t, zero_add]
  · intro z hz t ht
    rw [native_vertical_cylinder_flow Ω hΩsource hW hΩmodel G hG z hz 1 t,
      hright (z, 1 + t) (by dsimp; linarith), hright (z, 1) le_rfl,
      native_vertical_cylinder_flow Φ hΦsource hV hΦmodel F hF (D z) (hDU hz) 1 t]

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

theorem FlowSuspension.phaseCylinderChart_target {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (v : E → ℝ) (hv : ContDiff ℝ ∞ v) :
    (phaseCylinderChart Q v hv).target = Q.target ×ˢ Set.univ :=
  rfl

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

theorem MorseCancellation.cubicFlowCylinder_pushforward_vertical {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    (p : (Fin m → ℝ) × ℝ) :
    fderiv ℝ (cubicFlowCylinder σ a) p (0, 1) =
      cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a p) := by
  have hd :=
    ((contDiff_cubicFlowCylinder σ a).differentiable (by simp) p).hasFDerivAt |>.comp_hasDerivAt
      p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hd' := hasDerivAt_cubicFlowCylinder σ a p.1 p.2
  exact hd.unique hd'

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

def TransverseGerms.compose_supported_isotopies {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D₁ D₂ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {K₁ K₂ S : Set E}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy D₁ K₁ S)
    (B : SupportedDiffeomorph.SupportedRelativeIsotopy D₂ K₂ S) :
    SupportedDiffeomorph.SupportedRelativeIsotopy (D₁.trans D₂) (K₁ ∪ K₂) S
    where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = D₂ (D₁ x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)), B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

attribute [local instance 100] Classical.propDecidable in
theorem TransverseGerms.exists_transported_transition_correction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hQ0 : (0 : E) ∈ Q.source)
    (hP0 : (0 : E) ∈ P.source) (hQzero : Q 0 = 0) (hPzero : P 0 = 0) (hHs : H.source ⊆ Q.source)
    (hHt : H.target ⊆ P.source) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {Kₛ Kₜ Sₛ Sₜ : Set E} (hKₛ : IsCompact Kₛ)
    (hKₜ : IsCompact Kₜ) (hKs : Kₛ ⊆ H.source) (hKt : Kₜ ⊆ H.target) (hSₛ : (0 : E) ∈ Sₛ)
    (hSₜ : (0 : E) ∈ Sₜ) (A : SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ Sₛ)
    (B : SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ Sₜ) :
    ∃ (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (K : Set Z),
      IsCompact K ∧
        K = Q '' Kₛ ∪ P '' Kₜ ∧
          K ⊆ Q.target ∩ P.target ∧
            Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy D K {(0 : Z)}) ∧
              D 0 = 0 ∧ ∀ z ∈ H.source, D (Q z) = P (Dₜ (H (Dₛ z))) := by
  have hKQ : Kₛ ⊆ Q.source := hKs.trans hHs
  have hKP : Kₜ ⊆ P.source := hKt.trans hHt
  have hfixedQ (z : E) (hz : z ∈ Q.source) (h : Q z ∈ ({(0 : Z)} : Set Z)) : z ∈ Sₛ := by
    have he : z = 0 :=
      Q.toOpenPartialHomeomorph.injOn hz hQ0 ((Set.mem_singleton_iff.mp h).trans hQzero.symm)
    exact he.symm ▸ hSₛ
  have hfixedP (z : E) (hz : z ∈ P.source) (h : P z ∈ ({(0 : Z)} : Set Z)) : z ∈ Sₜ := by
    have he : z = 0 :=
      P.toOpenPartialHomeomorph.injOn hz hP0 ((Set.mem_singleton_iff.mp h).trans hPzero.symm)
    exact he.symm ▸ hSₜ
  let A' := A.extension Q hKₛ hKQ hfixedQ
  let B' := B.extension P hKₜ hKP hfixedP
  let DQ := SupportedDiffeomorph.extension Q Dₛ hKₛ hKQ A.endpoint_fixed_outside
  let DP := SupportedDiffeomorph.extension P Dₜ hKₜ hKP B.endpoint_fixed_outside
  let D := DQ.trans DP
  let K := Q '' Kₛ ∪ P '' Kₜ
  have hK : IsCompact K :=
    (hKₛ.image_of_continuousOn (Q.contMDiffOn_toFun.continuousOn.mono hKQ)).union
      (hKₜ.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hKP))
  have I : SupportedDiffeomorph.SupportedRelativeIsotopy D K {(0 : Z)} :=
    compose_supported_isotopies A' B'
  have hKU : K ⊆ Q.target ∩ P.target := by
    rintro y (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨Q.map_source' (hKQ hz), ?_⟩
      rw [← hdiagram z (hKs hz)]
      exact P.map_source' (hHt (H.map_source' (hKs hz)))
    · refine ⟨?_, P.map_source' (hKP hz)⟩
      have hh := hdiagram (H.symm z) (H.map_target' (hKt hz))
      have hi : H (H.symm z) = z := H.right_inv' (hKt hz)
      rw [hi] at hh
      rw [hh]
      exact Q.map_source' (hHs (H.map_target' (hKt hz)))
  refine ⟨D, K, hK, rfl, hKU, ⟨I⟩, I.endpoint_fixed_on 0 rfl, ?_⟩
  intro z hz
  have hDz : Dₛ z ∈ H.source :=
    SupportedDiffeomorph.mapsTo_source H Dₛ.toEquiv hKs A.endpoint_fixed_outside hz
  change DP (DQ (Q z)) = P (Dₜ (H (Dₛ z)))
  rw [SupportedDiffeomorph.extension_chart Q Dₛ hKₛ hKQ A.endpoint_fixed_outside (hHs hz)]
  rw [← hdiagram (Dₛ z) hDz]
  exact
    SupportedDiffeomorph.extension_chart P Dₜ hKₜ hKP B.endpoint_fixed_outside
      (hHt (H.map_source' hDz))

attribute [local instance 100] Classical.propDecidable in
theorem TransverseGerms.exists_common_transverse_range {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (h0 : (0 : E) ∈ H.source) (hQzero : Q 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z) :
    ∃ (Q' P' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (U : Set Z),
      IsOpen U ∧
        (0 : Z) ∈ U ∧
          Q'.source = H.source ∧
            P'.source = H.target ∧
              Q'.target = U ∧
                P'.target = U ∧ U ⊆ Q.target ∩ P.target ∧ (∀ z, Q' z = Q z) ∧ (∀ z, P' z = P z) :=
  by
  let Q' := PartialChart.restrictSource Q H.open_source
  let P' := PartialChart.restrictSource P H.open_target
  have hQs : Q'.source = H.source := Set.inter_eq_right.mpr hHs
  have hPs : P'.source = H.target := Set.inter_eq_right.mpr hHt
  have hsame : Q'.target = P'.target := by
    ext y
    constructor
    · intro hy
      have hz : Q'.symm y ∈ H.source := hQs ▸ Q'.map_target' hy
      have hw : H (Q'.symm y) ∈ P'.source := hPs.symm ▸ H.map_source' hz
      have heq : P' (H (Q'.symm y)) = y := (hdiagram _ hz).trans (Q'.right_inv' hy)
      exact heq ▸ P'.map_source' hw
    · intro hy
      have hz : P'.symm y ∈ H.target := hPs ▸ P'.map_target' hy
      have hw : H.symm (P'.symm y) ∈ Q'.source := hQs.symm ▸ H.map_target' hz
      have heq : Q' (H.symm (P'.symm y)) = y := by
        have hh := hdiagram (H.symm (P'.symm y)) (H.map_target' hz)
        have hi : H (H.symm (P'.symm y)) = P'.symm y := H.right_inv' hz
        rw [hi] at hh
        exact hh.symm.trans (P'.right_inv' hy)
      exact heq ▸ Q'.map_source' hw
  have h0U : (0 : Z) ∈ Q'.target := by
    have hh := Q'.map_source' (hQs.symm ▸ h0)
    change Q 0 ∈ Q'.target at hh
    rwa [hQzero] at hh
  refine
    ⟨Q', P', Q'.target, Q'.open_target, h0U, hQs, hPs, rfl, hsame.symm, ?_, fun _ => rfl, fun _ =>
      rfl⟩
  intro y hy
  have hyP : y ∈ P'.target := hsame ▸ hy
  exact ⟨hy.1, hyP.1⟩

theorem TransverseGerms.exists_common_transverse_coordinates {D B Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (e : D ≃L[ℝ] B)
    (Q P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQ0 : (0 : D) ∈ Q.source)
    (hP0 : (0 : D) ∈ P.source) (hQfix : Q 0 = 0) (hPfix : P 0 = 0) :
    ∃ (Q' P' : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B Z ∞) (H :
      PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, B) B B ∞) (U : Set Z),
      IsOpen U ∧
        (0 : Z) ∈ U ∧
          (0 : B) ∈ H.source ∧
            H 0 = 0 ∧
              Q' 0 = 0 ∧
                P' 0 = 0 ∧
                  Q'.source = H.source ∧
                    P'.source = H.target ∧
                      Q'.target = U ∧
                        P'.target = U ∧
                          U ⊆ Q.target ∩ P.target ∧
                            (∀ u ∈ Q'.source, e.symm u ∈ Q.source) ∧
                              (∀ u ∈ P'.source, e.symm u ∈ P.source) ∧
                                (∀ u, Q' u = Q (e.symm u)) ∧
                                  (∀ u, P' u = P (e.symm u)) ∧
                                    (∀ u ∈ H.source, P' (H u) = Q' u) ∧
                                      ∀ u, H u = e (P.symm (Q (e.symm u))) := by
  let R := e.symm.toDiffeomorph.toPartialDiffeomorph
  let Qe := R.trans Q
  let Pe := R.trans P
  have hQe0 : (0 : B) ∈ Qe.source := by
    change (0 : B) ∈ Set.univ ∧ e.symm 0 ∈ Q.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hQ0⟩
  have hPe0 : (0 : B) ∈ Pe.source := by
    change (0 : B) ∈ Set.univ ∧ e.symm 0 ∈ P.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hP0⟩
  have hQezero : Qe 0 = 0 := by change Q (e.symm 0) = 0; rw [map_zero, hQfix]
  have hPezero : Pe 0 = 0 := by change P (e.symm 0) = 0; rw [map_zero, hPfix]
  let H := Qe.trans Pe.symm
  have h0 : (0 : B) ∈ H.source := by
    refine ⟨hQe0, ?_⟩
    change Qe 0 ∈ Pe.target
    rw [hQezero, ← hPezero]
    exact Pe.map_source' hPe0
  have hH0 : H 0 = 0 := by
    change Pe.symm (Qe 0) = 0
    rw [hQezero, ← hPezero]
    exact Pe.left_inv' hPe0
  have hHs : H.source ⊆ Qe.source := fun _ hu => hu.1
  have hHt : H.target ⊆ Pe.source := fun _ hu => hu.1
  have hdiagram (u : B) (hu : u ∈ H.source) : Pe (H u) = Qe u := Pe.right_inv' hu.2
  obtain ⟨Q', P', U, hU, h0U, hQs, hPs, hQt, hPt, hUsub, hQmap, hPmap⟩ :=
    exists_common_transverse_range Qe Pe H h0 hQezero hHs hHt hdiagram
  refine
    ⟨Q', P', H, U, hU, h0U, h0, hH0, (hQmap 0).trans hQezero, (hPmap 0).trans hPezero, hQs, hPs,
      hQt, hPt, ?_, ?_, ?_, hQmap, hPmap, ?_, fun _ => rfl⟩
  · intro z hz
    exact ⟨(hUsub hz).1.1, (hUsub hz).2.1⟩
  · intro u hu
    exact (hHs (hQs ▸ hu)).2
  · intro u hu
    exact (hHt (hPs ▸ hu)).2
  · intro u hu
    exact (hPmap (H u)).trans ((hdiagram u hu).trans (hQmap u).symm)

theorem TransverseGerms.exists_restricted_native_cylinder {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U O : Set Z}
    (hsource : A.source = U ×ˢ Set.univ) (hO : IsOpen O) (hOU : O ⊆ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞,
      B.source = O ×ˢ Set.univ ∧
        B.source ⊆ A.source ∧
          B.target ⊆ A.target ∧
            (∀ z, B z = A z) ∧
              ∀ y ∈ B.target,
                V y =
                  FlowConstruction.partialChartField B.symm (fun _ : Z × ℝ => (0, 1)) y := by
  let B := PartialChart.restrictSource A (hO.prod isOpen_univ)
  have hsub : O ×ˢ (Set.univ : Set ℝ) ⊆ A.source := by
    rw [hsource]
    exact fun z hz => ⟨hOU hz.1, hz.2⟩
  have hBs : B.source = O ×ˢ Set.univ := Set.inter_eq_right.mpr hsub
  exact ⟨B, hBs, fun _ hz => hz.1, fun _ hy => hy.1, fun _ => rfl, fun y hy => hA y hy.1⟩

attribute [local instance 100] Classical.propDecidable in
theorem TransverseGerms.splitCoordinates_negative_zero_iff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℝ) :
    (MorseHandle.splitCoordinates w z).1 = 0 ↔ ∀ i, w i = -1 → z i = 0 := by
  constructor
  · intro h i hi
    have hh := congrArg (fun v : MorseHandle.NegativeSpace w => v ⟨i, hi⟩) h
    exact hh
  · intro h
    ext i
    exact h i.1 i.2

attribute [local instance 100] Classical.propDecidable in
theorem TransverseGerms.splitCoordinates_positive_zero_iff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    (MorseHandle.splitCoordinates w z).2 = 0 ↔ ∀ i, w i = 1 → z i = 0 := by
  constructor
  · intro h i hi
    have hn : w i ≠ -1 := by rw [hi]; norm_num
    have hh := congrArg (fun v : MorseHandle.PositiveSpace w => v ⟨i, hn⟩) h
    exact hh
  · intro h
    ext i
    exact h i.1 ((hw i.1).resolve_left i.2)

attribute [local instance 100] Classical.propDecidable in
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

theorem SignedCoordinates.positive_of_not_negative {ι : Type*} {w : ι → ℝ}
    (hw : ∀ i, w i = -1 ∨ w i = 1) {i : ι} (hi : w i ≠ -1) : w i = 1 :=
  (hw i).resolve_left hi

theorem SignedCoordinates.exists_equiv_of_negative_card_eq {ι κ : Type*} [Fintype ι]
    [Fintype κ] (w₀ : ι → ℝ) (w₁ : κ → ℝ) (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1)
    (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1) (hcard : Fintype.card ι = Fintype.card κ)
    [Fintype { i // w₀ i = -1 }] [Fintype { i // w₁ i = -1 }]
    (hneg : Fintype.card { i // w₀ i = -1 } = Fintype.card { i // w₁ i = -1 }) :
    ∃ e : ι ≃ κ, ∀ i, w₁ (e i) = w₀ i := by
  classical
  let eN : { i // w₀ i = -1 } ≃ { i // w₁ i = -1 } := Fintype.equivOfCardEq hneg
  have hpos : Fintype.card { i // ¬w₀ i = -1 } = Fintype.card { i // ¬w₁ i = -1 } := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard, hneg]
  let eP : { i // ¬w₀ i = -1 } ≃ { i // ¬w₁ i = -1 } := Fintype.equivOfCardEq hpos
  let e₀ := Equiv.sumCompl (fun i : ι => w₀ i = -1)
  let e₁ := Equiv.sumCompl (fun i : κ => w₁ i = -1)
  let e := e₀.symm.trans ((Equiv.sumCongr eN eP).trans e₁)
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨z, rfl⟩ := e₀.surjective i
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
  cases z with
  | inl x =>
    change w₁ (eN x) = w₀ x
    exact (eN x).property.trans x.property.symm
  | inr x =>
    change w₁ (eP x) = w₀ x
    exact
      (positive_of_not_negative h₁ (eP x).property).trans
        (positive_of_not_negative h₀ x.property).symm

theorem MorseCancellation.exists_coordinate_enum {m n : ℕ} (hn : n = m + 1) (j : Fin n) :
    ∃ ρ : Option (Fin m) ≃ Fin n, ρ Option.none = j := by
  let ρ₀ : Option (Fin m) ≃ Fin n := Fintype.equivOfCardEq (by simp [hn])
  exact ⟨ρ₀.trans (Equiv.swap (ρ₀ Option.none) j), by simp⟩

attribute [local instance 100] Classical.propDecidable in
theorem SignedCoordinates.negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) :
    Fintype.card { j // w j = -1 } =
      (if w (ρ Option.none) = -1 then 1 else 0) +
        Fintype.card { i : Fin m // w (ρ (Option.some i)) = -1 } := by
  have he : { i : Option (Fin m) // w (ρ i) = -1 } ≃ { j : Fin n // w j = -1 } :=
    ρ.subtypeEquiv (fun _ => Iff.rfl)
  rw [← Fintype.card_congr he]
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]

attribute [local instance 100] Classical.propDecidable in
theorem SignedCoordinates.exists_adjacent_sign_enumerations {m : ℕ}
    (w₀ w₁ : Fin (m + 1) → ℝ) (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1) (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hindex : Fintype.card { i // w₁ i = -1 } = Fintype.card { i // w₀ i = -1 } + 1) :
    ∃ ρ₀ ρ₁ : Option (Fin m) ≃ Fin (m + 1),
      w₀ (ρ₀ Option.none) = 1 ∧
        w₁ (ρ₁ Option.none) = -1 ∧ ∀ i, w₀ (ρ₀ (Option.some i)) = w₁ (ρ₁ (Option.some i)) := by
  have hbound := Fintype.card_subtype_le (fun i : Fin (m + 1) => w₁ i = -1)
  have hNpos : 0 < Fintype.card { i // w₁ i = -1 } := by omega
  have hPpos : 0 < Fintype.card { i // ¬w₀ i = -1 } := by
    rw [Fintype.card_subtype_compl]
    omega
  let j₀ := Classical.choice (Fintype.card_pos_iff.mp hPpos)
  let j₁ := Classical.choice (Fintype.card_pos_iff.mp hNpos)
  obtain ⟨ρ₀, hρ₀⟩ := MorseCancellation.exists_coordinate_enum rfl j₀.1
  obtain ⟨ρ₁, hρ₁⟩ := MorseCancellation.exists_coordinate_enum rfl j₁.1
  have hfirst₀ : w₀ (ρ₀ Option.none) = 1 := by
    rw [hρ₀]
    exact positive_of_not_negative h₀ j₀.2
  have hfirst₁ : w₁ (ρ₁ Option.none) = -1 := by
    rw [hρ₁]
    exact j₁.2
  let σ₀ := fun i : Fin m => w₀ (ρ₀ (Option.some i))
  let σ₁ := fun i : Fin m => w₁ (ρ₁ (Option.some i))
  have hrest : Fintype.card { i // σ₀ i = -1 } = Fintype.card { i // σ₁ i = -1 } := by
    have hcount₀ := negative_card_split ρ₀ w₀
    have hcount₁ := negative_card_split ρ₁ w₁
    rw [hfirst₀] at hcount₀
    rw [hfirst₁] at hcount₁
    norm_num at hcount₀ hcount₁
    change
      Fintype.card { i // w₀ (ρ₀ (Option.some i)) = -1 } =
        Fintype.card { i // w₁ (ρ₁ (Option.some i)) = -1 }
    omega
  obtain ⟨η, hη⟩ :=
    exists_equiv_of_negative_card_eq σ₀ σ₁ (fun i => h₀ _) (fun i => h₁ _) rfl hrest
  refine ⟨ρ₀, (Equiv.optionCongr η).trans ρ₁, hfirst₀, ?_, ?_⟩
  · simpa using hfirst₁
  · intro i
    exact (hη i).symm

attribute [local instance 100] Classical.propDecidable in
theorem SignedCoordinates.exists_adjacent_sign_enumerations_of_dimension {m n : ℕ}
    (hn : n = m + 1) (w₀ w₁ : Fin n → ℝ) (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1)
    (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hindex : Fintype.card { i // w₁ i = -1 } = Fintype.card { i // w₀ i = -1 } + 1) :
    ∃ ρ₀ ρ₁ : Option (Fin m) ≃ Fin n,
      w₀ (ρ₀ Option.none) = 1 ∧
        w₁ (ρ₁ Option.none) = -1 ∧ ∀ i, w₀ (ρ₀ (Option.some i)) = w₁ (ρ₁ (Option.some i)) := by
  subst n
  exact exists_adjacent_sign_enumerations w₀ w₁ h₀ h₁ hindex

attribute [local instance 100] Classical.propDecidable in
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

theorem TransverseGerms.hasFDerivAt_scalar_displacement {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f g : A → A} (hfzero : f 0 = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ A) 0)
    (hscalar : ∀ x, ∃ α ∈ Set.Icc (0 : ℝ) 1, g x = x + α • (f x - x)) :
    HasFDerivAt g (ContinuousLinearMap.id ℝ A) 0 := by
  have hgzero : g 0 = 0 := by
    obtain ⟨α, -, he⟩ := hscalar 0
    simpa only [hfzero, sub_self, smul_zero, add_zero] using he
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf.isLittleO.bound hε] with x hx
  simp only [hfzero, hgzero, sub_zero, ContinuousLinearMap.id_apply] at hx ⊢
  obtain ⟨α, hα, he⟩ := hscalar x
  rw [he, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) hα.2).trans hx

theorem TransverseGerms.exists_open_transverse_convex_blend {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {φ : (A × B) → (A × B)} {U : Set (A × B)} (hU : IsOpen U) (hzero : (0 : A × B) ∈ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hφzero : φ 0 = 0) (L : (A × B) →L[ℝ] (A × B))
    (hder : fderiv ℝ φ 0 = L) (P : A ≃L[ℝ] A) (hP : ∀ x : A, (L (x, 0)).1 = P x) :
    ∃ W : Set (A × B),
      IsOpen W ∧
        (0 : A × B) ∈ W ∧
          W ⊆ U ∧
            ∀ x : A,
              (x, (0 : B)) ∈ W →
                ∀ α ∈ Set.Icc (0 : ℝ) 1, (φ (x, 0) + α • (L (x, 0) - φ (x, 0))).1 = 0 ↔ x = 0 := by
  let ι := ContinuousLinearMap.inl ℝ A B
  let π := ContinuousLinearMap.fst ℝ A B
  let H : A → A := fun x => P.symm ((φ (x, 0)).1)
  let S : Set A := ι ⁻¹' U
  have hS : IsOpen S := hU.preimage ι.continuous
  have hSzero : (0 : A) ∈ S := hzero
  have hH : ContDiffOn ℝ ∞ H S :=
    P.symm.contDiff.comp_contDiffOn
      (π.contDiff.comp_contDiffOn (hφ.comp ι.contDiff.contDiffOn (fun x hx => hx)))
  have hfd : HasFDerivAt φ L 0 := by
    rw [← hder]
    exact ((hφ.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)).hasFDerivAt
  have hHd : HasFDerivAt H (P.symm.toContinuousLinearMap.comp (π.comp (L.comp ι))) 0 :=
    P.symm.toContinuousLinearMap.hasFDerivAt.comp (0 : A)
      (π.hasFDerivAt.comp (0 : A) (hfd.comp (f := ι) (0 : A) ι.hasFDerivAt))
  have hlinear :
    P.symm.toContinuousLinearMap.comp (π.comp (L.comp ι)) = ContinuousLinearMap.id ℝ A := by
    apply ContinuousLinearMap.ext
    intro x
    change P.symm ((L (x, 0)).1) = x
    rw [hP, P.symm_apply_apply]
  rw [hlinear] at hHd
  let u : A → A := fun x => H x - x
  have hu : ContDiffOn ℝ ∞ u S := hH.sub contDiffOn_id
  have hu0 : u 0 = 0 := by
    change P.symm ((φ (0 : A × B)).1) - 0 = 0
    rw [hφzero]
    simp
  have hdu : fderiv ℝ u 0 = 0 := by
    have hh := hHd.sub (hasFDerivAt_id (0 : A))
    change fderiv ℝ (H - id) 0 = 0
    simpa only [sub_self] using hh.fderiv
  obtain ⟨ρ, hρ, -, hlip⟩ :=
    SmallPerturbation.exists_closedBall_small_lipschitz_of_fderiv_zero hS hSzero hu hdu
      (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let W := U ∩ Metric.ball (0 : A × B) ρ
  refine
    ⟨W, hU.inter Metric.isOpen_ball, ⟨hzero, Metric.mem_ball_self hρ⟩, Set.inter_subset_left, ?_⟩
  intro x hx α hα
  have hxρ : x ∈ Metric.closedBall (0 : A) ρ := by
    have hh := mem_ball_zero_iff.mp hx.2
    apply mem_closedBall_zero_iff.mpr
    simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x)] using hh.le
  have h0ρ : (0 : A) ∈ Metric.closedBall (0 : A) ρ := Metric.mem_closedBall_self hρ.le
  have herr : ‖u x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
    have hh := hlip.dist_le_mul x hxρ 0 h0ρ
    simpa only [hu0, dist_zero_right, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
  constructor
  · intro hz
    have he : x + (1 - α) • u x = 0 := by
      have hh := congrArg P.symm hz
      change P.symm ((φ (x, 0)).1 + α • ((L (x, 0)).1 - (φ (x, 0)).1)) = P.symm 0 at hh
      simp only [map_add, map_smul, map_sub, hP, P.symm_apply_apply, map_zero] at hh
      change H x + α • (x - H x) = 0 at hh
      calc
        x + (1 - α) • u x = H x + α • (x - H x) := by dsimp [u]; module
        _ = 0 := hh
    have he' : x = -((1 - α) • u x) := eq_neg_of_add_eq_zero_left he
    have hnorm : ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
      calc
        ‖x‖ = ‖-((1 - α) • u x)‖ := congrArg Norm.norm he'
        _ = ‖(1 - α) • u x‖ := (norm_neg _)
        _ = (1 - α) * ‖u x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hα.2])]
        _ ≤ ‖u x‖ := (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hα.1]))
        _ ≤ (1 / 2 : ℝ) * ‖x‖ := herr
    exact norm_eq_zero.mp (le_antisymm (by linarith [norm_nonneg x]) (norm_nonneg x))
  · rintro rfl
    simp only [show ((0 : A), (0 : B)) = (0 : A × B) from rfl, hφzero, map_zero, sub_self,
      smul_zero, add_zero, Prod.fst_zero]

theorem TransverseGerms.exists_supported_transverse_germ_linearization {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0) (P : A ≃L[ℝ] A)
    (hP : ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (C : (A × B) ≃L[ℝ] (A × B)) (H : ℝ × (A × B) → A × B) (K : Set (A × B)),
      C.toContinuousLinearMap = fderiv ℝ Φ 0 ∧
        IsCompact K ∧
          K ⊆ Φ.target ∧
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H ∧
              (∀ y, H (0, y) = y) ∧
                (∀ t,
                    ∃ D : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞,
                      ∀ y, D y = H (t, y)) ∧
                  (∀ t y, y ∉ K → H (t, y) = y) ∧
                    (∀ t, H (t, 0) = 0) ∧
                      (∀ t x, (x, (0 : B)) ∈ Φ.source → ((H (t, Φ (x, 0))).1 = 0 ↔ x = 0)) ∧
                        (∀ t, fderiv ℝ (fun x => H (t, Φ x)) 0 = fderiv ℝ Φ 0) ∧
                          (fun x => H (1, Φ x)) =ᶠ[𝓝 (0 : A × B)] C := by
  have hΦ : ContDiffOn ℝ ∞ (Φ : (A × B) → A × B) Φ.source := Φ.contMDiffOn_toFun.contDiffOn
  have hbij : Function.Bijective (fderiv ℝ Φ 0) := by
    have hh := PartialChart.bijective_mfderiv Φ hzero
    change Function.Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ 0 : (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ 0).toLinearMap hbij).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ Φ 0 := rfl
  obtain ⟨W, hW, hWzero, hWsource, hblend⟩ :=
    exists_open_transverse_convex_blend Φ.open_source hzero hΦ hΦzero C.toContinuousLinearMap
      hC.symm P hP
  let U := Φ '' W
  have hU : IsOpen U := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW hWsource
  have hUzero : (0 : A × B) ∈ U := ⟨0, hWzero, hΦzero⟩
  have hUtarget : U ⊆ Φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hWsource hx)
  have htzero : (0 : A × B) ∈ Φ.target := hUtarget hUzero
  have hinvzero : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' hzero
    change Φ.symm (Φ 0) = 0 at hh
    rwa [hΦzero] at hh
  let G : (A × B) → A × B := C ∘ Φ.symm
  have hG : ContDiffOn ℝ ∞ G U :=
    C.contDiff.comp_contDiffOn (Φ.contMDiffOn_invFun.contDiffOn.mono hUtarget)
  have hGzero : G 0 = 0 := by simp only [G, Function.comp_apply, hinvzero, map_zero]
  have hdf :=
    ((hΦ.contDiffAt (Φ.open_source.mem_nhds hzero)).differentiableAt (by simp)).hasFDerivAt
  have hdi :=
    ((Φ.contMDiffOn_invFun.contDiffOn.contDiffAt (Φ.open_target.mem_nhds htzero)).differentiableAt
        (by simp)).hasFDerivAt
  have hdf' : HasFDerivAt (Φ : (A × B) → A × B) (fderiv ℝ Φ 0) (Φ.symm 0) := by
    rw [hinvzero]
    exact hdf
  have hcomp := hdf'.comp (f := Φ.symm) (0 : A × B) hdi
  have hid : (Φ ∘ Φ.symm) =ᶠ[𝓝 (0 : A × B)] id := by
    filter_upwards [Φ.open_target.mem_nhds htzero] with y hy
    exact Φ.right_inv' hy
  have hcancel : (fderiv ℝ Φ 0).comp (fderiv ℝ Φ.symm 0) = ContinuousLinearMap.id ℝ (A × B) :=
    hcomp.fderiv.symm.trans (hid.fderiv_eq.trans fderiv_id)
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ (A × B) := by
    have hh := C.toContinuousLinearMap.hasFDerivAt.comp (f := Φ.symm) (0 : A × B) hdi
    exact hh.fderiv.trans (by rw [hC]; exact hcancel)
  obtain ⟨H, K, hK, hKU, hH, hH0, hdiff, hfix, hscalar, hgerm⟩ :=
    SmallPerturbation.exists_supported_tangent_identity_isotopy hU hUzero hG hGzero hdG
  have hHorigin (t : ℝ) : H (t, 0) = 0 := by
    obtain ⟨α, -, hα⟩ := hscalar t 0
    simpa only [hGzero, sub_self, smul_zero, add_zero] using hα
  have hdG' : HasFDerivAt G (ContinuousLinearMap.id ℝ (A × B)) 0 := by
    rw [← hdG]
    exact ((hG.contDiffAt (hU.mem_nhds hUzero)).differentiableAt (by simp)).hasFDerivAt
  have hHder (t : ℝ) : HasFDerivAt (fun y => H (t, y)) (ContinuousLinearMap.id ℝ (A × B)) 0 :=
    hasFDerivAt_scalar_displacement hGzero hdG' (hscalar t)
  refine ⟨C, H, K, hC, hK, hKU.trans hUtarget, hH, hH0, hdiff, hfix, hHorigin, ?_, ?_, ?_⟩
  · intro t x hx
    by_cases hxin : Φ (x, 0) ∈ K
    · obtain ⟨z, hz, hzeq⟩ := hKU hxin
      have hzx : z = (x, 0) := Φ.toOpenPartialHomeomorph.injOn (hWsource hz) hx hzeq
      have hxW : (x, (0 : B)) ∈ W := hzx ▸ hz
      obtain ⟨α, hα, he⟩ := hscalar t (Φ (x, 0))
      have hGΦ : G (Φ (x, 0)) = C (x, 0) := by
        dsimp [G]
        exact congrArg C (Φ.left_inv' hx)
      rw [he, hGΦ]
      exact hblend x hxW α hα
    · rw [hfix t _ hxin]
      exact hunique x hx
  · intro t
    have hh : HasFDerivAt (fun y => H (t, y)) (ContinuousLinearMap.id ℝ (A × B)) (Φ 0) := by
      rw [hΦzero]
      exact hHder t
    simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using
      (hh.comp (f := Φ) (0 : A × B) hdf).fderiv
  · have hΦtend : Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
      have hh := Φ.toOpenPartialHomeomorph.continuousAt hzero
      change Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
      rwa [hΦzero] at hh
    filter_upwards [hgerm.comp_tendsto hΦtend, Φ.open_source.mem_nhds hzero] with x hx hxsource
    change H (1, Φ x) = C x
    change H (1, Φ x) = G (Φ x) at hx
    rw [hx]
    dsimp [G]
    exact congrArg C (Φ.left_inv' hxsource)

def TransverseGerms.transverseBlockMap {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B)
    (Q : B →L[ℝ] A) (R : A →L[ℝ] B) : (A × B) →L[ℝ] (A × B) :=
  let T :=
    P.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ A B + Q.comp (ContinuousLinearMap.snd ℝ A B))
  T.prod (S.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ A B) + R.comp T)

theorem TransverseGerms.exists_transverse_block_factorization {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] (C : (A × B) ≃L[ℝ] (A × B)) (P : A ≃L[ℝ] A)
    (hP : ∀ x : A, (C (x, 0)).1 = P x) :
    ∃ (Q : B →L[ℝ] A) (R : A →L[ℝ] B) (S : B ≃L[ℝ] B),
      C.toContinuousLinearMap = transverseBlockMap P S Q R := by
  let Q : B →L[ℝ] A :=
    P.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℝ A B).comp
        (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)))
  let R : A →L[ℝ] B :=
    (ContinuousLinearMap.snd ℝ A B).comp
      (C.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℝ A B).comp P.symm.toContinuousLinearMap))
  let S₀ : B →L[ℝ] B :=
    (ContinuousLinearMap.snd ℝ A B).comp
        (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)) -
      R.comp
        ((ContinuousLinearMap.fst ℝ A B).comp
          (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)))
  have hQ (y : B) : P (Q y) = (C (0, y)).1 := P.apply_symm_apply _
  have hR (x : A) : R (P x) = (C (x, 0)).2 := by
    change (C (P.symm (P x), 0)).2 = _
    rw [P.symm_apply_apply]
  have hsplit (p : A × B) : C p = C (p.1, 0) + C (0, p.2) := by
    rw [← map_add]
    congr 1
    simp
  have hmodel (p : A × B) : C p = (P (p.1 + Q p.2), S₀ p.2 + R (P (p.1 + Q p.2))) := by
    apply Prod.ext
    · rw [hsplit, Prod.fst_add, map_add, hP, hQ]
    · rw [hsplit, Prod.snd_add, map_add, map_add, hR, hQ]
      change
        (C (p.1, 0)).2 + (C (0, p.2)).2 =
          ((C (0, p.2)).2 - R ((C (0, p.2)).1)) + ((C (p.1, 0)).2 + R ((C (0, p.2)).1))
      abel
  have haxis (y : B) : C (-Q y, y) = (0, S₀ y) := by
    rw [hmodel]
    simp
  have hbij : Function.Bijective S₀ := by
    constructor
    · intro x y hxy
      have he : C (-Q x, x) = C (-Q y, y) := by rw [haxis, haxis, hxy]
      exact congrArg Prod.snd (C.injective he)
    · intro y
      obtain ⟨p, hp⟩ := C.surjective (0, y)
      have hfirst : P (p.1 + Q p.2) = 0 := by
        have hh := congrArg Prod.fst hp
        rwa [hmodel] at hh
      have hsecond : S₀ p.2 + R (P (p.1 + Q p.2)) = y := by
        have hh := congrArg Prod.snd hp
        rwa [hmodel] at hh
      exact ⟨p.2, by simpa only [hfirst, map_zero, add_zero] using hsecond⟩
  let S := (LinearEquiv.ofBijective S₀.toLinearMap hbij).toContinuousLinearEquiv
  refine ⟨Q, R, S, ?_⟩
  apply ContinuousLinearMap.ext
  intro p
  exact hmodel p

theorem TransverseGerms.exists_supported_lower_shear_isotopy {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] (R : A →L[ℝ] B) {U : Set (A × B)} (hU : IsOpen U)
    (hzero : (0 : A × B) ∈ U) :
    ∃ (H : ℝ × (A × B) → A × B) (K : Set (A × B)),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H ∧
            (∀ p, H (0, p) = p) ∧
              (∀ t,
                  ∃ D : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞,
                    ∀ p, D p = H (t, p)) ∧
                (∀ t p, p ∉ K → H (t, p) = p) ∧
                  (∀ t p, (H (t, p)).1 = p.1) ∧
                    (∀ t y, H (t, ((0 : A), y)) = (0, y)) ∧
                      (fun p => H (1, p)) =ᶠ[𝓝 (0 : A × B)] (fun p => (p.1, p.2 + R p.1)) := by
  let e := ContinuousLinearEquiv.prodComm ℝ A B
  let U' := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  have hzero' : (0 : B × A) ∈ U' := by simpa only [U', Set.mem_preimage, map_zero] using hzero
  obtain ⟨J, K', hK', hK'U', hJ, hJ0, hdiff, hfix, hsecond, hcore, hgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy R hU' hzero'
  let H : ℝ × (A × B) → A × B := fun p => e.symm (J (p.1, e p.2))
  let K := e.symm '' K'
  have hK : IsCompact K := hK'.image e.symm.continuous
  have hKU : K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hK'U' hy
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H :=
    e.symm.contDiff.contMDiff.comp
      (hJ.comp (contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)))
  refine ⟨H, K, hK, hKU, hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change e.symm (J (0, e p)) = p
    rw [hJ0, e.symm_apply_apply]
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    refine ⟨(e.toDiffeomorph.trans D).trans e.symm.toDiffeomorph, ?_⟩
    intro p
    change e.symm (D (e p)) = e.symm (J (t, e p))
    rw [hD]
  · intro t p hp
    have hnot : e p ∉ K' := fun h => hp ⟨e p, h, e.symm_apply_apply p⟩
    change e.symm (J (t, e p)) = p
    rw [hfix t _ hnot, e.symm_apply_apply]
  · intro t p
    exact hsecond t (e p)
  · intro t y
    change e.symm (J (t, (y, (0 : A)))) = (0, y)
    rw [hcore]
    rfl
  · have ht : Filter.Tendsto e (𝓝 (0 : A × B)) (𝓝 0) := by
      simpa only [map_zero] using e.continuous.tendsto (0 : A × B)
    filter_upwards [hgerm.comp_tendsto ht] with p hp
    change J (1, e p) = ((e p).1 + R (e p).2, (e p).2) at hp
    change e.symm (J (1, e p)) = (p.1, p.2 + R p.1)
    rw [hp]
    rfl

theorem TransverseGerms.exists_supported_transverse_block_reduction {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0) (P : A ≃L[ℝ] A)
    (hP : ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (S : B ≃L[ℝ] B) (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (Kₛ Kₜ :
      Set (A × B)),
      IsCompact Kₛ ∧
        Kₛ ⊆ Φ.source ∧
          IsCompact Kₜ ∧
            Kₜ ⊆ Φ.target ∧
              Nonempty
                  (SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ
                    {p : A × B | p.2 = 0}) ∧
                Nonempty
                    (SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)}) ∧
                  Set.MapsTo Dₛ Φ.source Φ.source ∧
                    Set.MapsTo Dₜ Φ.target Φ.target ∧
                      (∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Dₜ (Φ (Dₛ (x, 0)))).1 = 0 ↔ x = 0)) ∧
                        (fun p => Dₜ (Φ (Dₛ p))) =ᶠ[𝓝 (0 : A × B)] (fun p => (P p.1, S p.2)) := by
  obtain ⟨C, H, K₁, hC, hK₁, hK₁target, hH, hH0, hHdiff, hHfix, hHorigin, hHunique, -, hHgerm⟩ :=
    exists_supported_transverse_germ_linearization Φ hzero hΦzero P hP hunique
  have hCP (x : A) : (C (x, 0)).1 = P x := by
    change (C.toContinuousLinearMap (x, 0)).1 = P x
    rw [hC]
    exact hP x
  obtain ⟨Q, R, S, hfactor⟩ := exists_transverse_block_factorization C P hCP
  obtain ⟨J, K₂, hK₂, hK₂source, hJ, hJ0, hJdiff, hJfix, -, hJcore, hJgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy (-Q) Φ.open_source hzero
  have htzero : (0 : A × B) ∈ Φ.target := by
    have hh := Φ.map_source' hzero
    rwa [hΦzero] at hh
  obtain ⟨L, K₃, hK₃, hK₃target, hL, hL0, hLdiff, hLfix, hLfirst, hLcore, hLgerm⟩ :=
    exists_supported_lower_shear_isotopy (-R) Φ.open_target htzero
  obtain ⟨Dₕ, hDₕ⟩ := hHdiff 1
  obtain ⟨Dₛ, hDₛ⟩ := hJdiff 1
  obtain ⟨Dₗ, hDₗ⟩ := hLdiff 1
  let Dₜ := Dₕ.trans Dₗ
  let Kₜ := K₁ ∪ K₃
  have hKₜ : IsCompact Kₜ := hK₁.union hK₃
  have hKₜtarget : Kₜ ⊆ Φ.target := Set.union_subset hK₁target hK₃target
  have hsrc : SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ K₂ {p : A × B | p.2 = 0} := by
    refine ⟨J, hJ, hJ0, fun p => (hDₛ p).symm, hJdiff, hJfix, ?_⟩
    rintro t ⟨x, y⟩ hy
    change y = 0 at hy
    subst y
    exact hJcore t x
  have htgt : SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)} := by
    let T : ℝ × (A × B) → A × B := fun p => L (p.1, H p)
    have hT : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ T :=
      hL.comp (contMDiff_fst.prodMk hH)
    refine ⟨T, hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      change L (0, H (0, p)) = p
      rw [hH0, hL0]
    · intro p
      change L (1, H (1, p)) = Dₗ (Dₕ p)
      rw [hDₗ, hDₕ]
    · intro t
      obtain ⟨Eₕ, hEₕ⟩ := hHdiff t
      obtain ⟨Eₗ, hEₗ⟩ := hLdiff t
      refine ⟨Eₕ.trans Eₗ, ?_⟩
      intro p
      change Eₗ (Eₕ p) = L (t, H (t, p))
      rw [hEₗ, hEₕ]
    · intro t p hp
      change L (t, H (t, p)) = p
      rw [hHfix t p (fun h => hp (Or.inl h)), hLfix t p (fun h => hp (Or.inr h))]
    · intro t p hp
      have hp0 : p = 0 := Set.mem_singleton_iff.mp hp
      subst p
      change L (t, H (t, 0)) = 0
      rw [hHorigin]
      exact hLcore t 0
  have hsrczero : Dₛ (0 : A × B) = 0 := hsrc.endpoint_fixed_on 0 rfl
  have hsrctend : Filter.Tendsto Dₛ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Dₛ.continuous.tendsto (0 : A × B)
    rwa [hsrczero] at hh
  refine
    ⟨S, Dₛ, Dₜ, K₂, Kₜ, hK₂, hK₂source, hKₜ, hKₜtarget, ⟨hsrc⟩, ⟨htgt⟩,
      SupportedDiffeomorph.mapsTo_source Φ Dₛ.toEquiv hK₂source hsrc.endpoint_fixed_outside,
      SupportedDiffeomorph.mapsTo_source Φ.symm Dₜ.toEquiv hKₜtarget
        htgt.endpoint_fixed_outside,
      ?_, ?_⟩
  · intro x hx
    have hfixed : Dₛ (x, (0 : B)) = (x, 0) := hsrc.endpoint_fixed_on (x, 0) rfl
    rw [hfixed]
    change (Dₗ (Dₕ (Φ (x, 0)))).1 = 0 ↔ x = 0
    rw [hDₗ, hLfirst, hDₕ]
    exact hHunique 1 x hx
  · have hCtend : Filter.Tendsto (fun p => C (Dₛ p)) (𝓝 (0 : A × B)) (𝓝 0) := by
      have hh : Filter.Tendsto C (𝓝 (0 : A × B)) (𝓝 0) := by
        simpa only [map_zero] using C.continuous.tendsto (0 : A × B)
      exact hh.comp hsrctend
    filter_upwards [hHgerm.comp_tendsto hsrctend, hLgerm.comp_tendsto hCtend, hJgerm] with p hpH
      hpL hpJ
    change H (1, Φ (Dₛ p)) = C (Dₛ p) at hpH
    change L (1, C (Dₛ p)) = ((C (Dₛ p)).1, (C (Dₛ p)).2 + (-R) (C (Dₛ p)).1) at hpL
    change J (1, p) = (p.1 + (-Q) p.2, p.2) at hpJ
    change Dₗ (Dₕ (Φ (Dₛ p))) = (P p.1, S p.2)
    rw [hDₗ, hDₕ, hpH, hpL, hDₛ, hpJ]
    have hmodel (z : A × B) : C z = (P (z.1 + Q z.2), S z.2 + R (P (z.1 + Q z.2))) := by
      have hh := congrArg (fun T : (A × B) →L[ℝ] (A × B) => T z) hfactor
      exact hh
    rw [hmodel]
    simp only [neg_apply, add_neg_cancel_right, neg_add_cancel_right]

theorem TransverseGerms.exists_projected_equiv_of_native_transverse {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => Φ (x, 0))
        (fun y : B => (0, y)) 0 0) :
    ∃ P : A ≃L[ℝ] A, ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x := by
  let D : A →L[ℝ] (A × B) := (fderiv ℝ Φ 0).comp (ContinuousLinearMap.inl ℝ A B)
  let N : (A × B) →L[ℝ] A := ContinuousLinearMap.fst ℝ A B
  let J : B →L[ℝ] (A × B) := ContinuousLinearMap.inr ℝ A B
  have hdiff :=
    (Φ.contMDiffOn_toFun.contDiffOn.contDiffAt (Φ.open_source.mem_nhds hzero)).differentiableAt
      (by simp)
  have hι : HasFDerivAt (fun x : A => (x, (0 : B))) (ContinuousLinearMap.inl ℝ A B) (0 : A) :=
    (ContinuousLinearMap.inl ℝ A B).hasFDerivAt
  have hd : HasFDerivAt (fun x : A => Φ (x, 0)) D 0 :=
    hdiff.hasFDerivAt.comp (f := fun x : A => (x, (0 : B))) (0 : A) hι
  have hj : HasFDerivAt (fun y : B => (0, y)) J 0 := (ContinuousLinearMap.inr ℝ A B).hasFDerivAt
  have hcross : (0, (0 : B)) = Φ ((0 : A), 0) := hΦzero.symm
  have ht := htrans hcross
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv, hd.fderiv, hj.fderiv] at ht
  have hNJ : N.comp J = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  have hN : Function.Surjective N := fun x => ⟨(x, 0), rfl⟩
  have hJD : Function.Surjective (J.coprod D) :=
    TransverseCoordinates.surjective_coprod_swap D J ht
  have hbij : Function.Bijective (N.comp D) :=
    TransverseCoordinates.bijective_normal_comp N J D hN hJD hNJ rfl
  let P := (LinearEquiv.ofBijective (N.comp D).toLinearMap hbij).toContinuousLinearEquiv
  exact ⟨P, fun _ => rfl⟩

theorem TransverseGerms.exists_block_reduction_of_native_transverse {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => Φ (x, 0))
        (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ P : A ≃L[ℝ] A,
      (∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x) ∧
        ∃ (S : B ≃L[ℝ] B) (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (Kₛ Kₜ :
          Set (A × B)),
          IsCompact Kₛ ∧
            Kₛ ⊆ Φ.source ∧
              IsCompact Kₜ ∧
                Kₜ ⊆ Φ.target ∧
                  Nonempty
                      (SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ
                        {p : A × B | p.2 = 0}) ∧
                    Nonempty
                        (SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ
                          {(0 : A × B)}) ∧
                      Set.MapsTo Dₛ Φ.source Φ.source ∧
                        Set.MapsTo Dₜ Φ.target Φ.target ∧
                          (∀ x : A,
                              (x, (0 : B)) ∈ Φ.source → ((Dₜ (Φ (Dₛ (x, 0)))).1 = 0 ↔ x = 0)) ∧
                            (fun p => Dₜ (Φ (Dₛ p))) =ᶠ[𝓝 (0 : A × B)]
                              (fun p => (P p.1, S p.2)) := by
  obtain ⟨P, hP⟩ := exists_projected_equiv_of_native_transverse Φ hzero hΦzero htrans
  exact ⟨P, hP, exists_supported_transverse_block_reduction Φ hzero hΦzero P hP hunique⟩

theorem TransverseGerms.label_sheets_transverse_in_incoming_chart {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞) (hQsrc : (0 : A × B) ∈ Q.source)
    (hPsrc : (0 : A × B) ∈ P.source) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun x : A => Q (x, 0))
        (fun y : B => P (0, y)) 0 0) :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, A × B) (fun x : A => P.symm (Q (x, 0))) 0).coprod
        (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun y : B => P.symm (P (0, y))) 0)) := by
  have hcross : P ((0 : A), (0 : B)) = Q (0, 0) := hP0.trans hQ0.symm
  have htarget : Q ((0 : A), (0 : B)) ∈ P.target := by
    change Q (0 : A × B) ∈ P.target
    rw [hQ0, ← hP0]
    exact P.map_source' hPsrc
  have hι : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, A × B) (fun x : A => (x, (0 : B))) 0 :=
    ((contDiff_id : ContDiff ℝ ∞ (fun x : A => x)).prodMk
          contDiff_const).contMDiff.mdifferentiableAt
      (by simp)
  have hκ : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun y : B => ((0 : A), y)) 0 :=
    (contDiff_const.prodMk
          (contDiff_id : ContDiff ℝ ∞ (fun y : B => y))).contMDiff.mdifferentiableAt
      (by simp)
  have hqdiff : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, Z) (fun x : A => Q (x, 0)) 0 :=
    (Q.mdifferentiableAt (by simp) hQsrc).comp (f := fun x : A => (x, (0 : B))) 0 hι
  have hpdiff : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun y : B => P (0, y)) 0 :=
    (P.mdifferentiableAt (by simp) hPsrc).comp (f := fun y : B => ((0 : A), y)) 0 hκ
  exact
    ChartMapPerturbation.transverse_in_chart P.symm hqdiff hpdiff hcross htarget
      (htrans hcross)

theorem TransverseGerms.relative_label_sheet_germs {A B Z : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hPsrc : (0 : A × B) ∈ P.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ u ∈ H.source, P (H u) = Q u) :
    ((fun x : A => P.symm (Q (x, (0 : B)))) =ᶠ[𝓝 0] (fun x : A => H (x, 0))) ∧
      ((fun y : B => P.symm (P ((0 : A), y))) =ᶠ[𝓝 0] (fun y : B => (0, y))) := by
  have hnearH : ∀ᶠ x : A in 𝓝 0, (x, (0 : B)) ∈ H.source :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually (H.open_source.mem_nhds h0)
  have heqH : (fun x : A => P.symm (Q (x, (0 : B)))) =ᶠ[𝓝 0] (fun x : A => H (x, 0)) := by
    filter_upwards [hnearH] with x hx
    rw [← hdiagram (x, 0) hx]
    exact P.left_inv' (hHt (H.map_source' hx))
  have hnearP : ∀ᶠ y : B in 𝓝 0, ((0 : A), y) ∈ P.source :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually (P.open_source.mem_nhds hPsrc)
  have heqP : (fun y : B => P.symm (P ((0 : A), y))) =ᶠ[𝓝 0] (fun y : B => (0, y)) := by
    filter_upwards [hnearP] with y hy
    exact P.left_inv' hy
  exact ⟨heqH, heqP⟩

theorem TransverseGerms.relative_transverse_of_label_sheets {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun x : A => Q (x, 0))
        (fun y : B => P (0, y)) 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
      (fun y : B => (0, y)) 0 0 := by
  have hPsrc : (0 : A × B) ∈ P.source := by
    have hh := hHt (H.map_source' h0)
    rwa [hH0] at hh
  have ht := label_sheets_transverse_in_incoming_chart Q P (hHs h0) hPsrc hQ0 hP0 htrans
  obtain ⟨heqH, heqP⟩ := relative_label_sheet_germs Q P H h0 hPsrc hHt hdiagram
  rw [heqH.mfderiv_eq, heqP.mfderiv_eq] at ht
  exact fun _ => ht

theorem FlowSuspension.relative_intersection_of_native_unique_connection
    {A B Z E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) (h0U : (0 : Z) ∈ U) (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hHs : H.source ⊆ Q.source)
    (hQU : Q.target ⊆ U) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z) {p q : M}
    (hleftBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 0))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ H.source ∧ Q (x, 0) = z)
    (hrightBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 1))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ H.target, y.1 = 0 ∧ P y = z)
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x) :
    ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0) := by
  intro x hx
  constructor
  · intro hfirst
    have hzU : Q (x, 0) ∈ U := hQU (Q.map_source' (hHs hx))
    have hbot : Filter.Tendsto (fun t => F t (Φ (Q (x, 0), 0))) Filter.atBot (𝓝 q) :=
      (hleftBasin _ hzU).mpr ⟨x, hx, rfl⟩
    have htop1 : Filter.Tendsto (fun t => F t (Φ (Q (x, 0), 1))) Filter.atTop (𝓝 p) :=
      (hrightBasin _ hzU).mpr ⟨H (x, 0), H.map_source' hx, hfirst, hdiagram _ hx⟩
    rw [hflow _ hzU 1] at htop1
    have htop := (MorseCancellation.flow_time_atTop_limit_iff F 1 (Φ (Q (x, 0), 0)) p).mp htop1
    obtain ⟨t, ht⟩ := hunique _ hbot htop
    have hsrc0 : ((0 : Z), t) ∈ Φ.source := by rw [hsource]; exact ⟨h0U, Set.mem_univ _⟩
    have hsrcx : (Q (x, 0), (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hzU, Set.mem_univ _⟩
    have hpoints : Φ (0, t) = Φ (Q (x, 0), 0) := (hflow 0 h0U t).trans ht
    have hlabel : (0 : Z) = Q (x, 0) :=
      congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn hsrc0 hsrcx hpoints)
    have hpair : (x, (0 : B)) = (0 : A × B) :=
      Q.toOpenPartialHomeomorph.injOn (hHs hx) (hHs h0) (hlabel.symm.trans hQ0.symm)
    exact congrArg Prod.fst hpair
  · intro hx0
    subst x
    change (H (0 : A × B)).1 = 0
    rw [hH0]
    rfl

attribute [local instance 100] Classical.propDecidable in
theorem TransverseGerms.exists_cylinder_block_correction {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
        (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (K : Set Z),
      IsCompact K ∧
        K ⊆ Q.target ∩ P.target ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy D K {(0 : Z)}) ∧
            D 0 = 0 ∧
              (∀ z ∈ H.source, D (Q z) ∈ P.target) ∧
                (∀ x : A, (x, (0 : B)) ∈ H.source → ((P.symm (D (Q (x, 0)))).1 = 0 ↔ x = 0)) ∧
                  (fun z => D (Q z)) =ᶠ[𝓝 (0 : A × B)] (fun z => P (L₁ z.1, L₂ z.2)) := by
  obtain ⟨L₁, _, L₂, Dₛ, Dₜ, Kₛ, Kₜ, hKₛ, hKs, hKₜ, hKt, ⟨Iₛ⟩, ⟨Iₜ⟩, hDₛ, hDₜ, huniq, hgerm⟩ :=
    exists_block_reduction_of_native_transverse H h0 hH0 htrans hunique
  have hP0 : (0 : A × B) ∈ P.source := by
    have hh := hHt (H.map_source' h0)
    rwa [hH0] at hh
  obtain ⟨D, K, hK, _, hKU, hI, hD0, hformula⟩ :=
    exists_transported_transition_correction Q P H (hHs h0) hP0 hQzero hPzero hHs hHt hdiagram Dₛ
      Dₜ hKₛ hKₜ hKs hKt (show (0 : A × B) ∈ {p : A × B | p.2 = 0} from rfl)
      (show (0 : A × B) ∈ ({(0 : A × B)} : Set (A × B)) from rfl) Iₛ Iₜ
  have hPt (z : A × B) (hz : z ∈ H.source) : Dₜ (H (Dₛ z)) ∈ P.source :=
    hHt (hDₜ (H.map_source' (hDₛ hz)))
  have hinverse (z : A × B) (hz : z ∈ H.source) : P.symm (D (Q z)) = Dₜ (H (Dₛ z)) := by
    rw [hformula z hz]
    exact P.left_inv' (hPt z hz)
  refine ⟨L₁, L₂, D, K, hK, hKU, hI, hD0, ?_, ?_, ?_⟩
  · intro z hz
    rw [hformula z hz]
    exact P.map_source' (hPt z hz)
  · intro x hx
    rw [hinverse (x, 0) hx]
    exact huniq x hx
  · filter_upwards [H.open_source.mem_nhds h0, hgerm] with z hz hg
    rw [hformula z hz, hg]

theorem FlowSuspension.flow_preserves_base_region {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : Flow ℝ (E × ℝ)) {K U : Set E} (hKU : K ⊆ U)
    (hfix : ∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t)) {p : E × ℝ} (hp : p.1 ∈ U) (t : ℝ) :
    (F t p).1 ∈ U := by
  by_contra hout
  have hnotK : (F t p).1 ∉ K := fun h => hout (hKU h)
  have hh := hfix (F t p).1 hnotK (F t p).2 (-t)
  change F (-t) (F t p) = ((F t p).1, (F t p).2 + -t) at hh
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  have he := congrArg (fun z : E × ℝ => z.1) hh
  change p.1 = (F t p).1 at he
  exact hout (he ▸ hp)

theorem FlowSuspension.exists_native_suspension_chart {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {U : Set E}
    (hsource : Φ.source = U ×ˢ Set.univ) {D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {K : Set E}
    (hKU : K ⊆ U) {W : (E × ℝ) → E × ℝ} {F : Flow ℝ (E × ℝ)} (C : SuspensionCoordinates D K W F)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) :
    ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
      Ω.source = Φ.source ∧
        Ω.target = Φ.target ∧
          (∀ p, Ω p = Φ (C.chart p)) ∧
            (∀ y ∈ Ω.target,
                V y =
                  FlowConstruction.partialChartField Ω.symm (fun _ : E × ℝ => (0, 1)) y) ∧
              (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧ (∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) := by
  let Ω := C.chart.toPartialDiffeomorph.trans Φ
  have hΩsource : Ω.source = Φ.source := by
    ext p
    change (p ∈ (Set.univ : Set (E × ℝ)) ∧ C.chart p ∈ Φ.source) ↔ p ∈ Φ.source
    rw [hsource]
    simp only [Set.mem_univ, true_and, Set.mem_prod, and_true, C.base_iff U hKU]
  have hΩtarget : Ω.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (Set.univ : Set (E × ℝ))) ↔ y ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hpush (p : E × ℝ) (_ : p ∈ C.chart.toPartialDiffeomorph.source) :
    fderiv ℝ C.chart.toPartialDiffeomorph p (0, 1) = W (C.chart p) := by
    calc
      fderiv ℝ C.chart.toPartialDiffeomorph p (0, 1) = suspensionField C.chart (C.chart p) := by
        simp only [suspensionField, C.chart.symm_apply_apply]
        rfl
      _ = W (C.chart p) := (congrArg (fun w => w (C.chart p)) C.field_eq).symm
  refine ⟨Ω, hΩsource, hΩtarget, fun _ => rfl, ?_, ?_, ?_⟩
  · intro y hy
    have hyt : y ∈ Φ.target := hΩtarget ▸ hy
    rw [hmodel y hyt]
    exact
      (MorseCancellation.partialChartField_of_model_conjugacy C.chart.toPartialDiffeomorph Φ
          (fun _ : E × ℝ => (0, 1)) W hpush hy).symm
  · intro p hp
    change Φ (C.chart p) = Φ p
    rw [C.lower p hp]
  · intro p hp
    change Φ (C.chart p) = Φ (D p.1, p.2)
    rw [C.upper p hp]

theorem FlowSuspension.exists_full_cylinder_holonomy {E B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
    [T2Space M] [CompactSpace M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {U : Set E} (hsource : Φ.source = U ×ˢ Set.univ) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {K S : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (N : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧
        N ⊆ Φ.target ∩ f ⁻¹' Set.Ioo (c - 1) c ∧
          ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
              (∀ x, V' x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                    (∀ x ∈ Φ.target, ∀ t, G t x ∈ Φ.target) ∧
                      (∀ x ∉ Φ.target, ∀ t, G t x = H t x) ∧
                        (∀ x ∈ U, G 1 (Φ (x, 0)) = Φ (D x, 1)) ∧
                          (∀ x ∈ U ∩ S, ∀ s t : ℝ, G t (Φ (x, s)) = Φ (x, s + t)) ∧
                            ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
                              Ω.source = U ×ˢ Set.univ ∧
                                Ω.target = Φ.target ∧
                                  (∀ y ∈ Ω.target,
                                      V' y =
                                        FlowConstruction.partialChartField Ω.symm
                                          (fun _ : E × ℝ => (0, 1)) y) ∧
                                    (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
                                      (∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) ∧
                                        (∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0))) ∧
                                          (∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1)) ∧
                                            (∀ z ∈ U,
                                                ∀ t : ℝ,
                                                  t ≤ 0 → G t (Φ (z, 0)) = H t (Φ (z, 0))) ∧
                                              (∀ z ∈ U,
                                                ∀ t : ℝ,
                                                  0 ≤ t → G t (Ω (z, 1)) = H t (Ω (z, 1))) := by
  obtain ⟨W, F, hW, hWheight, -, hsupp, hF, hFend, -, hFoutside, hFfixed, ⟨Cdata⟩⟩ :=
    exists_compact_isotopy_suspension D hK I
  let C : Set (E × ℝ) := K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)
  have hC : IsCompact C := hK.prod CompactIccSpace.isCompact_Icc
  have hCsource : C ⊆ Φ.source := by
    rw [hsource]
    exact fun p hp => ⟨hKU hp.1, Set.mem_univ _⟩
  have hWfix (p : E × ℝ) (hp : p ∉ C) : W p = (0, 1) := by
    have hn : p ∉ tsupport (fun z : E × ℝ => W z - (0, 1)) := fun h => hp (hsupp h)
    have hh := image_eq_zero_of_notMem_tsupport hn
    exact sub_eq_zero.mp hh
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    exists_native_vertical_field_replacement Φ V hV hmodel hW hWheight hC hCsource hWfix
  let N := Φ '' C
  have hN : IsCompact N :=
    hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hslab (p : E × ℝ) (hp : p ∈ C) : p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hNsub : N ⊆ Φ.target ∩ f ⁻¹' Set.Ioo (c - 1) c := by
    rintro y ⟨p, hp, rfl⟩
    refine ⟨Φ.map_source' (hCsource hp), ?_⟩
    change f (Φ p) ∈ Set.Ioo (c - 1) c
    rw [hheight p (hCsource hp) (hslab p hp)]
    constructor <;> linarith [(hslab p hp).1, (hslab p hp).2]
  let R :=
    PartialChart.restrictSource Φ
      (isOpen_univ.prod (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)))
  have hRheight (p : E × ℝ) (hp : p ∈ R.source) : f (R p) = c - p.2 := hheight p hp.1 hp.2.2
  have hnegN (y : M) (hy : y ∈ N) : mvfderiv 𝓘(ℝ, B) f y (V' y) = -1 := by
    rcases hy with ⟨p, hp, rfl⟩
    have hpR : p ∈ R.source := ⟨hCsource hp, Set.mem_univ _, hslab p hp⟩
    rw [hnew (Φ p) (Φ.map_source' (hCsource hp))]
    change mvfderiv 𝓘(ℝ, B) f (R p) (FlowConstruction.partialChartField R.symm W (R p)) = -1
    rw [mvfderiv_native_height_field R hf hRheight W (R.map_source' hpR), hWheight]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : F t p ∈ Φ.source := by
    rw [hsource] at hp ⊢
    exact ⟨flow_preserves_base_region F hKU hFoutside hp.1 t, Set.mem_univ _⟩
  have hfull (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : G t (Φ p) = Φ (F t p) :=
    native_chart_flow_all_time Φ hV'₁ G hG F W hF hnew (hstay p hp) t
  have hinv := native_chart_target_invariant Φ hV'₁ G hG F W hF hnew hstay
  have hcomp := flow_complement_invariant G hinv
  obtain ⟨Ω, hΩsource, hΩtarget, hΩmap, hΩfield, hΩlower, hΩupper⟩ :=
    exists_native_suspension_chart Φ hsource hKU Cdata V' hnew
  have hΩflow (z : E) (hz : z ∈ U) (t : ℝ) : Ω (z, t) = G t (Φ (z, 0)) := by
    have h0 : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    have hC0 : Cdata.chart (z, (0 : ℝ)) = (z, 0) := Cdata.lower _ le_rfl
    have hFt : F t (z, 0) = Cdata.chart (z, t) := by
      calc
        F t (z, 0) = suspensionFlow Cdata.chart t (z, 0) :=
          congrArg (fun A : Flow ℝ (E × ℝ) => A t (z, 0)) Cdata.flow_eq
        _ = suspensionFlow Cdata.chart t (Cdata.chart (z, 0)) :=
          (congrArg (suspensionFlow Cdata.chart t) hC0.symm)
        _ = Cdata.chart (z, 0 + t) := (suspensionFlow_chart Cdata.chart t (z, 0))
        _ = Cdata.chart (z, t) := by rw [zero_add]
    rw [hΩmap]
    exact ((hfull (z, 0) h0 t).trans (congrArg Φ hFt)).symm
  have hDU : Set.MapsTo D U U :=
    SupportedDiffeomorph.mapsTo_of_fixed_outside D.toEquiv
      (fun z hz => I.endpoint_fixed_outside z (fun h => hz (hKU h)))
  have hΩsection (z : E) (hz : z ∈ U) : ∃ w ∈ U, Ω (z, 1) = Φ (w, 1) :=
    ⟨D z, hDU hz, hΩupper (z, 1) le_rfl⟩
  obtain ⟨hleftTail, hrightTail⟩ :=
    native_corrected_cylinder_tails Φ Ω hsource (hΩsource.trans hsource) (hV.of_le (by simp)) hV'₁
      hmodel hΩfield H G hH hG D hDU hΩlower hΩupper
  refine
    ⟨N, V', G, hN, hNsub, hV', hG, hzeros, ?_, hgerm, hinv, ?_, ?_, ?_, Ω, hΩsource.trans hsource,
      hΩtarget, hΩfield, hΩlower, hΩupper, hΩflow, hΩsection, hleftTail, hrightTail⟩
  · intro x hx
    by_cases hn : x ∈ N
    · rw [hnegN x hn]
      norm_num
    · rw [(hgerm x hn).self_of_nhds]
      exact hx
  · intro x hx t
    have hagree (s : ℝ) : V' (G s x) = V (G s x) :=
      (hgerm (G s x) (fun h => hcomp x hx s (hNsub h).1)).self_of_nhds
    rcases le_total 0 t with ht | ht
    · exact
        FlowCancellation.native_flow_eq_on_positive_halfline (hV.of_le (by simp)) H G hH hG
          (fun s _ => hagree s) t ht
    · exact
        FlowCancellation.native_flow_eq_on_negative_halfline (hV.of_le (by simp)) H G hH hG
          (fun s _ => hagree s) t ht
  · intro x hx
    have hp : (x, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hx, Set.mem_univ _⟩
    rw [hfull _ hp, hFend]
  · intro x hx s t
    have hp : (x, s) ∈ Φ.source := by rw [hsource]; exact ⟨hx.1, Set.mem_univ _⟩
    rw [hfull _ hp, hFfixed x hx.2 s t]

attribute [local instance 100] Classical.propDecidable in
theorem FlowSuspension.exists_native_block_holonomy {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source) (hQU : Q.target ⊆ U)
    (hPU : P.target ⊆ U) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
        (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G :
      Flow ℝ M) (Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞),
      IsCompact N ∧
        N ⊆ Φ.target ∩ f ⁻¹' Set.Ioo (c - 1) c ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                    (∀ x ∉ Φ.target, ∀ t, G t x = F t x) ∧
                      Ω.source = U ×ˢ Set.univ ∧
                        Ω.target = Φ.target ∧
                          (∀ y ∈ Ω.target,
                              W y =
                                FlowConstruction.partialChartField Ω.symm
                                  (fun _ : Z × ℝ => (0, 1)) y) ∧
                            (∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0))) ∧
                              (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
                                (∀ s t : ℝ, G t (Φ (0, s)) = Φ (0, s + t)) ∧
                                  (∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1)) ∧
                                    (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0))) ∧
                                      (∀ z ∈ U,
                                          ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1))) ∧
                                        (∀ x : A,
                                            (x, (0 : B)) ∈ H.source →
                                              ∀ y ∈ H.target,
                                                y.1 = 0 →
                                                  Ω (Q (x, 0), 1) = Φ (P y, 1) → x = 0 ∧ y = 0) ∧
                                          ∀ᶠ z in 𝓝 (0 : A × B),
                                            ∀ t : ℝ,
                                              1 ≤ t → Ω (Q z, t) = Φ (P (L₁ z.1, L₂ z.2), t) := by
  obtain ⟨L₁, L₂, D, K, hK, hKU, ⟨I⟩, hD0, hDP, huniq, hgerm⟩ :=
    TransverseGerms.exists_cylinder_block_correction Q P H h0 hH0 hQzero hPzero hHs hHt
      hdiagram htrans hunique
  have hKU' : K ⊆ U := fun z hz => hQU (hKU hz).1
  have h0U : (0 : Z) ∈ U := by
    have hh := hQU (Q.map_source' (hHs h0))
    rwa [hQzero] at hh
  obtain
    ⟨N, W, G, hN, hNsub, hW, hG, hzero, hdesc, hgerms, _, hout, _, haxis, Ω, hΩsource, hΩtarget,
      hΩfield, hΩlower, hΩupper, hΩflow, hΩsection, hleftTail, hrightTail⟩ :=
    exists_full_cylinder_holonomy Φ hsource hf hheight V hV hmodel F hF D hK hKU' I
  refine
    ⟨L₁, L₂, N, W, G, Ω, hN, hNsub, hW, hG, hzero, hdesc, hgerms, hout, hΩsource, hΩtarget,
      hΩfield, hΩflow, hΩlower, haxis 0 ⟨h0U, rfl⟩, hΩsection, hleftTail, hrightTail, ?_, ?_⟩
  · intro x hx y hy hy0 heq
    have hw : D (Q (x, 0)) ∈ P.target := hDP (x, 0) hx
    have hs₁ : (D (Q (x, 0)), (1 : ℝ)) ∈ Φ.source := by
      rw [hsource]
      exact ⟨hPU hw, Set.mem_univ _⟩
    have hs₂ : (P y, (1 : ℝ)) ∈ Φ.source := by
      rw [hsource]
      exact ⟨hPU (P.map_source' (hHt hy)), Set.mem_univ _⟩
    rw [hΩupper _ le_rfl] at heq
    have hlabel : D (Q (x, 0)) = P y :=
      congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn hs₁ hs₂ heq)
    have hinv : P.symm (D (Q (x, 0))) = y := by
      rw [hlabel]
      exact P.left_inv' (hHt hy)
    have hx0 : x = 0 := (huniq x hx).mp (by rw [hinv]; exact hy0)
    refine ⟨hx0, ?_⟩
    have hP0 : (0 : A × B) ∈ P.source := by
      have hh := hHt (H.map_source' h0)
      rwa [hH0] at hh
    have hPy : P y = 0 := by
      rw [← hlabel, hx0]
      change D (Q (0 : A × B)) = 0
      rw [hQzero, hD0]
    exact P.toOpenPartialHomeomorph.injOn (hHt hy) hP0 (hPy.trans hPzero.symm)
  · filter_upwards [hgerm] with z hz
    intro t ht
    rw [hΩupper _ ht, hz]

theorem FlowSuspension.corrected_cylinder_unique_connection {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z} (h0U : (0 : Z) ∈ U)
    (hΦsource : Φ.source = U ×ˢ Set.univ) (hΩsource : Ω.source = U ×ˢ Set.univ)
    (hΩtarget : Ω.target = Φ.target) (F G : Flow ℝ M)
    (hΦflow : ∀ z ∈ U, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (hΩflow : ∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0)))
    (hΩsection : ∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1))
    (hleft : ∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0)))
    (hright : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1)))
    (hout : ∀ x ∉ Φ.target, ∀ t, G t x = F t x) (Q P : (A × B) → Z) (hQ0 : Q 0 = 0)
    (S T : Set (A × B)) {p q : M}
    (hleftBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 0))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ S ∧ Q (x, 0) = z)
    (hrightBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 1))) Filter.atTop (𝓝 p) ↔ ∃ y ∈ T, y.1 = 0 ∧ P y = z)
    (hsection :
      ∀ x : A, (x, (0 : B)) ∈ S → ∀ y ∈ T, y.1 = 0 → Ω (Q (x, 0), 1) = Φ (P y, 1) → x = 0 ∧ y = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x) :
    ∀ x,
      Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x := by
  intro x hbot htop
  by_cases hx : x ∈ Φ.target
  · have hxΩ : x ∈ Ω.target := hΩtarget.symm ▸ hx
    let w := Ω.symm x
    have hw : w ∈ Ω.source := Ω.map_target' hxΩ
    have hwU : w.1 ∈ U := by rw [hΩsource] at hw; exact hw.1
    have hpoint : x = G w.2 (Φ (w.1, 0)) := by
      calc
        x = Ω w := (Ω.right_inv' hxΩ).symm
        _ = G w.2 (Φ (w.1, 0)) := hΩflow w.1 hwU w.2
    have hbot0 : Filter.Tendsto (fun t => G t (Φ (w.1, 0))) Filter.atBot (𝓝 q) := by
      apply (MorseCancellation.flow_time_atBot_limit_iff G w.2 (Φ (w.1, 0)) q).mp
      rwa [← hpoint]
    have htop0 : Filter.Tendsto (fun t => G t (Φ (w.1, 0))) Filter.atTop (𝓝 p) := by
      apply (MorseCancellation.flow_time_atTop_limit_iff G w.2 (Φ (w.1, 0)) p).mp
      rwa [← hpoint]
    have htop1 : Filter.Tendsto (fun t => G t (Ω (w.1, 1))) Filter.atTop (𝓝 p) := by
      rw [hΩflow w.1 hwU 1]
      exact (MorseCancellation.flow_time_atTop_limit_iff G 1 (Φ (w.1, 0)) p).mpr htop0
    have hbotF : Filter.Tendsto (fun t => F t (Φ (w.1, 0))) Filter.atBot (𝓝 q) := by
      apply hbot0.congr'
      filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
      exact hleft w.1 hwU t ht
    have htopF : Filter.Tendsto (fun t => F t (Ω (w.1, 1))) Filter.atTop (𝓝 p) := by
      apply htop1.congr'
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact hright w.1 hwU t ht
    obtain ⟨a, ha, hQa⟩ := (hleftBasin w.1 hwU).mp hbotF
    obtain ⟨v, hv, hΩv⟩ := hΩsection w.1 hwU
    rw [hΩv] at htopF
    obtain ⟨y, hy, hy0, hPy⟩ := (hrightBasin v hv).mp htopF
    have hcross : Ω (Q (a, 0), 1) = Φ (P y, 1) := by rw [hQa, hPy]; exact hΩv
    have ha0 := (hsection a ha y hy hy0 hcross).1
    have hw0 : w.1 = 0 := by
      rw [← hQa, ha0]
      exact hQ0
    refine ⟨w.2, ?_⟩
    rw [hpoint, hw0]
  · have hbotF : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) :=
      hbot.congr' (Filter.Eventually.of_forall (hout x hx))
    have htopF : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) :=
      htop.congr' (Filter.Eventually.of_forall (hout x hx))
    obtain ⟨t, ht⟩ := hold x hbotF htopF
    have hsource : (0, t) ∈ Φ.source := by rw [hΦsource]; exact ⟨h0U, Set.mem_univ _⟩
    have hxt : x ∈ Φ.target := by
      rw [← ht, ← hΦflow 0 h0U t]
      exact Φ.map_source' hsource
    exact (hx hxt).elim

theorem FlowTimeChange.exists_small_supported_scalar_germ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ}
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0) {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (K : Set E) (g : E → ℝ),
      IsCompact K ∧
        K ⊆ U ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ K ∧ g =ᶠ[𝓝 0] v ∧ g 0 = 0 ∧ ∀ x, |g x| < ε := by
  have hnear : ∀ᶠ x in 𝓝 (0 : E), x ∈ U ∧ |v x| < ε := by
    have hp : |v 0| < ε := by simpa only [hv0, abs_zero] using hε
    have hmem : ∀ᶠ x in 𝓝 (0 : E), x ∈ U := hU.mem_nhds h0U
    exact hmem.and (hv.continuous.abs.continuousAt (eventually_lt_nhds hp))
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff.mp hnear
  let β : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let K := Metric.closedBall (0 : E) β.rOut
  let g (x : E) := β x * v x
  have hKsmall {x : E} (hx : x ∈ K) : Dist.dist x 0 < r := by
    have hh : Dist.dist x 0 ≤ r / 2 := hx
    linarith
  have hKU : K ⊆ U := fun _ hx => (hrsub (hKsmall hx)).1
  have hsupp : tsupport g ⊆ K := by
    have hh := tsupport_mul_subset_left (f := fun x : E => β x) (g := v)
    rw [β.tsupport_eq] at hh
    exact hh
  have hgerm : g =ᶠ[𝓝 0] v := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) β.rIn_pos] with x hx
    change β x * v x = v x
    rw [β.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_mul]
  refine
    ⟨K, g, ProperSpace.isCompact_closedBall _ _, hKU, β.contDiff.mul hv, hsupp, hgerm,
      hgerm.eq_of_nhds.trans hv0, ?_⟩
  intro x
  by_cases hx : β x = 0
  · simpa only [g, hx, MulZeroClass.zero_mul, abs_zero] using hε
  · have hxin : x ∈ K := by
      change x ∈ Metric.closedBall (0 : E) β.rOut
      rw [← β.tsupport_eq]
      exact subset_tsupport β hx
    have hvx : |v x| < ε := (hrsub (hKsmall hxin)).2
    change |β x * v x| < ε
    rw [abs_mul, abs_of_nonneg β.nonneg]
    exact (mul_le_of_le_one_left (abs_nonneg (v x)) β.le_one).trans_lt hvx

theorem FlowTimeChange.exists_bounded_step_profile :
    ∃ (τ : ℝ → ℝ) (L : ℝ),
      ContDiff ℝ ∞ τ ∧
        0 < L ∧
          (∀ t, τ t ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ t, t ≤ 1 / 3 → τ t = 0) ∧
              (∀ t, 2 / 3 ≤ t → τ t = 1) ∧
                (∀ t, t ∉ Set.Icc (1 / 3 : ℝ) (2 / 3) → deriv τ t = 0) ∧ ∀ t, |deriv τ t| ≤ L := by
  let τ : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hτ : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hzero (t : ℝ) (ht : t ≤ 1 / 3) : τ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hone (t : ℝ) (ht : 2 / 3 ≤ t) : τ t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hout (t : ℝ) (ht : t ∉ Set.Icc (1 / 3 : ℝ) (2 / 3)) : deriv τ t = 0 := by
    by_cases hlo : t < 1 / 3
    · have hg : τ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventually_lt_nhds hlo] with s hs
        exact hzero s hs.le
      rw [hg.deriv_eq]
      exact deriv_const _ _
    · have hhi : 2 / 3 < t := by
        by_contra hn
        exact ht ⟨le_of_not_gt hlo, le_of_not_gt hn⟩
      have hg : τ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
        filter_upwards [eventually_gt_nhds hhi] with s hs
        exact hone s hs.le
      rw [hg.deriv_eq]
      exact deriv_const _ _
  have hcomp : HasCompactSupport (deriv τ) :=
    HasCompactSupport.intro
      (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (1 / 3 : ℝ) (2 / 3))) hout
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous (hτ.continuous_deriv (by simp))
  let L : ℝ := Max.max C 0 + 1
  refine ⟨τ, L, hτ, by dsimp [L]; positivity, ?_, hzero, hone, hout, ?_⟩
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro t
    have hh : |deriv τ t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t
    exact hh.trans (by dsimp [L]; linarith [le_max_left C 0])

theorem FlowTimeChange.exists_supported_phase_clock {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ (K : Set E) (g : E → ℝ) (τ : ℝ → ℝ) (D :
      Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞),
      IsCompact K ∧
        K ⊆ U ∧
          ContDiff ℝ ∞ g ∧
            tsupport g ⊆ K ∧
              g =ᶠ[𝓝 0] v ∧
                g 0 = 0 ∧
                  (∀ x, |g x| < 1 / 12) ∧
                    ContDiff ℝ ∞ τ ∧
                      (∀ t, τ t ∈ Set.Icc (0 : ℝ) 1) ∧
                        (∀ p, D p = (p.1 + τ p.1 * g p.2, p.2)) ∧
                          (∀ s, D (s, 0) = (s, 0)) ∧
                            (∀ p, p.1 ≤ 1 / 3 → D p = p) ∧
                              (∀ p, 2 / 3 ≤ p.1 → D p = (p.1 + g p.2, p.2)) ∧
                                ∀ p, 1 / 2 < fderiv ℝ (fun q => (D q).1) p (1, 0) := by
  obtain ⟨τ, L, hτ, hL, hrange, hleft, hright, -, hder⟩ := exists_bounded_step_profile
  let ε : ℝ := Min.min (1 / 12) (1 / (2 * L))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨K, g, hK, hKU, hg, hsupp, hgerm, hg0, hsmall⟩ :=
    exists_small_supported_scalar_germ hv hv0 hU h0U hε
  let u (p : ℝ × E) := τ p.1 * g p.2
  have hu : ContDiff ℝ ∞ u := (hτ.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hbound (p : ℝ × E) : |u p| ≤ ε := by
    change |τ p.1 * g p.2| ≤ ε
    rw [abs_mul, abs_of_nonneg (hrange p.1).1]
    exact (mul_le_of_le_one_left (abs_nonneg (g p.2)) (hrange p.1).2).trans (hsmall p.2).le
  have hrate (p : ℝ × E) :
    fderiv ℝ (RegularHeightCoordinates.displacedHeight u) p (1, 0) =
      1 + deriv τ p.1 * g p.2 := by
    have ha :=
      (RegularHeightCoordinates.scalar_derivative
          (RegularHeightCoordinates.contDiff_displacedHeight hu) p.1 p.2).deriv
    have hb :=
      ((hasDerivAt_id p.1).add
          ((hτ.differentiable (by simp) p.1).hasDerivAt.mul_const (g p.2))).deriv
    exact ha.symm.trans hb
  have hsmall' (p : ℝ × E) : |deriv τ p.1 * g p.2| < 1 / 2 := by
    rw [abs_mul]
    calc
      |deriv τ p.1| * |g p.2| ≤ L * |g p.2| := mul_le_mul_of_nonneg_right (hder _) (abs_nonneg _)
      _ < L * ε := (mul_lt_mul_of_pos_left (hsmall _) hL)
      _ ≤ L * (1 / (2 * L)) := (mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le)
      _ = 1 / 2 := by field_simp
  have hpositive (p : ℝ × E) :
    1 / 2 < fderiv ℝ (RegularHeightCoordinates.displacedHeight u) p (1, 0) := by
    rw [hrate]
    linarith [(abs_lt.mp (hsmall' p)).1]
  have hpos (p : ℝ × E) :
    0 < fderiv ℝ (RegularHeightCoordinates.displacedHeight u) p (1, 0) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans (hpositive p)
  have hF := RegularHeightCoordinates.contDiff_displacedHeight hu
  have hlocal :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞
      (RegularHeightCoordinates.heightMap
        (RegularHeightCoordinates.displacedHeight u)) :=
    fun p => RegularHeightCoordinates.heightMap_localDiffeomorph hF (hpos p).ne'
  let D :=
    hlocal.diffeomorphOfBijective
      ⟨RegularHeightCoordinates.heightMap_injective_of_positive hF hpos,
        RegularHeightCoordinates.heightMap_surjective_of_bounded hu.continuous ε hε.le
          hbound⟩
  have hD (p : ℝ × E) : D p = (p.1 + τ p.1 * g p.2, p.2) := rfl
  refine
    ⟨K, g, τ, D, hK, hKU, hg, hsupp, hgerm, hg0, fun x => (hsmall x).trans_le (min_le_left _ _),
      hτ, hrange, hD, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hD, hg0, MulZeroClass.mul_zero, add_zero]
  · intro p hp
    rw [hD, hleft p.1 hp, MulZeroClass.zero_mul, add_zero]
  · intro p hp
    rw [hD, hright p.1 hp, one_mul]
  · exact hpositive

def FlowTimeChange.phaseConjugatingDiffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) :
    Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
  ((ContinuousLinearEquiv.prodComm ℝ E ℝ).toDiffeomorph.trans D).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ E).toDiffeomorph

theorem FlowTimeChange.phaseClockFlow_base {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hbase : ∀ p, (D p).2 = p.2) (p : E × ℝ) (t : ℝ) :
    (FlowSuspension.suspensionFlow (phaseConjugatingDiffeomorph D) t p).1 = p.1 := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have hh := congrArg (fun w : E × ℝ => w.1) (Q.apply_symm_apply p)
  change (D (z.2, z.1)).2 = p.1 at hh
  rw [hbase] at hh
  change (D (z.2 + t, z.1)).2 = p.1
  rw [hbase]
  exact hh

theorem FlowTimeChange.phaseClockField_base_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hbase : ∀ p, (D p).2 = p.2) (p : E × ℝ) :
    (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).1 = 0 := by
  have hd :
    HasDerivAt
      (fun t => (FlowSuspension.suspensionFlow (phaseConjugatingDiffeomorph D) t p).1)
      (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).1 0 :=
    (FlowSuspension.hasDerivAt_suspensionFlow_zero (phaseConjugatingDiffeomorph D) p).fst
  have heq :
    (fun t => (FlowSuspension.suspensionFlow (phaseConjugatingDiffeomorph D) t p).1) =
      (fun _ => p.1) :=
    funext (phaseClockFlow_base D hbase p)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 p.1)

theorem FlowTimeChange.phaseClockField_time_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) (p : E × ℝ) :
    (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).2 =
      fderiv ℝ (fun q => (D q).1) ((phaseConjugatingDiffeomorph D).symm p).swap (1, 0) := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have hd :
    HasDerivAt (fun t => (FlowSuspension.suspensionFlow Q t p).2)
      (FlowSuspension.suspensionField Q p).2 0 :=
    (FlowSuspension.hasDerivAt_suspensionFlow_zero Q p).snd
  have hD : ContDiff ℝ ∞ (fun q : ℝ × E => (D q).1) := D.contMDiff.contDiff.fst
  have hc : HasDerivAt (fun t : ℝ => (z.2 + t, z.1)) ((1 : ℝ), (0 : E)) 0 :=
    ((hasDerivAt_id 0).const_add z.2).prodMk (hasDerivAt_const 0 z.1)
  have hi := (hD.differentiable (by simp) (z.2 + 0, z.1)).hasFDerivAt.comp_hasDerivAt 0 hc
  simp only [add_zero] at hi
  change
    HasDerivAt (fun t => (D (z.2 + t, z.1)).1) (FlowSuspension.suspensionField Q p).2
      0 at hd
  exact hd.unique hi

theorem FlowTimeChange.phaseClockField_time_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hpos : ∀ q, 1 / 2 < fderiv ℝ (fun p => (D p).1) q (1, 0)) (p : E × ℝ) :
    1 / 2 < (FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p).2 := by
  rw [phaseClockField_time_derivative]
  exact hpos _

theorem FlowTimeChange.phaseClockField_eq_vertical_of_translation_germ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) (p : E × ℝ) {h : ℝ}
    (hgerm :
      ∀ᶠ s in 𝓝 ((phaseConjugatingDiffeomorph D).symm p).2,
        D (s, ((phaseConjugatingDiffeomorph D).symm p).1) =
          (s + h, ((phaseConjugatingDiffeomorph D).symm p).1)) :
    FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p = (0, 1) := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have ht : Filter.Tendsto (fun t : ℝ => z.2 + t) (𝓝 0) (𝓝 z.2) := by
    have hc : Continuous (fun t : ℝ => z.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq :
    (fun t => FlowSuspension.suspensionFlow Q t p) =ᶠ[𝓝 0] (fun t => (z.1, z.2 + t + h)) :=
    by
    filter_upwards [ht.eventually hgerm] with t hts
    change ((D (z.2 + t, z.1)).2, (D (z.2 + t, z.1)).1) = _
    rw [hts]
  have hd :=
    (FlowSuspension.hasDerivAt_suspensionFlow_zero Q p).congr_of_eventuallyEq heq.symm
  exact
    hd.unique
      ((hasDerivAt_const 0 z.1).prodMk (((hasDerivAt_id (0 : ℝ)).const_add z.2).add_const h))

theorem FlowTimeChange.exists_compact_phase_field_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) {g : E → ℝ} {τ : ℝ → ℝ}
    {K : Set E} (hK : IsCompact K) (hsupp : tsupport g ⊆ K) (hsmall : ∀ x, |g x| < 1 / 12)
    (hrange : ∀ t, τ t ∈ Set.Icc (0 : ℝ) 1) (hD : ∀ p, D p = (p.1 + τ p.1 * g p.2, p.2))
    (hleft : ∀ p, p.1 ≤ 1 / 3 → D p = p) (hright : ∀ p, 2 / 3 ≤ p.1 → D p = (p.1 + g p.2, p.2)) :
    ∃ C : Set (E × ℝ),
      IsCompact C ∧
        C ⊆ K ×ˢ Set.Ioo (0 : ℝ) 1 ∧
          ∀ p ∉ C,
            FlowSuspension.suspensionField (phaseConjugatingDiffeomorph D) p = (0, 1) := by
  let Q := phaseConjugatingDiffeomorph D
  let C := Q '' (K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3))
  have hC : IsCompact C := (hK.prod CompactIccSpace.isCompact_Icc).image Q.continuous
  have hsub : C ⊆ K ×ˢ Set.Ioo (0 : ℝ) 1 := by
    rintro p ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    change ((D (t, z)).2, (D (t, z)).1) ∈ K ×ˢ Set.Ioo (0 : ℝ) 1
    rw [hD]
    have hamp : |τ t * g z| < 1 / 12 := by
      rw [abs_mul, abs_of_nonneg (hrange t).1]
      exact (mul_le_of_le_one_left (abs_nonneg (g z)) (hrange t).2).trans_lt (hsmall z)
    refine ⟨hz, ?_, ?_⟩ <;> linarith [(abs_lt.mp hamp).1, (abs_lt.mp hamp).2, ht.1, ht.2]
  refine ⟨C, hC, hsub, ?_⟩
  intro p hp
  let z := Q.symm p
  have hz : z ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) := fun hh => hp ⟨z, hh, Q.apply_symm_apply p⟩
  by_cases hbase : z.1 ∈ K
  · have htime : z.2 ∉ Set.Icc (1 / 3 : ℝ) (2 / 3) := fun ht => hz ⟨hbase, ht⟩
    by_cases hlo : z.2 < 1 / 3
    · apply phaseClockField_eq_vertical_of_translation_germ D p (h := 0)
      filter_upwards [eventually_lt_nhds hlo] with s hs
      simpa only [add_zero] using hleft (s, z.1) hs.le
    · have hhi : 2 / 3 < z.2 := by
        by_contra hn
        exact htime ⟨le_of_not_gt hlo, le_of_not_gt hn⟩
      apply phaseClockField_eq_vertical_of_translation_germ D p (h := g z.1)
      filter_upwards [eventually_gt_nhds hhi] with s hs
      exact hright (s, z.1) hs.le
  · have hg : g z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hbase (hsupp h))
    apply phaseClockField_eq_vertical_of_translation_germ D p (h := 0)
    apply Filter.Eventually.of_forall
    intro s
    rw [hD, hg, MulZeroClass.mul_zero]

structure FlowTimeChange.PhaseFlowCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : E → ℝ) (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = FlowSuspension.suspensionField chart
  flow_eq : F = FlowSuspension.suspensionFlow chart
  base : ∀ p, (chart p).1 = p.1
  lower : ∀ p, p.2 ≤ 1 / 3 → chart p = p
  upper : ∀ p, 2 / 3 ≤ p.2 → chart p = (p.1, p.2 + g p.1)
  axis : ∀ t : ℝ, chart (0, t) = (0, t)

theorem FlowTimeChange.exists_compact_phase_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ (K : Set E) (C : Set (E × ℝ)) (g : E → ℝ) (W : E × ℝ → E × ℝ) (F : Flow ℝ (E × ℝ)),
      IsCompact K ∧
        K ⊆ U ∧
          IsCompact C ∧
            C ⊆ K ×ˢ Set.Ioo (0 : ℝ) 1 ∧
              ContDiff ℝ ∞ g ∧
                tsupport g ⊆ K ∧
                  g =ᶠ[𝓝 0] v ∧
                    g 0 = 0 ∧
                      ContDiff ℝ ∞ W ∧
                        (∀ p, (W p).1 = 0) ∧
                          (∀ p, 1 / 2 < (W p).2) ∧
                            (∀ p ∉ C, W p = (0, 1)) ∧
                              (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
                                (∀ p t, (F t p).1 = p.1) ∧
                                  (∀ z t, t ≤ 1 / 3 → F t (z, 0) = (z, t)) ∧
                                    (∀ z t, 2 / 3 ≤ t → F t (z, 0) = (z, t + g z)) ∧
                                      (∀ s t : ℝ, F t (0, s) = (0, s + t)) ∧
                                        Nonempty (PhaseFlowCoordinates g W F) := by
  obtain
    ⟨K, g, τ, D, hK, hKU, hg, hsupp, hgerm, hg0, hsmall, hτ, hrange, hD, haxis, hleft, hright,
      hpos⟩ :=
    exists_supported_phase_clock hv hv0 hU h0U
  let Q := phaseConjugatingDiffeomorph D
  let W := FlowSuspension.suspensionField Q
  let F := FlowSuspension.suspensionFlow Q
  have hbase (p : ℝ × E) : (D p).2 = p.2 := by rw [hD]
  obtain ⟨C, hC, hCsub, hoff⟩ :=
    exists_compact_phase_field_support D hK hsupp hsmall hrange hD hleft hright
  have hinitial (z : E) : Q (z, 0) = (z, 0) := by
    change ((D (0, z)).2, (D (0, z)).1) = (z, 0)
    rw [hleft (0, z) (by norm_num)]
  have hinverse (z : E) : Q.symm (z, 0) = (z, 0) := by
    have hh := Q.symm_apply_apply (z, 0)
    rw [hinitial] at hh
    exact hh
  have hfromzero (z : E) (t : ℝ) : F t (z, 0) = ((D (t, z)).2, (D (t, z)).1) := by
    change Q ((Q.symm (z, 0)).1, (Q.symm (z, 0)).2 + t) = _
    rw [hinverse, zero_add]
    rfl
  have hcoords : PhaseFlowCoordinates g W F := by
    refine ⟨Q, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro p
      change (D (p.2, p.1)).2 = p.1
      rw [hD]
    · intro p hp
      change ((D (p.2, p.1)).2, (D (p.2, p.1)).1) = p
      rw [hleft (p.2, p.1) hp]
    · intro p hp
      change ((D (p.2, p.1)).2, (D (p.2, p.1)).1) = (p.1, p.2 + g p.1)
      rw [hright (p.2, p.1) hp]
    · intro t
      change ((D (t, 0)).2, (D (t, 0)).1) = (0, t)
      rw [haxis]
  refine
    ⟨K, C, g, W, F, hK, hKU, hC, hCsub, hg, hsupp, hgerm, hg0,
      FlowSuspension.contDiff_suspensionField Q, phaseClockField_base_zero D hbase,
      phaseClockField_time_positive D hpos, hoff,
      FlowSuspension.hasDerivAt_suspensionFlow Q, phaseClockFlow_base D hbase, ?_, ?_, ?_,
      ⟨hcoords⟩⟩
  · intro z t ht
    rw [hfromzero, hleft (t, z) ht]
  · intro z t ht
    rw [hfromzero, hright (t, z) ht]
  · intro s t
    have hQaxis (r : ℝ) : Q (0, r) = (0, r) := by
      change ((D (r, 0)).2, (D (r, 0)).1) = (0, r)
      rw [haxis]
    have hiaxis : Q.symm (0, s) = (0, s) := by
      have hh := Q.symm_apply_apply (0, s)
      rw [hQaxis] at hh
      exact hh
    change Q ((Q.symm (0, s)).1, (Q.symm (0, s)).2 + t) = _
    rw [hiaxis, hQaxis]

theorem FlowTimeChange.partialChartField_vertical_factor {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) (W : (E × ℝ) → E × ℝ)
    (hbase : ∀ p, (W p).1 = 0) (x : M) :
    FlowConstruction.partialChartField Φ.symm W x =
      (W (Φ.symm x)).2 •
        FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x := by
  have hw (p : E × ℝ) : W p = (W p).2 • ((0 : E), (1 : ℝ)) := by
    apply Prod.ext
    · simpa only [Prod.smul_fst, smul_zero] using hbase p
    · simp only [Prod.smul_snd, smul_eq_mul, mul_one]
  unfold FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, VectorField.mpullback_apply]
  conv_lhs => rw [hw]
  rw [map_smul, map_smul]

theorem FlowTimeChange.exists_native_positive_cylinder_rescaling {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace M] [ChartedSpace B M] [T2Space M] [IsManifold 𝓘(ℝ, B) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (W : (E × ℝ) → E × ℝ) (hW : ContDiff ℝ ∞ W) (hbase : ∀ p, (W p).1 = 0)
    (hpos : ∀ p, 0 < (W p).2) {C : Set (E × ℝ)} (hC : IsCompact C) (hCsource : C ⊆ Φ.source)
    (hfix : ∀ p ∉ C, W p = (0, 1)) :
    ∃ ρ : M → ℝ,
      ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ x, 0 < ρ x) ∧
          ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
              (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
            (∀ x ∈ Φ.target, ρ x • V x = FlowConstruction.partialChartField Φ.symm W x) ∧
              (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
                (∀ (f : M → ℝ) x,
                    mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (ρ x • V x) < 0) ∧
                  ∀ x ∉ Φ '' C, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let w (p : E × ℝ) := (W p).2
  let ρ := LocalFunctionReplacement.replace Φ (fun _ : M => 1) w
  have hw : ContDiff ℝ ∞ w := hW.snd
  have hwfix (p : E × ℝ) (hp : p ∉ C) : w p = 1 := by
    change (W p).2 = 1
    rw [hfix p hp]
  have hρ : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ ρ :=
    LocalFunctionReplacement.contMDiff_replace Φ contMDiff_const hw hC hCsource
      (fun _ _ => rfl) hwfix
  have hρpos (x : M) : 0 < ρ x := by
    change 0 < LocalFunctionReplacement.replace Φ (fun _ : M => 1) w x
    by_cases hx : x ∈ Φ.target
    · rw [LocalFunctionReplacement.replace_of_mem Φ (fun _ => 1) w hx]
      exact hpos _
    · rw [LocalFunctionReplacement.replace_of_notMem Φ (fun _ => 1) w hx]
      exact zero_lt_one
  refine ⟨ρ, hρ, hρpos, hρ.smul_section hV, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change LocalFunctionReplacement.replace Φ (fun _ : M => 1) w x • V x = _
    rw [LocalFunctionReplacement.replace_of_mem Φ (fun _ => 1) w hx, hmodel x hx,
      partialChartField_vertical_factor Φ W hbase x]
  · intro x
    exact smul_eq_zero.trans (or_iff_right (hρpos x).ne')
  · intro f x hx
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hρpos x) hx
  · intro x hx
    exact
      LocalFunctionReplacement.replace_germ_off_support Φ hC hCsource (fun _ _ => rfl)
        hwfix hx

theorem FlowSuspension.exists_native_cylinder_conjugacy {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ)
    (D : Diffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, Z × ℝ) (Z × ℝ) (Z × ℝ) ∞)
    (hbase : ∀ p, (D p).1 ∈ U ↔ p.1 ∈ U) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel :
      ∀ y ∈ Φ.target,
        V y = FlowConstruction.partialChartField Φ.symm (suspensionField D) y) :
    ∃ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞,
      Ω.source = U ×ˢ Set.univ ∧
        Ω.target = Φ.target ∧
          (∀ p, Ω p = Φ (D p)) ∧
            ∀ y ∈ Ω.target,
              V y = FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y :=
  by
  let Ω := D.toPartialDiffeomorph.trans Φ
  have hΩsource : Ω.source = U ×ˢ Set.univ := by
    ext p
    change (p ∈ (Set.univ : Set (Z × ℝ)) ∧ D p ∈ Φ.source) ↔ p ∈ U ×ˢ Set.univ
    rw [hsource]
    simp only [Set.mem_univ, true_and, Set.mem_prod, and_true, hbase]
  have hΩtarget : Ω.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (Set.univ : Set (Z × ℝ))) ↔ y ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hpush (p : Z × ℝ) (_ : p ∈ D.toPartialDiffeomorph.source) :
    fderiv ℝ D.toPartialDiffeomorph p (0, 1) = suspensionField D (D p) := by
    simp only [suspensionField, D.symm_apply_apply]
    rfl
  refine ⟨Ω, hΩsource, hΩtarget, fun _ => rfl, ?_⟩
  intro y hy
  rw [hmodel y (hΩtarget ▸ hy)]
  exact
    (MorseCancellation.partialChartField_of_model_conjugacy D.toPartialDiffeomorph Φ
        (fun _ : Z × ℝ => (0, 1)) (suspensionField D) hpush hy).symm

theorem FlowTimeChange.exists_native_phase_realization {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    [IsManifold 𝓘(ℝ, B) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {U : Set E} (hU : IsOpen U)
    (h0U : (0 : E) ∈ U) (hsource : Φ.source = U ×ˢ Set.univ)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V) {v : E → ℝ}
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0) :
    ∃ (N : Set M) (g : E → ℝ) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧
        N ⊆ Φ.target ∩ Φ '' (U ×ˢ Set.Ioo (0 : ℝ) 1) ∧
          ContDiff ℝ ∞ g ∧
            g =ᶠ[𝓝 0] v ∧
              g 0 = 0 ∧
                ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
                    (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
                  (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
                    (∀ x, V' x = 0 ↔ V x = 0) ∧
                      (∀ (f : M → ℝ) x,
                          mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
                        (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                          (∀ x,
                              Set.range (fun t => G t x) = Set.range (fun t => H t x) ∧
                                (∀ p,
                                    Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) ↔
                                      Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p)) ∧
                                  ∀ p,
                                    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
                                      Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p)) ∧
                            (∀ z ∈ U, ∀ t : ℝ, t ≤ 1 / 3 → G t (Φ (z, 0)) = Φ (z, t)) ∧
                              (∀ z ∈ U, ∀ t : ℝ, 2 / 3 ≤ t → G t (Φ (z, 0)) = Φ (z, t + g z)) ∧
                                (∀ s t : ℝ, G t (Φ (0, s)) = Φ (0, s + t)) ∧
                                  ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
                                    Ω.source = U ×ˢ Set.univ ∧
                                      Ω.target = Φ.target ∧
                                        (∀ y ∈ Ω.target,
                                            V' y =
                                              FlowConstruction.partialChartField Ω.symm
                                                (fun _ : E × ℝ => (0, 1)) y) ∧
                                          (∀ p, p.2 ≤ 1 / 3 → Ω p = Φ p) ∧
                                            (∀ p, 2 / 3 ≤ p.2 → Ω p = Φ (p.1, p.2 + g p.1)) ∧
                                              (∀ t : ℝ, Ω (0, t) = Φ (0, t)) ∧
                                                ∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0)) := by
  obtain
    ⟨K, C, g, W, F, -, hKU, hC, hCsub, hg, -, hgerm, hg0, hW, hWbase, hWpos, hWfix, hF, hFbase,
      hleft, hright, haxis, ⟨Cdata⟩⟩ :=
    exists_compact_phase_flow hv hv0 hU h0U
  have hCsource : C ⊆ Φ.source := by
    rw [hsource]
    exact fun p hp => ⟨hKU (hCsub hp).1, Set.mem_univ _⟩
  obtain ⟨ρ, hρ, hρpos, hV', hnew, hzeros, hneg, hρgerm⟩ :=
    exists_native_positive_cylinder_rescaling Φ V hV hmodel W hW hWbase
      (fun p => (by norm_num : (0 : ℝ) < 1 / 2).trans (hWpos p)) hC hCsource hWfix
  let V' : (x : M) → TangentSpace 𝓘(ℝ, B) x := fun x => ρ x • V x
  let N := Φ '' C
  have hN : IsCompact N :=
    hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hNsub : N ⊆ Φ.target ∩ Φ '' (U ×ˢ Set.Ioo (0 : ℝ) 1) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨Φ.map_source' (hCsource hp), ⟨p, ⟨hKU (hCsub hp).1, (hCsub hp).2⟩, rfl⟩⟩
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : F t p ∈ Φ.source := by
    rw [hsource] at hp ⊢
    exact ⟨(hFbase p t) ▸ hp.1, Set.mem_univ _⟩
  have hfull (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : G t (Φ p) = Φ (F t p) :=
    FlowSuspension.native_chart_flow_all_time Φ hV'₁ G hG F W hF hnew (hstay p hp) t
  have hnew' (y : M) (hy : y ∈ Φ.target) :
    V' y =
      FlowConstruction.partialChartField Φ.symm
        (FlowSuspension.suspensionField Cdata.chart) y := by
    exact
      (hnew y hy).trans
        (congrArg (fun w => FlowConstruction.partialChartField Φ.symm w y) Cdata.field_eq)
  obtain ⟨Ω, hΩsource, hΩtarget, hΩmap, hΩfield⟩ :=
    FlowSuspension.exists_native_cylinder_conjugacy Φ hsource Cdata.chart
      (fun p => by rw [Cdata.base]) V' hnew'
  have hΩlower (p : E × ℝ) (hp : p.2 ≤ 1 / 3) : Ω p = Φ p := by rw [hΩmap, Cdata.lower p hp]
  have hΩupper (p : E × ℝ) (hp : 2 / 3 ≤ p.2) : Ω p = Φ (p.1, p.2 + g p.1) := by
    rw [hΩmap, Cdata.upper p hp]
  have hΩaxis (t : ℝ) : Ω (0, t) = Φ (0, t) := by rw [hΩmap, Cdata.axis]
  have hΩflow (z : E) (hz : z ∈ U) (t : ℝ) : Ω (z, t) = G t (Φ (z, 0)) := by
    have h0 : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    have hC0 : Cdata.chart (z, (0 : ℝ)) = (z, 0) := Cdata.lower _ (by norm_num)
    have hFt : F t (z, 0) = Cdata.chart (z, t) := by
      calc
        F t (z, 0) = FlowSuspension.suspensionFlow Cdata.chart t (z, 0) :=
          congrArg (fun A : Flow ℝ (E × ℝ) => A t (z, 0)) Cdata.flow_eq
        _ = FlowSuspension.suspensionFlow Cdata.chart t (Cdata.chart (z, 0)) :=
          (congrArg (FlowSuspension.suspensionFlow Cdata.chart t) hC0.symm)
        _ = Cdata.chart (z, 0 + t) :=
          (FlowSuspension.suspensionFlow_chart Cdata.chart t (z, 0))
        _ = Cdata.chart (z, t) := by rw [zero_add]
    rw [hΩmap]
    exact ((hfull (z, 0) h0 t).trans (congrArg Φ hFt)).symm
  refine
    ⟨N, g, V', G, hN, hNsub, hg, hgerm, hg0, hV', hG, hzeros, hneg, ?_,
      native_flow_time_change_orbits hρ.continuous hρpos hV'₁ H G hH hG, ?_, ?_, ?_, Ω, hΩsource,
      hΩtarget, hΩfield, hΩlower, hΩupper, hΩaxis, hΩflow⟩
  · intro x hx
    filter_upwards [hρgerm x hx] with y hy
    simp only [V', hy, one_smul]
  · intro z hz t ht
    have hp : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    rw [hfull _ hp, hleft z t ht]
  · intro z hz t ht
    have hp : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    rw [hfull _ hp, hright z t ht]
  · intro s t
    have hp : ((0 : E), s) ∈ Φ.source := by rw [hsource]; exact ⟨h0U, Set.mem_univ _⟩
    rw [hfull _ hp, haxis]

theorem FlowTimeChange.exists_native_matched_phase_cylinder {E Z B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
    [T2Space M] [CompactSpace M] (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Ω.source = U ×ˢ Set.univ)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (hQtarget : Q.target = U)
    (hQ0 : (0 : E) ∈ Q.source) (hQzero : Q 0 = 0) (P : E → Z) {v₀ v₁ : E → ℝ}
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ y ∈ Ω.target,
        V y = FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hleft : ∀ p, p.2 ≤ 0 → Ω p = Φ p)
    (hright : ∀ᶠ z in 𝓝 (0 : E), ∀ t : ℝ, 1 ≤ t → Ω (Q z, t) = Φ (P z, t)) :
    ∃ (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M) (Ξ :
      PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞),
      IsCompact N ∧
        N ⊆ Ω.target ∧
          ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ (f : M → ℝ) x,
                    mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (W x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                    (∀ x,
                        Set.range (fun t => G t x) = Set.range (fun t => F t x) ∧
                          (∀ p,
                              Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) ∧
                            ∀ p,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
                                Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) ∧
                      Ξ.source = Q.source ×ˢ Set.univ ∧
                        Ξ.target = Ω.target ∧
                          (∀ y ∈ Ξ.target,
                              W y =
                                FlowConstruction.partialChartField Ξ.symm
                                  (fun _ : E × ℝ => (0, 1)) y) ∧
                            (∀ t : ℝ, Ξ (0, t) = Ω (0, t)) ∧
                              ∀ᶠ z in 𝓝 (0 : E),
                                (∀ t : ℝ, t ≤ -1 → Ξ (z, t) = Φ (Q z, t + v₀ z)) ∧
                                  (∀ t : ℝ, 2 ≤ t → Ξ (z, t) = Φ (P z, t + v₁ z)) := by
  obtain ⟨Ψ, hΨsource, hΨtarget, hΨmap, hΨmodel⟩ :=
    FlowSuspension.exists_native_phase_cylinder Ω hsource Q hQtarget v₀ hv₀ V hmodel
  let v : E → ℝ := fun z => v₁ z - v₀ z
  have hv : ContDiff ℝ ∞ v := hv₁.sub hv₀
  have hvzero : v 0 = 0 := by simp only [v, hv₁zero, hv₀zero, sub_self]
  obtain
    ⟨N, g, W, G, hN, hNsub, _, hgerm, _, hW, hG, hzero, hdesc, hfield, hgeometry, _, _, _, Ξ,
      hΞsource, hΞtarget, hΞmodel, hΞleft, hΞright, hΞaxis, _⟩ :=
    exists_native_phase_realization Ψ Q.open_source hQ0 hΨsource V hV hΨmodel F hF hv hvzero
  have hsmall₀ : ∀ᶠ z in 𝓝 (0 : E), v₀ z ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    hv₀.continuous.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by rw [hv₀zero]; constructor <;> norm_num))
  have hsmall₁ : ∀ᶠ z in 𝓝 (0 : E), v₁ z ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    hv₁.continuous.continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by rw [hv₁zero]; constructor <;> norm_num))
  refine
    ⟨N, W, G, Ξ, hN, fun x hx => hΨtarget ▸ (hNsub hx).1, hW, hG, hzero, hdesc, hfield, hgeometry,
      hΞsource, hΞtarget.trans hΨtarget, hΞmodel, ?_, ?_⟩
  · intro t
    rw [hΞaxis, hΨmap, hQzero, hv₀zero, add_zero]
  · filter_upwards [hgerm, hright, hsmall₀, hsmall₁] with z hg hr h₀ h₁
    constructor
    · intro t ht
      rw [hΞleft (z, t) (by dsimp; linarith), hΨmap]
      exact hleft (Q z, t + v₀ z) (by dsimp; linarith [h₀.2])
    · intro t ht
      have hclock : t + g z + v₀ z = t + v₁ z := by
        change g z = v₁ z - v₀ z at hg
        rw [hg]
        ring
      rw [hΞright (z, t) (by dsimp; linarith), hΨmap, hclock]
      exact hr (t + v₁ z) (by linarith [h₁.1])

theorem FlowSuspension.exists_unique_phase_corrected_cylinder {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source) (hQtarget : Q.target = U)
    (hPtarget : P.target = U) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
        (fun y : B => (0, y)) 0 0)
    {p q : M}
    (hleftBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 0))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ H.source ∧ Q (x, 0) = z)
    (hrightBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 1))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ H.target, y.1 = 0 ∧ P y = z)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x)
    {v₀ v₁ : (A × B) → ℝ} (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0)
    (hv₁zero : v₁ 0 = 0) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G :
      Flow ℝ M) (Ξ : PartialDiffeomorph 𝓘(ℝ, (A × B) × ℝ) 𝓘(ℝ, E) ((A × B) × ℝ) M ∞),
      IsCompact N ∧
        N ⊆ Φ.target ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                    Ξ.source = Q.source ×ˢ Set.univ ∧
                      Ξ.target = Φ.target ∧
                        (∀ y ∈ Ξ.target,
                            W y =
                              FlowConstruction.partialChartField Ξ.symm
                                (fun _ : (A × B) × ℝ => (0, 1)) y) ∧
                          (∀ t : ℝ, Ξ (0, t) = Φ (0, t)) ∧
                            (∀ x,
                                Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q) →
                                  Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) →
                                    ∃ t, G t (Φ (0, 0)) = x) ∧
                              ∀ᶠ u in 𝓝 (0 : A × B),
                                (∀ t : ℝ, t ≤ -1 → Ξ (u, t) = Φ (Q u, t + v₀ u)) ∧
                                  (∀ t : ℝ,
                                    2 ≤ t →
                                      Ξ (u, t) =
                                        Φ (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) := by
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have h0U : (0 : Z) ∈ U := by
    have hh := hQU (Q.map_source' (hHs h0))
    rwa [hQ0] at hh
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : Φ (z, t) = F t (Φ (z, 0)) := by
    simpa only [zero_add] using
      (native_vertical_cylinder_flow Φ hsource (hV.of_le (by simp)) hmodel F hF z hz 0 t).symm
  have hrelative :=
    relative_intersection_of_native_unique_connection Φ hsource h0U F hflow Q P H h0 hH0 hQ0 hHs
      hQU hdiagram hleftBasin hrightBasin hold
  obtain
    ⟨L₁, L₂, N₁, V₁, G₁, Ω, hN₁, hN₁sub, hV₁, hG₁, hzero₁, hdesc₁, hgerm₁, hout₁, hΩsource,
      hΩtarget, hΩfield, hΩflow, hΩleft, haxis₁, hΩsection, hleftTail, hrightTail, hsection,
      hΩright⟩ :=
    exists_native_block_holonomy Φ hsource hf hheight V hV hmodel F hF Q P H h0 hH0 hQ0 hP0 hHs
      hHt hQU hPU hdiagram htrans hrelative
  have hunique₁ :=
    corrected_cylinder_unique_connection Φ Ω h0U hsource hΩsource hΩtarget F G₁ hflow hΩflow
      hΩsection hleftTail hrightTail hout₁ Q P hQ0 H.source H.target hleftBasin hrightBasin
      hsection hold
  let L := L₁.prodCongr L₂
  have hv₁L : ContDiff ℝ ∞ (fun u : A × B => v₁ (L u)) := hv₁.comp L.contDiff
  have hv₁L0 : v₁ (L (0 : A × B)) = 0 := by rw [map_zero, hv₁zero]
  obtain
    ⟨N₂, W, G, Ξ, hN₂, hN₂sub, hW, hG, hzero₂, hdesc₂, hgerm₂, hgeometry, hΞsource, hΞtarget,
      hΞfield, hΞaxis, hΞmatch⟩ :=
    FlowTimeChange.exists_native_matched_phase_cylinder Φ Ω hΩsource Q hQtarget (hHs h0)
      hQ0 (fun u => P (L u)) hv₀ hv₁L hv₀zero hv₁L0 V₁ hV₁ hΩfield G₁ hG₁ hΩleft hΩright
  let N := N₁ ∪ N₂
  have hN : IsCompact N := hN₁.union hN₂
  have hNsub : N ⊆ Φ.target := by
    intro x hx
    rcases hx with hx | hx
    · exact (hN₁sub hx).1
    · exact hΩtarget ▸ hN₂sub hx
  have hkeep (x : M) (hx : x ∉ N) : ∀ᶠ y in 𝓝 x, W y = V y := by
    filter_upwards [hgerm₂ x (fun h => hx (Or.inr h)), hgerm₁ x (fun h => hx (Or.inl h))] with y
      h₂ h₁
    exact h₂.trans h₁
  have haxis (t : ℝ) : Ξ (0, t) = Φ (0, t) := by rw [hΞaxis, hΩflow 0 h0U t, haxis₁ 0 t, zero_add]
  have hunique :
    ∀ x,
      Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x := by
    intro x hbot htop
    obtain ⟨t, ht⟩ := hunique₁ x ((hgeometry x).2.2 q |>.mp hbot) ((hgeometry x).2.1 p |>.mp htop)
    have hmem : x ∈ Set.range (fun t => G₁ t (Φ (0, 0))) := ⟨t, ht⟩
    rw [← (hgeometry (Φ (0, 0))).1] at hmem
    exact hmem
  exact
    ⟨L₁, L₂, N, W, G, Ξ, hN, hNsub, hW, hG, fun x => (hzero₂ x).trans (hzero₁ x), fun x hx =>
      hdesc₂ f x (hdesc₁ x hx), hkeep, hΞsource, hΞtarget.trans hΩtarget, hΞfield, haxis, hunique,
      hΞmatch⟩

theorem MorseCancellation.native_endpoint_phase_through_box {E Z M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΦmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (hAmodel :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c r : ℝ}
    (hbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source) (z : Fin m → ℝ) {q : Z}
    (hq : q ∈ U) {T v : ℝ}
    (hstart : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hmatch : Φ (cubicFlowCylinder σ a (z, T)) = A (q, T + v)) :
    ∀ t : ℝ,
      cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
        Φ (cubicFlowCylinder σ a (z, t)) = A (q, t + v) := by
  intro t ht
  calc
    Φ (cubicFlowCylinder σ a (z, t)) = F (t - T) (Φ (cubicFlowCylinder σ a (z, T))) :=
      (native_cubic_flow_between_box_points σ ha Φ hV hΦmodel F hF hbox z hstart ht).symm
    _ = F (t - T) (A (q, T + v)) := (congrArg (F (t - T)) hmatch)
    _ = A (q, (T + v) + (t - T)) :=
      (FlowSuspension.native_vertical_cylinder_flow A hAsource hV hAmodel F hF q hq (T + v)
        (t - T))
    _ = A (q, t + v) := congrArg (fun s : ℝ => A (q, s)) (by ring)

theorem MorseCancellation.matched_cubic_time_formulas {E Z B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, B) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (e : (Fin m → ℝ) ≃L[ℝ] E)
    (L : E ≃L[ℝ] E) (Q P : E → Z) (v₀ v₁ : E → ℝ) {Oq Op : Set E} (hOq : IsOpen Oq)
    (hOp : IsOpen Op) (h0q : (0 : E) ∈ Oq) (h0p : (0 : E) ∈ Op) (hQU : ∀ u ∈ Oq, Q u ∈ U)
    (hPU : ∀ u ∈ Op, P u ∈ U) {Rq Rp Tq Tp : ℝ}
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Oq, cubicFlowCylinder σ a (e.symm u, Tq) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ Op, cubicFlowCylinder σ a (e.symm u, Tp) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq : ∀ u ∈ Oq, Φq (cubicFlowCylinder σ a (e.symm u, Tq)) = A (Q u, Tq + v₀ u))
    (hphasep : ∀ u ∈ Op, Φp (cubicFlowCylinder σ a (e.symm u, Tp)) = A (P u, Tp + v₁ u))
    (Ψq Ψp Φm : Model m → M) (Ξ : E × ℝ → M) (hnewq : ∀ p, Ψq p = Φq p)
    (hnewp :
      ∀ z t, Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)))
    (hmid : ∀ z t, Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t)) {rq rp : ℝ}
    (hcontrolq :
      Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hcontrolp :
      ∀ z t,
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
          cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hleft : ∀ᶠ u in 𝓝 (0 : E), ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright : ∀ᶠ u in 𝓝 (0 : E), ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L u), t + v₁ (L u))) :
    (∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          t ≤ -1 →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
              Ψq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) ∧
      (∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          2 ≤ t →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
              Ψp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) := by
  have he : Filter.Tendsto e (𝓝 (0 : Fin m → ℝ)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using e.continuous.tendsto 0
  have heL : Filter.Tendsto (fun z : Fin m → ℝ => L (e z)) (𝓝 0) (𝓝 (0 : E)) := by
    have hh : Filter.Tendsto L (𝓝 (0 : E)) (𝓝 (0 : E)) := by
      simpa only [map_zero] using L.continuous.tendsto 0
    exact hh.comp he
  constructor
  · filter_upwards [he.eventually hleft, he.eventually (hOq.mem_nhds h0q)] with z hformula hz
    intro t ht hp
    have hstart : cubicFlowCylinder σ a (z, Tq) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq := by
      simpa only [e.symm_apply_apply] using hsliceq (e z) hz
    have hphase : Φq (cubicFlowCylinder σ a (z, Tq)) = A (Q (e z), Tq + v₀ (e z)) := by
      simpa only [e.symm_apply_apply] using hphaseq (e z) hz
    calc
      Ψq (cubicFlowCylinder σ a (z, t)) = Φq (cubicFlowCylinder σ a (z, t)) := hnewq _
      _ = A (Q (e z), t + v₀ (e z)) :=
        (native_endpoint_phase_through_box σ ha Φq A hAsource hV hqfield hAfield F hF hboxq z
          (hQU (e z) hz) hstart hphase t (hcontrolq hp))
      _ = Ξ (e z, t) := (hformula t ht).symm
      _ = Φm (cubicFlowCylinder σ a (z, t)) := (hmid z t).symm
  · filter_upwards [he.eventually hright, heL.eventually (hOp.mem_nhds h0p)] with z hformula hz
    intro t ht hp
    calc
      Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) :=
        hnewp z t
      _ = A (P (L (e z)), t + v₁ (L (e z))) :=
        (native_endpoint_phase_through_box σ ha Φp A hAsource hV hpfield hAfield F hF hboxp
          (e.symm (L (e z))) (hPU (L (e z)) hz) (hslicep (L (e z)) hz) (hphasep (L (e z)) hz) t
          (hcontrolp z t hp))
      _ = Ξ (e z, t) := (hformula t ht).symm
      _ = Φm (cubicFlowCylinder σ a (z, t)) := (hmid z t).symm

theorem FieldChartGluing.partialChartField_eq_of_forward_germ {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (W : D → D) {p : D} (hpΦ : p ∈ Φ.source) (hpΨ : p ∈ Ψ.source) (heq : (Φ : D → M) =ᶠ[𝓝 p] Ψ) :
    FlowConstruction.partialChartField Φ.symm W (Φ p) =
      FlowConstruction.partialChartField Ψ.symm W (Φ p) := by
  have hval : Φ p = Ψ p := heq.eq_of_nhds
  have hyΨ : Φ p ∈ Ψ.target := hval.symm ▸ Ψ.map_source' hpΨ
  have hiΦ : Φ.symm (Φ p) = p := Φ.left_inv' hpΦ
  have hiΨ : Ψ.symm (Φ p) = p := by rw [hval]; exact Ψ.left_inv' hpΨ
  rw [FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W (Φ.map_source' hpΦ),
    FlowConstruction.partialChartField_eq_mfderiv_symm Ψ.symm W hyΨ]
  change
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) Φ (Φ.symm (Φ p))
        ((NormedSpace.fromTangentSpace (Φ.symm (Φ p))).symm (W (Φ.symm (Φ p)))) =
      mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) Ψ (Ψ.symm (Φ p))
        ((NormedSpace.fromTangentSpace (Ψ.symm (Φ p))).symm (W (Ψ.symm (Φ p))))
  rw [hiΦ, hiΨ, heq.mfderiv_eq]
  rfl

theorem FieldChartGluing.isLocalDiffeomorphAt_of_chart_germ {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {f : D → M} {p : D} (hp : p ∈ Φ.source) (heq : f =ᶠ[𝓝 p] Φ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f p := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp heq
  let Ψ := PartialChart.restrictSource Φ hU
  exact ⟨Ψ, ⟨hp, hpU⟩, fun x hx => hUsub hx.2⟩

attribute [local instance 100] Classical.propDecidable in
theorem FieldChartGluing.exists_native_field_chart_near_compact {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M] (f : D → M) (W : D → D)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) {K : Set D} (hK : IsCompact K) (hinj : Set.InjOn f K)
    (hlocal :
      ∀ p ∈ K,
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
          p ∈ Φ.source ∧
            f =ᶠ[𝓝 p] Φ ∧
              ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
      K ⊆ Φ.source ∧
        (∀ p, Φ p = f p) ∧
          ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y := by
  let U : Set D :=
    {p |
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
        p ∈ Φ.source ∧
          f =ᶠ[𝓝 p] Φ ∧ ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨Ψ, hp, heq, hfield⟩
    filter_upwards [Ψ.open_source.mem_nhds hp, heq.eventuallyEq_nhds] with q hq hqeq
    exact ⟨Ψ, hq, hqeq, hfield⟩
  have hloc (p : D) (hp : p ∈ K) : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f p := by
    obtain ⟨Ψ, hpΨ, heq, _⟩ := hlocal p hp
    exact isLocalDiffeomorphAt_of_chart_germ Ψ hpΨ heq
  obtain ⟨Φ, hKΦ, hΦU, hmap⟩ :=
    exists_partialDiffeomorph_near_compact hK hinj hloc hU hlocal
  refine ⟨Φ, hKΦ, fun p => congrFun hmap p, ?_⟩
  intro y hy
  have hp : Φ.symm y ∈ Φ.source := Φ.map_target' hy
  obtain ⟨Ψ, hpΨ, heq, hfield⟩ := hΦU hp
  have hΦeq : (Φ : D → M) =ᶠ[𝓝 (Φ.symm y)] Ψ := by rw [hmap]; exact heq
  have hi : Φ (Φ.symm y) = y := Φ.right_inv' hy
  have hΨval : Ψ (Φ.symm y) = y := hΦeq.eq_of_nhds.symm.trans hi
  have hyΨ : y ∈ Ψ.target := hΨval ▸ Ψ.map_source' hpΨ
  have hsame := partialChartField_eq_of_forward_germ Φ Ψ W hp hpΨ hΦeq
  rw [hi] at hsame
  exact (hfield y hyΨ).trans hsame.symm

theorem FieldChartGluing.exists_controlled_field_germ_chart {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (W : D → D) (V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) {c : D}
    (hc : c ∈ Φ.source) (hfield : ∀ᶠ y in 𝓝 (Φ c), V' y = V y) {O : Set D} (hO : IsOpen O)
    (hcO : c ∈ O) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (r : ℝ),
      0 < r ∧
        Metric.closedBall c r ⊆ Ψ.source ∧
          Ψ.source ⊆ Φ.source ∩ O ∧
            Ψ.target ⊆ Φ.target ∧
              (∀ z, Ψ z = Φ z) ∧
                ∀ y ∈ Ψ.target, V' y = FlowConstruction.partialChartField Ψ.symm W y := by
  obtain ⟨U, hUsub, hU, hcenter⟩ := mem_nhds_iff.mp hfield
  let R := PartialChart.restrictTarget Φ hU
  let Ψ := PartialChart.restrictSource R hO
  have hcΨ : c ∈ Ψ.source := by
    change (c ∈ Φ.source ∧ Φ c ∈ U) ∧ c ∈ O
    exact ⟨⟨hc, hcenter⟩, hcO⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds hcΨ)
  refine ⟨Ψ, r, hr, hball, fun z hz => ⟨hz.1.1, hz.2⟩, fun y hy => hy.1.1, fun _ => rfl, ?_⟩
  intro y hy
  exact (hUsub hy.1.2).trans (hmodel y hy.1.1)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.signed_split_transverse_rate {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (z : Fin m → ℝ) :
    MorseHandle.splitCoordinates σ (fun i => σ i * z i) =
      ((-1 : ℝ) • (MorseHandle.splitCoordinates σ z).1,
        (1 : ℝ) • (MorseHandle.splitCoordinates σ z).2) := by
  apply Prod.ext
  · ext i
    change σ i.1 * z i.1 = (-1 : ℝ) * z i.1
    simp [i.2]
  · ext i
    change σ i.1 * z i.1 = (1 : ℝ) * z i.1
    simp [(hσ i.1).resolve_left i.2]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.signed_split_transverse_exponential {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (t : ℝ) (z : Fin m → ℝ) :
    MorseHandle.splitCoordinates σ (fun i => Real.exp (-σ i * t) * z i) =
      (Real.exp t • (MorseHandle.splitCoordinates σ z).1,
        Real.exp (-t) • (MorseHandle.splitCoordinates σ z).2) := by
  apply Prod.ext
  · ext i
    change Real.exp (-σ i.1 * t) * z i.1 = Real.exp t * z i.1
    simp [i.2]
  · ext i
    change Real.exp (-σ i.1 * t) * z i.1 = Real.exp (-t) * z i.1
    simp [(hσ i.1).resolve_left i.2]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.signed_block_change_cubic_cylinder {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (P : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (S : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ) (a t : ℝ)
    (z : Fin m → ℝ) :
    transverseFieldChange (splitTransverseChange (MorseHandle.splitCoordinates σ) P S)
        (cubicFlowCylinder σ a (z, t)) =
      cubicFlowCylinder σ a
        (splitTransverseChange (MorseHandle.splitCoordinates σ) P S z, t) := by
  apply Prod.ext
  · rfl
  · exact
      splitTransverseChange_commutes (fun i => Real.exp (-σ i * t))
        (MorseHandle.splitCoordinates σ) (Real.exp t) (Real.exp (-t))
        (signed_split_transverse_exponential σ hσ t) P S z

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_signed_block_changed_cubic_chart {m : ℕ} {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (P : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (S : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (τ : ℝ)
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ τ y) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        (∀ s : ℝ, ((s, (0 : Fin m → ℝ)) ∈ Ψ.source ↔ (s, 0) ∈ Φ.source)) ∧
          (∀ s : ℝ, Ψ (s, 0) = Φ (s, 0)) ∧
            (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ τ y) ∧
              ∀ (a t : ℝ)
                (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
                Ψ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, t)) =
                  Φ
                    (cubicFlowCylinder σ a
                      ((MorseHandle.splitCoordinates σ).symm (P u.1, S u.2), t)) := by
  let T := splitTransverseChange (MorseHandle.splitCoordinates σ) P S
  let D := transverseFieldChange T
  let Ψ := D.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have htarget : Ψ.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (Set.univ : Set (Model m))) ↔ y ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hDaxis (s : ℝ) : D (s, 0) = (s, 0) := by
    change (s, T 0) = (s, 0)
    rw [map_zero]
  have hpush (p : Model m) (_ : p ∈ D.toDiffeomorph.toPartialDiffeomorph.source) :
    fderiv ℝ D.toDiffeomorph.toPartialDiffeomorph p (cubicDescent σ τ p) =
      cubicDescent σ τ (D p) := by
    change fderiv ℝ D p (cubicDescent σ τ p) = _
    rw [D.fderiv]
    exact
      transverseFieldChange_cubicDescent σ T
        (splitTransverseChange_commutes σ (MorseHandle.splitCoordinates σ) (-1) 1
          (signed_split_transverse_rate σ hσ) P S)
        τ p
  refine ⟨Ψ, htarget, ?_, ?_, ?_, ?_⟩
  · intro s
    change ((s, (0 : Fin m → ℝ)) ∈ Set.univ ∧ D (s, 0) ∈ Φ.source) ↔ (s, 0) ∈ Φ.source
    rw [hDaxis]
    simp only [Set.mem_univ, true_and]
  · intro s
    change Φ (D (s, 0)) = Φ (s, 0)
    rw [hDaxis]
  · intro y hy
    rw [hmodel y (htarget ▸ hy)]
    exact
      (partialChartField_of_model_conjugacy D.toDiffeomorph.toPartialDiffeomorph Φ
          (cubicDescent σ τ) (cubicDescent σ τ) hpush hy).symm
  · intro a t u
    change Φ (D (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, t))) = _
    rw [signed_block_change_cubic_cylinder σ hσ P S]
    have hT :
      T ((MorseHandle.splitCoordinates σ).symm u) =
        (MorseHandle.splitCoordinates σ).symm (P u.1, S u.2) := by
      simp only [T, splitTransverseChange, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply]
    change Φ (cubicFlowCylinder σ a (T ((MorseHandle.splitCoordinates σ).symm u), t)) = _
    rw [hT]

theorem MorseCancellation.exists_native_regular_cubic_field_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ Set.univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ι : (Fin m → ℝ) → M)
    (hformula : ∀ p ∈ Φ.source, Φ p = F p.2 (ι p.1)) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
          (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (ι 0)) ∧
            (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
              Ψ.source ⊆ Set.Ioo (-a) a ×ˢ Set.univ ∧ ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  let C := cubicFlowCylinderChart σ ha
  let Ψ := C.symm.trans Φ
  have htarget : Ψ.target = Φ.target := by
    ext x
    change x ∈ Φ.target ∧ Φ.symm x ∈ Set.univ ↔ x ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hcompose (p : (Fin m → ℝ) × ℝ) : Ψ (C p) = Φ p := by
    change Φ (C.symm (C p)) = Φ p
    have hh : C.symm (C p) = p := C.left_inv' (Set.mem_univ p)
    exact congrArg Φ hh
  have hopenaxis : Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change (s, (0 : Fin m → ℝ)) ∈ C.target ∧ C.symm (s, 0) ∈ Φ.source
    refine ⟨⟨hs, Set.mem_univ _⟩, ?_⟩
    rw [hsource]
    change (fun i => Real.exp (σ i * cubicAxisClock a s) * (0 : Fin m → ℝ) i) ∈ U ∧ _
    simp only [Pi.zero_apply, MulZeroClass.mul_zero]
    exact ⟨h0, Set.mem_univ _⟩
  refine ⟨Ψ, htarget, hopenaxis, ?_, ?_, fun _ hp => hp.1, hcompose⟩
  · intro s
    change Φ (cubicFlowCylinderInverse σ a (s, 0)) = _
    have hsΦ : cubicFlowCylinderInverse σ a (s, 0) ∈ Φ.source := by
      rw [hsource]
      simp only [cubicFlowCylinderInverse, Pi.zero_apply, MulZeroClass.mul_zero]
      exact ⟨h0, Set.mem_univ _⟩
    rw [hformula _ hsΦ]
    simp only [cubicFlowCylinderInverse, Pi.zero_apply, MulZeroClass.mul_zero]
    rfl
  · intro x hx
    have hxΦ : x ∈ Φ.target := htarget ▸ hx
    let p := Φ.symm x
    have hp : p ∈ Φ.source := Φ.map_target' hxΦ
    have hpU : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
    have hpC : C p ∈ Ψ.source := by
      change C p ∈ C.target ∧ C.symm (C p) ∈ Φ.source
      have hh : C.symm (C p) = p := C.left_inv' (Set.mem_univ p)
      exact ⟨C.map_source' (Set.mem_univ p), hh.symm ▸ hp⟩
    let α : ℝ → Model m := fun s => C (p.1, s)
    have hα : HasDerivAt α (cubicDescent σ (-(a ^ 2)) (α p.2)) p.2 :=
      hasDerivAt_cubicFlowCylinder σ a p.1 p.2
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Ψ.symm
        (cubicDescent σ (-(a ^ 2))) hα hpC
    have hcurveeq : Ψ.symm.symm ∘ α = fun t => F t (ι p.1) := by
      funext t
      have hpt : (p.1, t) ∈ Φ.source := by rw [hsource]; exact ⟨hpU, Set.mem_univ _⟩
      exact (hcompose (p.1, t)).trans (hformula (p.1, t) hpt)
    rw [hcurveeq] at hd
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (FlowConstruction.partialChartField Ψ.symm (cubicDescent σ (-(a ^ 2)))
            (Ψ (C p)))) at hd
    rw [hcompose p, hformula p hp] at hd
    have hh := (hF (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
    have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) => L 1) hh
    simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
    have hpx : F p.2 (ι p.1) = x := (hformula p hp).symm.trans (Φ.right_inv' hxΦ)
    rw [hpx] at hv
    exact hv

theorem MorseCancellation.exists_regular_cubic_chart_of_native_vertical_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ Set.univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ y ∈ Φ.target,
        V y =
          FlowConstruction.partialChartField Φ.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
          (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (Φ (0, 0))) ∧
            (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
              Ψ.source ⊆ Set.Ioo (-a) a ×ˢ Set.univ ∧ ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  apply exists_native_regular_cubic_field_chart σ ha Φ hsource h0 V F hF (fun z => Φ (z, 0))
  intro p hp
  have hz : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
  simpa only [zero_add] using
    (FlowSuspension.native_vertical_cylinder_flow Φ hsource hV hmodel F hF p.1 hz 0
        p.2).symm

def FieldChartGluing.threeChartMap {Z M : Type*} (f₀ fₘ f₁ : (ℝ × Z) → M) (a b : ℝ)
    (p : ℝ × Z) : M :=
  if p.1 ≤ a then f₀ p else if b ≤ p.1 then f₁ p else fₘ p

theorem FieldChartGluing.threeChartMap_left_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} {p : ℝ × Z} (hp : p.1 < a) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₀ := by
  filter_upwards [continuousAt_fst.eventually (eventually_lt_nhds hp)] with q hq
  simp only [threeChartMap, if_pos hq.le]

theorem FieldChartGluing.threeChartMap_middle_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} {p : ℝ × Z} (ha : a < p.1) (hb : p.1 < b) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] fₘ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds ha),
    continuousAt_fst.eventually (eventually_lt_nhds hb)] with q hqa hqb
  simp only [threeChartMap, if_neg (not_le_of_gt hqa), if_neg (not_le_of_gt hqb)]

theorem FieldChartGluing.threeChartMap_right_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) {p : ℝ × Z} (hp : b < p.1) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₁ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds hp)] with q hq
  simp only [threeChartMap, if_neg (not_le_of_gt (hab.trans hq)), if_pos hq.le]

theorem FieldChartGluing.threeChartMap_left_closed_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) (heq : f₀ =ᶠ[𝓝 (a, (0 : Z))] fₘ)
    {s : ℝ} (hs : s ≤ a) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₀ := by
  rcases hs.lt_or_eq with hs | hs
  · exact threeChartMap_left_germ f₀ fₘ f₁ hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_lt_nhds hab)] with p hp hpb
    by_cases hpa : p.1 ≤ a
    · simp only [threeChartMap, if_pos hpa]
    · simp only [threeChartMap, if_neg hpa, if_neg (not_le_of_gt hpb)]
      exact hp.symm

theorem FieldChartGluing.threeChartMap_right_closed_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) (heq : f₁ =ᶠ[𝓝 (b, (0 : Z))] fₘ)
    {s : ℝ} (hs : b ≤ s) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₁ := by
  rcases hs.eq_or_lt with hs | hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_gt_nhds hab)] with p hp hpa
    by_cases hpb : b ≤ p.1
    · simp only [threeChartMap, if_neg (not_le_of_gt hpa), if_pos hpb]
    · simp only [threeChartMap, if_neg (not_le_of_gt hpa), if_neg hpb]
      exact hp.symm
  · exact threeChartMap_right_germ f₀ fₘ f₁ hab hs

theorem FieldChartGluing.exists_glued_three_native_field_charts {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) (W : (ℝ × Z) → ℝ × Z)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hsource₀ : ∀ s ∈ Set.Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Set.Ioo a b, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Set.Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ) (γ : ℝ → M)
    (hinj : Set.InjOn γ (Set.Icc l r)) (haxis₀ : ∀ s ∈ Set.Icc l a, Φ₀ (s, 0) = γ s)
    (haxisₘ : ∀ s ∈ Set.Ioo a b, Φₘ (s, 0) = γ s) (haxis₁ : ∀ s ∈ Set.Icc b r, Φ₁ (s, 0) = γ s) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Set.Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        (∀ s ∈ Set.Icc l r, Φ (s, 0) = γ s) ∧
          (∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) ∧
            ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
              ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let f := threeChartMap Φ₀ Φₘ Φ₁ a b
  have haxis (s : ℝ) (hs : s ∈ Set.Icc l r) : f (s, 0) = γ s := by
    by_cases hsa : s ≤ a
    · exact
        (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa).eq_of_nhds.trans
          (haxis₀ s ⟨hs.1, hsa⟩)
    · by_cases hbs : b ≤ s
      · exact
          (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs).eq_of_nhds.trans
            (haxis₁ s ⟨hbs, hs.2⟩)
      · exact
          (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa)
                (lt_of_not_ge hbs)).eq_of_nhds.trans
            (haxisₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩)
  have hfinj : Set.InjOn f (Set.Icc l r ×ˢ {(0 : Z)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [haxis s hs, haxis t ht] at heq
    exact congrArg (fun s : ℝ => (s, (0 : Z))) (hinj hs ht heq)
  have hlocal :
    ∀ p ∈ Set.Icc l r ×ˢ {(0 : Z)},
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
        p ∈ Ψ.source ∧
          f =ᶠ[𝓝 p] Ψ ∧
            ∀ y ∈ Ψ.target, V y = FlowConstruction.partialChartField Ψ.symm W y := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsa : s ≤ a
    · exact
        ⟨Φ₀, hsource₀ s ⟨hs.1, hsa⟩, threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa,
          hfield₀⟩
    · by_cases hbs : b ≤ s
      · exact
          ⟨Φ₁, hsource₁ s ⟨hbs, hs.2⟩, threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs,
            hfield₁⟩
      · exact
          ⟨Φₘ, hsourceₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩,
            threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa) (lt_of_not_ge hbs), hfieldₘ⟩
  obtain ⟨Φ, hsource, hmap, hfield⟩ :=
    exists_native_field_chart_near_compact f W V
      (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hfinj hlocal
  refine ⟨Φ, hsource, fun s hs => (hmap (s, 0)).trans (haxis s hs), hfield, ?_, ?_⟩
  · filter_upwards [threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hla] with p hp
    exact (hmap p).trans hp
  · filter_upwards [threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbr] with p hp
    exact (hmap p).trans hp

theorem FieldChartGluing.injective_closed_axis_of_regular_chart {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) {l r : ℝ} (γ : ℝ → M)
    (hsource : ∀ s ∈ Set.Ioo l r, (s, (0 : Z)) ∈ Φ.source)
    (hregular : ∀ s ∈ Set.Ioo l r, γ s = Φ (s, 0)) (hleft : γ l ∉ Φ.target)
    (hright : γ r ∉ Φ.target) (hne : γ l ≠ γ r) : Set.InjOn γ (Set.Icc l r) := by
  have htarget (s : ℝ) (hs : s ∈ Set.Ioo l r) : γ s ∈ Φ.target := by
    rw [hregular s hs]
    exact Φ.map_source' (hsource s hs)
  have hleftOnly (s : ℝ) (hs : s ∈ Set.Icc l r) (heq : γ s = γ l) : s = l := by
    by_cases hsl : s = l
    · exact hsl
    by_cases hsr : s = r
    · subst s
      exact (hne heq.symm).elim
    have hi : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hleft (heq ▸ htarget s hi)).elim
  have hrightOnly (s : ℝ) (hs : s ∈ Set.Icc l r) (heq : γ s = γ r) : s = r := by
    by_cases hsr : s = r
    · exact hsr
    by_cases hsl : s = l
    · subst s
      exact (hne heq).elim
    have hi : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hright (heq ▸ htarget s hi)).elim
  intro s hs t ht heq
  by_cases hsl : s = l
  · subst s
    exact (hleftOnly t ht heq.symm).symm
  by_cases hsr : s = r
  · subst s
    exact (hrightOnly t ht heq.symm).symm
  by_cases htl : t = l
  · subst t
    exact hleftOnly s hs heq
  by_cases htr : t = r
  · subst t
    exact hrightOnly s hs heq
  have hs' : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
  have ht' : t ∈ Set.Ioo l r := ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
  rw [hregular s hs', hregular t ht'] at heq
  exact congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn (hsource s hs') (hsource t ht') heq)

theorem FieldChartGluing.exists_closed_axis_native_field_chart {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) (W : (ℝ × Z) → ℝ × Z)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l < a) (hab : a < b) (hbr : b < r)
    (hsource₀ : ∀ s ∈ Set.Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Set.Ioo l r, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Set.Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ)
    (haxis₀ : ∀ s ∈ Set.Ioc l a, Φ₀ (s, 0) = Φₘ (s, 0))
    (haxis₁ : ∀ s ∈ Set.Ico b r, Φ₁ (s, 0) = Φₘ (s, 0)) (hleft : Φ₀ (l, 0) ∉ Φₘ.target)
    (hright : Φ₁ (r, 0) ∉ Φₘ.target) (hne : Φ₀ (l, 0) ≠ Φ₁ (r, 0)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Set.Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) ∧
          Φ (l, 0) = Φ₀ (l, 0) ∧
            Φ (r, 0) = Φ₁ (r, 0) ∧
              (∀ s ∈ Set.Ioo l r, Φ (s, 0) = Φₘ (s, 0)) ∧
                ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
                  ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let γ : ℝ → M := fun s => threeChartMap Φ₀ Φₘ Φ₁ a b (s, 0)
  have hγ₀ (s : ℝ) (hs : s ≤ a) : γ s = Φ₀ (s, 0) :=
    (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hs).eq_of_nhds
  have hγ₁ (s : ℝ) (hs : b ≤ s) : γ s = Φ₁ (s, 0) :=
    (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hs).eq_of_nhds
  have hγₘ (s : ℝ) (hs : s ∈ Set.Ioo a b) : γ s = Φₘ (s, 0) :=
    (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ hs.1 hs.2).eq_of_nhds
  have hregular (s : ℝ) (hs : s ∈ Set.Ioo l r) : γ s = Φₘ (s, 0) := by
    by_cases hsa : s ≤ a
    · exact (hγ₀ s hsa).trans (haxis₀ s ⟨hs.1, hsa⟩)
    by_cases hbs : b ≤ s
    · exact (hγ₁ s hbs).trans (haxis₁ s ⟨hbs, hs.2⟩)
    exact hγₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩
  have hinj : Set.InjOn γ (Set.Icc l r) :=
    injective_closed_axis_of_regular_chart Φₘ γ hsourceₘ hregular
      (by rw [hγ₀ l hla.le]; exact hleft) (by rw [hγ₁ r hbr.le]; exact hright)
      (by rw [hγ₀ l hla.le, hγ₁ r hbr.le]; exact hne)
  obtain ⟨Φ, hsource, haxis, hfield, hg₀, hg₁⟩ :=
    exists_glued_three_native_field_charts Φ₀ Φₘ Φ₁ W V hfield₀ hfieldₘ hfield₁ hla.le hab hbr.le
      hsource₀ (fun s hs => hsourceₘ s ⟨hla.trans hs.1, hs.2.trans hbr⟩) hsource₁ hgerm₀ hgerm₁ γ
      hinj (fun s hs => (hγ₀ s hs.2).symm) (fun s hs => (hγₘ s hs).symm)
      (fun s hs => (hγ₁ s hs.1).symm)
  have hlr : l ≤ r := (hla.trans (hab.trans hbr)).le
  refine
    ⟨Φ, hsource, hfield, (haxis l ⟨le_rfl, hlr⟩).trans (hγ₀ l hla.le),
      (haxis r ⟨hlr, le_rfl⟩).trans (hγ₁ r hbr.le), ?_, hg₀, hg₁⟩
  exact fun s hs => (haxis s ⟨hs.1.le, hs.2.le⟩).trans (hregular s hs)

theorem MorseCancellation.exists_cubic_spatial_overlap_germ {m : ℕ} {M : Type*} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (Φ Ψ : Model m → M) {c r : ℝ} (hr : 0 < r) {l : Filter ℝ} [Filter.NeBot l]
    (hlim : Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) l (𝓝 (c, (0 : Fin m → ℝ))))
    {J : Set ℝ} (hJ : IsOpen J) (hJl : J ∈ l)
    (hmatch :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t ∈ J,
          cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
            Φ (cubicFlowCylinder σ a (z, t)) = Ψ (cubicFlowCylinder σ a (z, t))) :
    ∃ T ∈ J,
      cubicFlowCylinder σ a (0, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r ∧
        Φ =ᶠ[𝓝 (cubicFlowCylinder σ a (0, T))] Ψ := by
  have hnear : ∀ᶠ t in l, cubicFlowCylinder σ a (0, t) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  have hJevent : ∀ᶠ t in l, t ∈ J := hJl
  obtain ⟨T, hTJ, hTball⟩ := (hJevent.and hnear).exists
  let C := cubicFlowCylinderChart σ ha
  let p₀ : (Fin m → ℝ) × ℝ := (0, T)
  have htime : (fun p => Φ (C p)) =ᶠ[𝓝 p₀] (fun p => Ψ (C p)) := by
    have hball : ∀ᶠ p in 𝓝 p₀, C p ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
      (contDiff_cubicFlowCylinder σ a).continuous.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds hTball)
    filter_upwards [continuousAt_fst.eventually hmatch,
      continuousAt_snd.eventually (hJ.mem_nhds hTJ), hball] with p hp hpt hpball
    exact hp p.2 hpt (Metric.ball_subset_closedBall hpball)
  have hCt : C p₀ ∈ C.target := C.map_source' (Set.mem_univ p₀)
  have hi : C.symm (C p₀) = p₀ := C.left_inv' (Set.mem_univ p₀)
  have hInv : Filter.Tendsto C.symm (𝓝 (C p₀)) (𝓝 p₀) := by
    have hh : Filter.Tendsto C.symm (𝓝 (C p₀)) (𝓝 (C.symm (C p₀))) :=
      C.toOpenPartialHomeomorph.symm.continuousAt hCt |>.tendsto
    rwa [hi] at hh
  refine ⟨T, hTJ, hTball, ?_⟩
  filter_upwards [hInv.eventually htime, C.open_target.mem_nhds hCt] with p hp hpt
  have hright : C (C.symm p) = p := C.right_inv' hpt
  change Φ (C (C.symm p)) = Ψ (C (C.symm p)) at hp
  rwa [hright] at hp

theorem MorseCancellation.cubicFlowCylinder_forward_stays_box {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim :
      Filter.Tendsto (fun t => cubicFlowCylinder σ a (z, t)) Filter.atTop
        (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) {t : ℝ}
    (ht : T ≤ t) : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear :
    ∀ᶠ u in Filter.atTop, cubicFlowCylinder σ a (z, u) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (Filter.eventually_ge_atTop t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨ht, hut⟩ hT (Metric.ball_subset_closedBall hu)

theorem MorseCancellation.cubicFlowCylinder_backward_stays_box {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim :
      Filter.Tendsto (fun t => cubicFlowCylinder σ a (z, t)) Filter.atBot
        (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) {t : ℝ}
    (ht : t ≤ T) : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear :
    ∀ᶠ u in Filter.atBot, cubicFlowCylinder σ a (z, u) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (Filter.eventually_le_atBot t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨hut, ht⟩ (Metric.ball_subset_closedBall hu) hT

theorem MorseCancellation.strictMono_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    StrictMono (cubicAxisParameter a) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left (strictMono_tanh (mul_lt_mul_of_pos_left hst ha)) ha

theorem MorseCancellation.tendsto_cubicFlowCylinder_axis_atTop {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) :
    Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) Filter.atTop
      (𝓝 (a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atTop (m := m) ha

theorem MorseCancellation.tendsto_cubicFlowCylinder_axis_atBot {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) :
    Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) Filter.atBot
      (𝓝 (-a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atBot (m := m) ha

theorem MorseCancellation.cubicFlowCylinder_zero_clock {m : ℕ} (σ : Fin m → ℝ) {a s : ℝ} (ha : 0 < a)
    (hs : s ∈ Set.Ioo (-a) a) :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
  rw [cubicFlowCylinder_axis]
  change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
  rw [cubicAxisParameter_clock ha hs]

theorem MorseCancellation.incoming_axis_segment_in_box {m : ℕ} (σ : Fin m → ℝ) {a r T : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Set.Icc (cubicAxisParameter a T) a,
      (s, (0 : Fin m → ℝ)) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) r ∧
        (s < a → T ≤ cubicAxisClock a s) := by
  intro s hs
  rcases hs.2.lt_or_eq with hsa | hsa
  · have hs' : s ∈ Set.Ioo (-a) a := ⟨(cubicAxisParameter_mem ha T).1.trans_le hs.1, hsa⟩
    have ht : T ≤ cubicAxisClock a s := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.1
    have hb :=
      cubicFlowCylinder_forward_stays_box σ ha 0 hr (tendsto_cubicFlowCylinder_axis_atTop σ ha)
        hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩
  · subst s
    exact ⟨Metric.mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩

theorem MorseCancellation.outgoing_axis_segment_in_box {m : ℕ} (σ : Fin m → ℝ) {a r T : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Set.Icc (-a) (cubicAxisParameter a T),
      (s, (0 : Fin m → ℝ)) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) r ∧
        (-a < s → cubicAxisClock a s ≤ T) := by
  intro s hs
  rcases hs.1.eq_or_lt with has | has
  · subst s
    exact ⟨Metric.mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩
  · have hs' : s ∈ Set.Ioo (-a) a := ⟨has, hs.2.trans_lt (cubicAxisParameter_mem ha T).2⟩
    have ht : cubicAxisClock a s ≤ T := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.2
    have hb :=
      cubicFlowCylinder_backward_stays_box σ ha 0 hr (tendsto_cubicFlowCylinder_axis_atBot σ ha)
        hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩

theorem MorseCancellation.exists_matched_full_cubic_field_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (Φq Φm Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hmfield : ∀ y ∈ Φm.target, V y = nativeCubicDescent σ Φm (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y) {rq rp : ℝ}
    (hrq : 0 < rq) (hrp : 0 < rp) (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) rp ⊆ Φp.source)
    (hmiddle : ∀ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φm.source)
    (hleft : Φq (-a, 0) ∉ Φm.target) (hright : Φp (a, 0) ∉ Φm.target)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hmatchq :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          t ≤ -1 →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
              Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)))
    (hmatchp :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          2 ≤ t →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
              Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
          Φ (-a, 0) = Φq (-a, 0) ∧
            Φ (a, 0) = Φp (a, 0) ∧
              (∀ s ∈ Set.Ioo (-a) a, Φ (s, 0) = Φm (s, 0)) ∧
                ((Φ : Model m → M) =ᶠ[𝓝 (-a, (0 : Fin m → ℝ))] Φq) ∧
                  ((Φ : Model m → M) =ᶠ[𝓝 (a, (0 : Fin m → ℝ))] Φp) := by
  have hqmatch :
    ∀ᶠ z : Fin m → ℝ in 𝓝 0,
      ∀ t ∈ Set.Iio (-1 : ℝ),
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
          Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchq] with z hz
    exact fun t ht => hz t ht.le
  have hpmatch :
    ∀ᶠ z : Fin m → ℝ in 𝓝 0,
      ∀ t ∈ Set.Ioi (2 : ℝ),
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
          Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchp] with z hz
    exact fun t ht => hz t ht.le
  obtain ⟨Tq, hTq, hqball, hgq⟩ :=
    exists_cubic_spatial_overlap_germ σ ha Φq Φm hrq (tendsto_cubicFlowCylinder_axis_atBot σ ha)
      isOpen_Iio (Filter.Iio_mem_atBot (-1 : ℝ)) hqmatch
  obtain ⟨Tp, hTp, hpball, hgp⟩ :=
    exists_cubic_spatial_overlap_germ σ ha Φp Φm hrp (tendsto_cubicFlowCylinder_axis_atTop σ ha)
      isOpen_Ioi (Filter.Ioi_mem_atTop (2 : ℝ)) hpmatch
  have hcutq := cubicAxisParameter_mem ha Tq
  have hcutp := cubicAxisParameter_mem ha Tp
  have horder : cubicAxisParameter a Tq < cubicAxisParameter a Tp :=
    strictMono_cubicAxisParameter ha (by change Tq < -1 at hTq; change 2 < Tp at hTp; linarith)
  have hgq' : (Φq : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tq, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgq
  have hgp' : (Φp : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tp, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgp
  have hqsegment := outgoing_axis_segment_in_box σ ha hrq (Metric.ball_subset_closedBall hqball)
  have hpsegment := incoming_axis_segment_in_box σ ha hrp (Metric.ball_subset_closedBall hpball)
  have hqaxis (s : ℝ) (hs : s ∈ Set.Ioc (-a) (cubicAxisParameter a Tq)) : Φq (s, 0) = Φm (s, 0) :=
    by
    have hs' : s ∈ Set.Ioo (-a) a := ⟨hs.1, hs.2.trans_lt hcutq.2⟩
    obtain ⟨hb, ht⟩ := hqsegment s ⟨hs.1.le, hs.2⟩
    have hball :
      cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈
        Metric.closedBall (-a, (0 : Fin m → ℝ)) rq := by
      rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchq.self_of_nhds (cubicAxisClock a s) ((ht hs.1).trans hTq.le) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  have hpaxis (s : ℝ) (hs : s ∈ Set.Ico (cubicAxisParameter a Tp) a) : Φp (s, 0) = Φm (s, 0) := by
    have hs' : s ∈ Set.Ioo (-a) a := ⟨hcutp.1.trans_le hs.1, hs.2⟩
    obtain ⟨hb, ht⟩ := hpsegment s ⟨hs.1, hs.2.le⟩
    have hball :
      cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp :=
      by rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchp.self_of_nhds (cubicAxisClock a s) (hTp.le.trans (ht hs.2)) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  exact
    FieldChartGluing.exists_closed_axis_native_field_chart Φq Φm Φp
      (cubicDescent σ (-(a ^ 2))) V hqfield hmfield hpfield hcutq.1 horder hcutp.2
      (fun s hs => hboxq (hqsegment s hs).1) hmiddle (fun s hs => hboxp (hpsegment s hs).1) hgq'
      hgp' hqaxis hpaxis hleft hright hne

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_full_cubic_chart_from_corrected_cylinder {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {m : ℕ}
    {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a : ℝ} (ha : 0 < a) (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (L₁ : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (L₂ : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (Q P : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → Z)
    (v₀ v₁ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ)
    {Oq Op : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)}
    (hOq : IsOpen Oq) (hOp : IsOpen Op) (h0q : 0 ∈ Oq) (h0p : 0 ∈ Op) (hQU : ∀ u ∈ Oq, Q u ∈ U)
    (hPU : ∀ u ∈ Op, P u ∈ U) {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Oq,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
          Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ Op,
        cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
          Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq :
      ∀ u ∈ Oq,
        Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
          A (Q u, Tq + v₀ u))
    (hphasep :
      ∀ u ∈ Op,
        Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
          A (P u, Tp + v₁ u))
    (Ξ :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ) 𝓘(ℝ, E)
        ((MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ) M ∞)
    {O : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)}
    (hO : IsOpen O) (h0O : 0 ∈ O) (hΞsource : Ξ.source = O ×ˢ Set.univ)
    (hΞtarget : Ξ.target = A.target)
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΞfield :
      ∀ y ∈ Ξ.target,
        W y =
          FlowConstruction.partialChartField Ξ.symm
            (fun _ :
                (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ =>
              (0, 1))
            y)
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    (hWq : ∀ᶠ y in 𝓝 (Φq (-a, 0)), W y = V y) (hWp : ∀ᶠ y in 𝓝 (Φp (a, 0)), W y = V y)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hleft :
      ∀ᶠ u in 𝓝 (0 : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
        ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright :
      ∀ᶠ u in 𝓝 (0 : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
        ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, W y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
          Φ (-a, 0) = Φq (-a, 0) ∧ Φ (a, 0) = Φp (a, 0) ∧ Φ (0, 0) = Ξ (0, 0) := by
  let e := MorseHandle.splitCoordinates σ
  let L := L₁.prodCongr L₂
  let T := splitTransverseChange e L₁ L₂
  let D := transverseFieldChange T
  have hqsrc : (-a, (0 : Fin m → ℝ)) ∈ Φq.source := hboxq (Metric.mem_closedBall_self hRq.le)
  have hpsrc : (a, (0 : Fin m → ℝ)) ∈ Φp.source := hboxp (Metric.mem_closedBall_self hRp.le)
  obtain ⟨Ψq, rq, hrq, hΨqbox, hΨqsub, _, hΨqmap, hΨqfield⟩ :=
    FieldChartGluing.exists_controlled_field_germ_chart Φq (cubicDescent σ (-(a ^ 2))) V W
      hqfield hqsrc hWq Metric.isOpen_ball (Metric.mem_ball_self hRq)
  have hcontrolq :
    Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq :=
    fun p hp => Metric.ball_subset_closedBall (hΨqsub (hΨqbox hp)).2
  obtain ⟨ΦpB, _, hpBsource, hpBaxis, hpBfield, hpBflow⟩ :=
    exists_signed_block_changed_cubic_chart σ hσ L₁ L₂ Φp V (-(a ^ 2)) hpfield
  have hDcenter : D (a, 0) = (a, 0) := by change (a, T 0) = (a, 0); rw [map_zero]
  have hOpcoord : IsOpen (D ⁻¹' Metric.ball (a, (0 : Fin m → ℝ)) Rp) :=
    Metric.isOpen_ball.preimage D.continuous
  have hpO : (a, (0 : Fin m → ℝ)) ∈ D ⁻¹' Metric.ball (a, (0 : Fin m → ℝ)) Rp := by
    change D (a, 0) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp
    rw [hDcenter]
    exact Metric.mem_ball_self hRp
  have hWpB : ∀ᶠ y in 𝓝 (ΦpB (a, 0)), W y = V y := by rw [hpBaxis]; exact hWp
  obtain ⟨Ψp, rp, hrp, hΨpbox, hΨpsub, _, hΨpmap, hΨpfield⟩ :=
    FieldChartGluing.exists_controlled_field_germ_chart ΦpB (cubicDescent σ (-(a ^ 2))) V W
      hpBfield ((hpBsource a).mpr hpsrc) hWpB hOpcoord hpO
  have hnewp (z : Fin m → ℝ) (t : ℝ) :
    Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) := by
    have hh := hpBflow a t (e z)
    change
      ΦpB (cubicFlowCylinder σ a (e.symm (e z), t)) =
        Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) at hh
    rw [e.symm_apply_apply] at hh
    exact (hΨpmap _).trans hh
  have hcontrolp (z : Fin m → ℝ) (t : ℝ)
    (hp : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp) :
    cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp := by
    have hb : D (cubicFlowCylinder σ a (z, t)) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp :=
      (hΨpsub (hΨpbox hp)).2
    have hc : D (cubicFlowCylinder σ a (z, t)) = cubicFlowCylinder σ a (e.symm (L (e z)), t) :=
      signed_block_change_cubic_cylinder σ hσ L₁ L₂ a t z
    rw [hc] at hb
    exact Metric.ball_subset_closedBall hb
  let R := PartialChart.restrictTarget e.toDiffeomorph.toPartialDiffeomorph hO
  have hRtarget : R.target = O := by
    ext u
    change
      (u ∈
            (Set.univ :
              Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)) ∧
          u ∈ O) ↔
        u ∈ O
    simp only [Set.mem_univ, true_and]
  have hR0 : (0 : Fin m → ℝ) ∈ R.source := by
    change (0 : Fin m → ℝ) ∈ Set.univ ∧ e 0 ∈ O
    rw [map_zero]
    exact ⟨Set.mem_univ _, h0O⟩
  obtain ⟨B₀, hBsource, hBtarget, hBmap, hBfield⟩ :=
    FlowSuspension.exists_native_phase_cylinder Ξ hΞsource R hRtarget (fun _ => (0 : ℝ))
      contDiff_const W hΞfield
  obtain ⟨Φm, hmTarget, hmidAxis, _, hmField, _, hcompose⟩ :=
    exists_regular_cubic_chart_of_native_vertical_field σ ha B₀ hBsource hR0 W hW hBfield G hG
  have hmid (z : Fin m → ℝ) (t : ℝ) : Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t) := by
    rw [hcompose, hBmap]
    change Ξ (e z, t + 0) = Ξ (e z, t)
    rw [add_zero]
  have hmTargetA : Φm.target = A.target := hmTarget.trans (hBtarget.trans hΞtarget)
  have hzeroAt (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) {c : ℝ}
    (hc : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (hcrit : c ^ 2 = a ^ 2)
    (hf : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) : V (Φ (c, 0)) = 0 := by
    rw [hf _ (Φ.map_source' hc)]
    apply (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) (Φ.map_source' hc)).mpr
    have hi : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hc
    rw [hi]
    ext i <;> simp [cubicDescent, hcrit]
  have hzeroq : V (Φq (-a, 0)) = 0 := hzeroAt Φq hqsrc (by ring) hqfield
  have hzerop : V (Φp (a, 0)) = 0 := hzeroAt Φp hpsrc rfl hpfield
  have hAregular (y : M) (hy : y ∈ A.target) : V y ≠ 0 := by
    intro hz
    rw [hAfield y hy] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hy).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqval : Ψq (-a, 0) = Φq (-a, 0) := hΨqmap _
  have hpval : Ψp (a, 0) = Φp (a, 0) := (hΨpmap _).trans (hpBaxis a)
  have hqnot : Ψq (-a, 0) ∉ Φm.target := by
    rw [hqval, hmTargetA]
    exact fun h => hAregular _ h hzeroq
  have hpnot : Ψp (a, 0) ∉ Φm.target := by
    rw [hpval, hmTargetA]
    exact fun h => hAregular _ h hzerop
  obtain ⟨hmatchq, hmatchp⟩ :=
    matched_cubic_time_formulas σ ha Φq Φp A hAsource hV hqfield hpfield hAfield F hF e L Q P v₀
      v₁ hOq hOp h0q h0p hQU hPU hboxq hboxp hsliceq hslicep hphaseq hphasep Ψq Ψp Φm Ξ hΨqmap
      hnewp hmid hcontrolq hcontrolp hleft hright
  obtain ⟨Φ, haxis, hfield, hΦq, hΦp, hΦmid, _, _⟩ :=
    exists_matched_full_cubic_field_chart σ ha Ψq Φm Ψp W hΨqfield hmField hΨpfield hrq hrp hΨqbox
      hΨpbox (fun s hs => hmidAxis ⟨hs, rfl⟩) hqnot hpnot (by rw [hqval, hpval]; exact hne)
      hmatchq hmatchp
  have hmid0 : Φm (0, 0) = Ξ (0, 0) := by
    have hh := hmid 0 0
    simpa only [cubicFlowCylinder_zero_time, map_zero] using hh
  exact
    ⟨Φ, haxis, hfield, hΦq.trans hqval, hΦp.trans hpval, (hΦmid 0 ⟨by linarith, ha⟩).trans hmid0⟩

theorem FlowSuspension.cylinder_phase_basin_coordinates {E Z M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [TopologicalSpace M] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : E → M) (v : E → ℝ)
    (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) (Basin : M → Prop)
    (hshift : ∀ t x, Basin (F t x) ↔ Basin x) (R : E → Prop)
    (hbasin : ∀ u ∈ Q.source, Basin (Ξ u) ↔ R u) :
    ∀ z ∈ Q.target, ∀ b : ℝ, Basin (Φ (z, b)) ↔ R (Q.symm z) := by
  intro z hz b
  have hu := Q.map_target' hz
  have hi : Q (Q.symm z) = z := Q.right_inv' hz
  have hphase' : Ξ (Q.symm z) = F (v (Q.symm z)) (Φ (z, 0)) := by
    rw [hphase (Q.symm z) hu, hi, hflow z hz]
  have hend : Basin (Ξ (Q.symm z)) ↔ Basin (Φ (z, 0)) := by
    rw [hphase']
    exact hshift _ _
  have hslice : Basin (Φ (z, b)) ↔ Basin (Φ (z, 0)) := by
    rw [hflow z hz b]
    exact hshift _ _
  exact hslice.trans (hend.symm.trans (hbasin _ hu))

theorem FlowSuspension.cylinder_outgoing_basin_labels {Z M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace M] {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : (A × B) → M)
    (v : (A × B) → ℝ) (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) {q : M}
    (hbasin : ∀ u ∈ Q.source, Filter.Tendsto (fun t => F t (Ξ u)) Filter.atBot (𝓝 q) ↔ u.2 = 0) :
    ∀ z ∈ Q.target,
      ∀ b : ℝ,
        Filter.Tendsto (fun t => F t (Φ (z, b))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ Q.source ∧ Q (x, 0) = z := by
  have hcoord :=
    cylinder_phase_basin_coordinates F Φ Q hflow Ξ v hphase
      (fun x => Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
      (fun t x => MorseCancellation.flow_time_atBot_limit_iff F t x q) (fun u : A × B => u.2 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    have hpair : Q.symm z = ((Q.symm z).1, (0 : B)) := Prod.ext rfl hu
    refine ⟨(Q.symm z).1, hpair ▸ Q.map_target' hz, ?_⟩
    rw [← hpair]
    exact Q.right_inv' hz
  · rintro ⟨x, hx, hQx⟩
    have hi : Q.symm (Q (x, (0 : B))) = (x, 0) := Q.left_inv' hx
    rw [← hQx, hi]

theorem FlowSuspension.cylinder_incoming_basin_labels {Z M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace M] {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ P.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : (A × B) → M)
    (v : (A × B) → ℝ) (hphase : ∀ u ∈ P.source, Ξ u = Φ (P u, v u)) {p : M}
    (hbasin : ∀ u ∈ P.source, Filter.Tendsto (fun t => F t (Ξ u)) Filter.atTop (𝓝 p) ↔ u.1 = 0) :
    ∀ z ∈ P.target,
      ∀ b : ℝ,
        Filter.Tendsto (fun t => F t (Φ (z, b))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ P.source, y.1 = 0 ∧ P y = z := by
  have hcoord :=
    cylinder_phase_basin_coordinates F Φ P hflow Ξ v hphase
      (fun x => Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
      (fun t x => MorseCancellation.flow_time_atTop_limit_iff F t x p) (fun u : A × B => u.1 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    exact ⟨P.symm z, P.map_target' hz, hu, P.right_inv' hz⟩
  · rintro ⟨y, hy, hy0, hPy⟩
    have hi : P.symm (P y) = y := P.left_inv' hy
    rw [← hPy, hi]
    exact hy0

theorem MorseCancellation.cubicFlowCylinder_transverse_zero_iff {m : ℕ} (σ : Fin m → ℝ) (a T : ℝ)
    (z : Fin m → ℝ) (i : Fin m) : (cubicFlowCylinder σ a (z, T)).2 i = 0 ↔ z i = 0 := by
  simp [cubicFlowCylinder, Real.exp_ne_zero]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.incoming_cubic_slice_basin {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (σ : Fin m → ℝ) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (F : Flow ℝ M) {p : M}
    (hbasin :
      ∀ z ∈ Φ.source,
        Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p) ↔ ∀ i, σ i = -1 → z.2 i = 0)
    (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Filter.Tendsto
        (fun t =>
          F t (Φ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T))))
        Filter.atTop (𝓝 p) ↔
      u.1 = 0 := by
  rw [hbasin _ hu]
  have he :
    (∀ i,
        σ i = -1 →
          (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = -1 → (MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← TransverseGerms.splitCoordinates_negative_zero_iff]
  rw [(MorseHandle.splitCoordinates σ).apply_symm_apply]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.outgoing_cubic_slice_basin {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (F : Flow ℝ M) {q : M}
    (hbasin :
      ∀ z ∈ Φ.source,
        Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 q) ↔ ∀ i, σ i = 1 → z.2 i = 0)
    (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Filter.Tendsto
        (fun t =>
          F t (Φ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T))))
        Filter.atBot (𝓝 q) ↔
      u.2 = 0 := by
  rw [hbasin _ hu]
  have he :
    (∀ i,
        σ i = 1 →
          (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = 1 → (MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← TransverseGerms.splitCoordinates_positive_zero_iff σ hσ]
  rw [(MorseHandle.splitCoordinates σ).apply_symm_apply]

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

def MorseCancellation.transverseEnergy {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : ℝ :=
  ∑ i, (σ i * p.2 i) ^ 2

theorem MorseCancellation.transverseEnergy_nonneg {m : ℕ} (σ : Fin m → ℝ) (p : Model m) :
    0 ≤ transverseEnergy σ p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem MorseCancellation.transverseEnergy_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : transverseEnergy σ p = 0 ↔ p.2 = 0 := by
  constructor
  · intro h
    funext i
    have hh :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp h i
        (Finset.mem_univ i)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hh)).resolve_left (hσ i)
  · intro h
    simp [transverseEnergy, h]

def MorseCancellation.fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) : ℝ :=
  p.1 + k * ∑ i, σ i * p.2 i ^ 2

theorem MorseCancellation.contDiff_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) :
    ContDiff ℝ ∞ (fieldLyapunov σ k) := by
  unfold fieldLyapunov
  fun_prop

theorem MorseCancellation.hasFDerivAt_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) :
    HasFDerivAt (fieldLyapunov σ k)
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
        k •
          ∑ i,
            (2 * σ i * p.2 i) •
              ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))
      p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! hx.add (hq.const_mul k) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [mul_assoc, mul_comm]

theorem MorseCancellation.fieldLyapunov_speed {m : ℕ} (σ : Fin m → ℝ) (k a : ℝ) (φ : Model m → ℝ)
    (p : Model m) :
    fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) =
      (cancelledDescent σ a φ p).1 - 2 * k * transverseEnergy σ p := by
  rw [(hasFDerivAt_fieldLyapunov σ k p).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change
    (cancelledDescent σ a φ p).1 + k * (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = _
  have hsum :
    (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = -2 * transverseEnergy σ p := by
    rw [transverseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change 2 * σ i * p.2 i * (-σ i * p.2 i) = _
    ring
  rw [hsum]
  ring

theorem MorseCancellation.exists_compact_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) {C : Set (Model m)} (hC : IsCompact C) :
    ∃ k : ℝ,
      0 ≤ k ∧
        ContDiff ℝ ∞ (fieldLyapunov σ k) ∧
          ∀ p ∈ C, fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) < 0 := by
  let O : ℕ → Set (Model m) := fun n =>
    {p | (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0}
  have henergy : Continuous (transverseEnergy σ) := by
    unfold transverseEnergy
    fun_prop
  have hO (n : ℕ) : IsOpen (O n) :=
    isOpen_lt
      ((contDiff_cancelledDescent σ a hφ).continuous.fst.sub (continuous_const.mul henergy))
      continuous_const
  have hcover : C ⊆ ⋃ n, O n := by
    intro p hp
    by_cases hz : p.2 = 0
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
      have hh := cancelledDescent_axis_negative σ ha hφnonneg hone p.1
      have hneg : (cancelledDescent σ a φ p).1 < 0 :=
        (congrArg (fun q : Model m => (cancelledDescent σ a φ q).1) he).trans_lt hh
      simpa only [O, Set.mem_ofPred_eq, Nat.cast_zero, MulZeroClass.mul_zero,
        MulZeroClass.zero_mul, sub_zero] using hneg
    · have hpos : 0 < transverseEnergy σ p :=
        lt_of_le_of_ne (transverseEnergy_nonneg σ p)
          (Ne.symm (fun he => hz ((transverseEnergy_zero_iff σ hσ p).mp he)))
      obtain ⟨n, hn⟩ := exists_nat_gt ((cancelledDescent σ a φ p).1 / (2 * transverseEnergy σ p))
      have hh := (div_lt_iff₀ (mul_pos (by norm_num) hpos)).mp hn
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0
      nlinarith
  have hmono : Monotone O := by
    intro i j hij p hp
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have he := transverseEnergy_nonneg σ p
    change (cancelledDescent σ a φ p).1 - 2 * (i : ℝ) * transverseEnergy σ p < 0 at hp
    change (cancelledDescent σ a φ p).1 - 2 * (j : ℝ) * transverseEnergy σ p < 0
    nlinarith
  obtain ⟨n, hn⟩ :=
    hC.elim_directed_cover O hO hcover
      (fun i j => ⟨Max.max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
  refine ⟨n, by positivity, contDiff_fieldLyapunov σ n, ?_⟩
  intro p hp
  rw [fieldLyapunov_speed]
  exact hn hp

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

theorem FlowCancellation.hasDerivAt_comp_native_integralCurve_at {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ t)) (hγ : IsMIntegralCurve γ V) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t := by
  have hd := hf.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (V (γ t))
  exact map_smul _ _ _

theorem FlowCancellation.mvfderiv_signedLevelTime {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hx : x ∈ levelBasin F f c) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 := by
  obtain ⟨hB, hsmooth, hshift⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  have hlocal := (hsmooth x hx).contMDiffAt (hB.mem_nhds hx)
  have hlocal0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (signedLevelTime F f c) (F 0 x) := by
    rw [F.map_zero_apply]
    exact hlocal.mdifferentiableAt (by simp)
  have hd := hasDerivAt_comp_native_integralCurve_at hlocal0 (hcurve x)
  have heq :
    (signedLevelTime F f c ∘ (fun t => F t x)) = fun t : ℝ => signedLevelTime F f c x - t :=
    funext (hshift x hx)
  rw [heq] at hd
  have hh := hd.unique ((hasDerivAt_id (0 : ℝ)).const_sub (signedLevelTime F f c x))
  have he :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) y (V y)) (F.map_zero_apply x)
  exact he.symm.trans hh

def FlowCancellation.crossingBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) : Set X :=
  levelBasin F f c ∩ levelBasin F f d

def FlowCancellation.crossingDuration {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  signedLevelTime F f c x - signedLevelTime F f d x

def FlowCancellation.flowBandHeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  c + (d - c) * signedLevelTime F f c x / crossingDuration F f c d x

theorem FlowCancellation.crossingDuration_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hcd : c < d) {x : X} (hx : x ∈ crossingBasin F f c d) :
    0 < crossingDuration F f c d x := by
  apply sub_pos.mpr
  by_contra h
  have hle := le_of_not_gt h
  have hh :=
    forwardInvariant_sublevel_of_boundary F hf hD hder hc (F (signedLevelTime F f c x) x)
      (signedLevelTime_hits F f c hx.1).le (signedLevelTime F f d x - signedLevelTime F f c x)
      (sub_nonneg.mpr hle)
  rw [← F.map_add, sub_add_cancel, signedLevelTime_hits F f d hx.2] at hh
  exact (not_le_of_gt hcd) hh

theorem FlowCancellation.crossingDuration_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    crossingDuration F f c d (F s x) = crossingDuration F f c d x := by
  simp only [crossingDuration, signedLevelTime_flow F hf hD hder hc hx.1 s,
    signedLevelTime_flow F hf hD hder hd hx.2 s]
  ring

theorem FlowCancellation.flowBandHeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    flowBandHeight F f c d (F s x) =
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * s := by
  simp only [flowBandHeight, crossingDuration_flow F hf hD hder hc hd hx s,
    signedLevelTime_flow F hf hD hder hc hx.1 s]
  ring

theorem FlowCancellation.flowBandHeight_lower {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : flowBandHeight F f c d x = c := by
  simp only [flowBandHeight, signedLevelTime_eq_zero F hf hD hder hc hx, MulZeroClass.mul_zero,
    zero_div, add_zero]

theorem FlowCancellation.flowBandHeight_upper {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) (hcd : c < d) {x : X}
    (hx : x ∈ crossingBasin F f c d) (hfx : f x = d) : flowBandHeight F f c d x = d := by
  have hz := signedLevelTime_eq_zero F hf hD hder hd hfx
  have hpos := crossingDuration_pos F hf hD hder hc hcd hx
  have heq : signedLevelTime F f c x = crossingDuration F f c d x := by
    simp only [crossingDuration, hz, sub_zero]
  rw [flowBandHeight, heq, mul_div_cancel_right₀ _ hpos.ne']
  ring

theorem FlowCancellation.smooth_flowBandHeight {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (crossingBasin F f c d) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) ∧
        ∀ x ∈ crossingBasin F f c d,
          mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) =
              -((d - c) / crossingDuration F f c d x) ∧
            mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) < 0 := by
  obtain ⟨hBc, htc, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  obtain ⟨hBd, htd, -⟩ := smooth_signed_level_time hf hV F hcurve hd
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hB : IsOpen (crossingBasin F f c d) := hBc.inter hBd
  have hpos (x : M) (hx : x ∈ crossingBasin F f c d) : 0 < crossingDuration F f c d x :=
    crossingDuration_pos F hf.continuous hD hder hc hcd hx
  have hsc := htc.mono (Set.inter_subset_left : crossingBasin F f c d ⊆ levelBasin F f c)
  have hsd := htd.mono (Set.inter_subset_right : crossingBasin F f c d ⊆ levelBasin F f d)
  have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (crossingDuration F f c d) (crossingBasin F f c d) :=
    hsc.sub hsd
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) :=
    contMDiffOn_const.add ((contMDiffOn_const.mul hsc).div₀ hA (fun x hx => (hpos x hx).ne'))
  refine ⟨hB, hg, ?_⟩
  intro x hx
  have hlocal : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (flowBandHeight F f c d) (F 0 x) := by
    rw [F.map_zero_apply]
    exact ((hg x hx).contMDiffAt (hB.mem_nhds hx)).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_comp_native_integralCurve_at hlocal (hcurve x)
  have heq :
    (flowBandHeight F f c d ∘ (fun t => F t x)) = fun t =>
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * t :=
    funext (fun t => flowBandHeight_flow F hf.continuous hD hder hc hd hx t)
  rw [heq] at hchain
  have hline :=
    ((hasDerivAt_id (0 : ℝ)).const_mul ((d - c) / crossingDuration F f c d x)).const_sub
      (flowBandHeight F f c d x)
  have hnative :
    mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) = -((d - c) / crossingDuration F f c d x) :=
    by
    have he :=
      congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) y (V y))
        (F.map_zero_apply x)
    exact he.symm.trans (by simpa using hchain.unique hline)
  exact ⟨hnative, hnative ▸ neg_neg_of_pos (div_pos (sub_pos.mpr hcd) (hpos x hx))⟩

def FlowCancellation.logarithmicCoordinate (η L t : ℝ) : ℝ :=
  Real.log (1 + (t / η) ^ 2) / L

theorem FlowCancellation.contDiff_logarithmicCoordinate (η L : ℝ) :
    ContDiff ℝ ∞ (logarithmicCoordinate η L) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.add ((contDiff_id.div_const η).pow 2)
  · intro t
    positivity

theorem FlowCancellation.hasDerivAt_logarithmicCoordinate {η L : ℝ} (hη : 0 < η)
    (hL : 0 < L) (t : ℝ) :
    HasDerivAt (logarithmicCoordinate η L) (2 * t / (L * (η ^ 2 + t ^ 2))) t := by
  have hp : 1 + (t / η) ^ 2 ≠ 0 := by positivity
  have hh := (((((hasDerivAt_id t).div_const η).pow 2).const_add 1).log hp).div_const L
  convert hh using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp

theorem FlowCancellation.logarithmicCoordinate_weighted_deriv_bound {η L : ℝ} (hη : 0 < η)
    (hL : 0 < L) (t : ℝ) : |t * deriv (logarithmicCoordinate η L) t| ≤ 2 / L := by
  rw [(hasDerivAt_logarithmicCoordinate hη hL t).deriv]
  have hden : 0 < η ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hη) (sq_nonneg t)
  have heq : t * (2 * t / (L * (η ^ 2 + t ^ 2))) = (2 / L) * (t ^ 2 / (η ^ 2 + t ^ 2)) := by
    field_simp
  rw [heq, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one hden).mpr (by nlinarith))

theorem FlowCancellation.exists_logarithmic_cutoff {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧
        HasCompactSupport χ ∧
          (∀ᶠ t in 𝓝 0, χ t = 1) ∧
            (∀ t, ε ≤ |t| → χ t = 0) ∧
              (∀ t, χ t ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ t, |t * deriv χ t| < δ := by
  obtain ⟨β, hβ, hcompact, hsupp, hone, hrange⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : ℝ)}) (U := Metric.ball 0 1) isCompact_singleton
      Metric.isOpen_ball (by simp)
  obtain ⟨C, hC⟩ := hcompact.deriv.exists_bound_of_continuous (hβ.continuous_deriv (by simp))
  let B : ℝ := Max.max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (t : ℝ) : |deriv β t| ≤ B := by
    have hh := hC t
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [B]; linarith [le_max_left C 0])
  let L : ℝ := 2 * B / δ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : B * (2 / L) < δ := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hL).mpr
    dsimp [L]
    have hd : δ * (2 * B / δ) = 2 * B := by field_simp
    nlinarith
  let η : ℝ := ε / Real.exp L
  have hη : 0 < η := div_pos hε (Real.exp_pos L)
  let q := logarithmicCoordinate η L
  have hq : ContDiff ℝ ∞ q := contDiff_logarithmicCoordinate η L
  have hqzero : q 0 = 0 := by simp [q, logarithmicCoordinate]
  let χ : ℝ → ℝ := β ∘ q
  have hχ : ContDiff ℝ ∞ χ := hβ.comp hq
  have hout (t : ℝ) (ht : ε ≤ |t|) : χ t = 0 := by
    have hratio : Real.exp L ≤ |t / η| := by
      rw [abs_div, abs_of_pos hη, le_div_iff₀ hη]
      have he : Real.exp L * η = ε := by dsimp [η]; field_simp
      simpa only [he] using ht
    have heone : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL.le
    have hlower : L ≤ Real.log (1 + (t / η) ^ 2) := by
      apply (Real.le_log_iff_exp_le (by positivity)).mpr
      nlinarith [sq_abs (t / η)]
    have honeq : 1 ≤ q t := (le_div_iff₀ hL).mpr (by simpa using hlower)
    have hnotsupp : q t ∉ tsupport β := by
      intro hh
      have hball := hsupp hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hball
      linarith [hball.2]
    change β (q t) = 0
    exact image_eq_zero_of_notMem_tsupport hnotsupp
  have hcompactχ : HasCompactSupport χ := by
    apply HasCompactSupport.intro (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (-ε) ε))
    intro t ht
    apply hout
    by_contra h
    have hh := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨hh.1.le, hh.2.le⟩
  have hnear : ∀ᶠ t in 𝓝 0, χ t = 1 := by
    have hb : ∀ᶠ r in 𝓝 (0 : ℝ), β r = 1 := by simpa only [nhdsSet_singleton] using hone
    have ht : Filter.Tendsto q (𝓝 0) (𝓝 0) := by
      have hh : Filter.Tendsto q (𝓝 0) (𝓝 (q 0)) := hq.continuous.continuousAt
      simpa only [hqzero] using hh
    exact ht.eventually hb
  refine ⟨χ, hχ, hcompactχ, hnear, hout, fun t => hrange (q t), ?_⟩
  intro t
  have hder : deriv χ t = deriv β (q t) * deriv q t :=
    ((hβ.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
        (hq.differentiable (by simp)).differentiableAt.hasDerivAt).deriv
  rw [hder]
  have he : |t * (deriv β (q t) * deriv q t)| = |deriv β (q t)| * |t * deriv q t| := by
    rw [← abs_mul]; congr 1; ring
  rw [he]
  exact
    lt_of_le_of_lt
      (mul_le_mul (hbound _) (logarithmicCoordinate_weighted_deriv_bound hη hL t) (abs_nonneg _)
        hB.le)
      hsmall

theorem FlowCancellation.deriv_eq_zero_of_nonneg_zero {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (hnonneg : ∀ t, 0 ≤ χ t) {t : ℝ} (ht : χ t = 0) : deriv χ t = 0 := by
  have hm : IsLocalMin χ t :=
    Filter.Eventually.of_forall
      (fun s => by
        change χ t ≤ χ s
        rw [ht]
        exact hnonneg s)
  exact hm.hasDerivAt_eq_zero (hχ t).hasDerivAt

theorem FlowCancellation.weighted_blend_neg {α a b r s z μ C δ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (ha : a ≤ -μ) (hb : b ≤ -μ) (hC : 0 ≤ C) (hr : |r| ≤ C * |s|)
    (hz : |s * z| ≤ δ) (hsmall : C * δ < μ) : b + α * (a - b) - z * r < 0 := by
  have hbase : b + α * (a - b) ≤ -μ := by
    nlinarith [mul_nonneg hα.1 (sub_nonneg.mpr ha),
      mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hb)]
  have herr : |z * r| ≤ C * δ :=
    calc
      |z * r| = |z| * |r| := abs_mul _ _
      _ ≤ |z| * (C * |s|) := (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
      _ = C * |s * z| := by rw [abs_mul]; ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hz hC
  linarith [neg_abs_le (z * r)]

theorem FlowCancellation.hasDerivAt_flow_height_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (F : Flow ℝ M)
    (hcurve : IsMIntegralCurve (fun t => F t x) V) :
    HasDerivAt (fun t => f (F t x)) (mvfderiv 𝓘(ℝ, E) f x (V x)) 0 := by
  have hf0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (F 0 x) := by
    rw [F.map_zero_apply]
    exact hf
  have hh := hasDerivAt_comp_native_integralCurve_at hf0 hcurve
  have he := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  exact he ▸ hh

def FlowCancellation.descentBlend {M : Type*} (χ : ℝ → ℝ) (θ f g : M → ℝ) (x : M) : ℝ :=
  g x + χ (θ x) * (f x - g x)

theorem FlowCancellation.mvfderiv_descentBlend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {χ : ℝ → ℝ} {θ f g : M → ℝ} {x : M}
    (hχ : ContDiff ℝ ∞ χ) (hθ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ x)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f x) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g x)
    (F : Flow ℝ M) (hcurve : IsMIntegralCurve (fun t => F t x) V)
    (htime : mvfderiv 𝓘(ℝ, E) θ x (V x) = -1) :
    mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) =
      mvfderiv 𝓘(ℝ, E) g x (V x) +
          χ (θ x) * (mvfderiv 𝓘(ℝ, E) f x (V x) - mvfderiv 𝓘(ℝ, E) g x (V x)) -
        deriv χ (θ x) * (f x - g x) := by
  have dθ := hasDerivAt_flow_height_zero (hθ.mdifferentiableAt (by simp)) F hcurve
  have df := hasDerivAt_flow_height_zero (hf.mdifferentiableAt (by simp)) F hcurve
  have dg := hasDerivAt_flow_height_zero (hg.mdifferentiableAt (by simp)) F hcurve
  rw [htime] at dθ
  have dχ := ((hχ.differentiable (by simp)) (θ (F 0 x))).hasDerivAt.comp 0 dθ
  have db := dg.add (dχ.mul (df.sub dg))
  have hb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (descentBlend χ θ f g) x :=
    hg.add ((hχ.contMDiff.contMDiffAt.comp x hθ).mul (hf.sub hg))
  have dn := hasDerivAt_flow_height_zero (hb.mdifferentiableAt (by simp)) F hcurve
  have he := dn.unique db
  simp only [Pi.sub_apply, Function.comp_apply, F.map_zero_apply] at he
  exact he.trans (by ring)

theorem FlowCancellation.exists_native_descent_blend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {θ f g : M → ℝ}
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (htime : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) θ x (V x) = -1)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {ε μ C : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hC : 0 ≤ C)
    (hcollar :
      ∀ x ∈ U,
        |θ x| < ε →
          mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
            mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |θ x|) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x ∈ U, θ x = 0 → b =ᶠ[𝓝 x] f) ∧
            (∀ x, ε ≤ |θ x| → b x = g x) ∧ ∀ x ∈ U, ε < |θ x| → b =ᶠ[𝓝 x] g := by
  let δ := μ / (C + 1)
  have hδ : 0 < δ := div_pos hμ (by positivity)
  have hsmall : C * δ < μ := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  obtain ⟨χ, hχ, -, hone, hzero, hrange, hweight⟩ := exists_logarithmic_cutoff hε hδ
  let b := descentBlend χ θ f g
  have hb : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U :=
    hg.add ((hχ.contMDiff.comp_contMDiffOn hθ).mul (hf.sub hg))
  have hout (x : M) (hx : ε ≤ |θ x|) : b x = g x := by
    simp only [b, descentBlend, hzero _ hx, MulZeroClass.zero_mul, add_zero]
  refine ⟨b, hb, ?_, ?_, hout, ?_⟩
  · intro x hx
    have hder :=
      mvfderiv_descentBlend hχ ((hθ x hx).contMDiffAt (hU.mem_nhds hx))
        ((hf x hx).contMDiffAt (hU.mem_nhds hx)) ((hg x hx).contMDiffAt (hU.mem_nhds hx)) F
        (hcurve x) (htime x hx)
    change mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) < 0
    rw [hder]
    by_cases hnear : |θ x| < ε
    · obtain ⟨hdf, hdg, hdiff⟩ := hcollar x hx hnear
      exact weighted_blend_neg (hrange _) hdf hdg hC hdiff (hweight _).le hsmall
    · have hz := hzero (θ x) (le_of_not_gt hnear)
      have hdχ :=
        deriv_eq_zero_of_nonneg_zero (hχ.differentiable (by simp)) (fun t => (hrange t).1) hz
      simpa only [hz, hdχ, MulZeroClass.zero_mul, add_zero, sub_zero] using hgneg x hx
  · intro x hx hxzero
    have ht : ContinuousAt θ x := (hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hone' : ∀ᶠ t in 𝓝 (θ x), χ t = 1 := by simpa only [hxzero] using hone
    filter_upwards [ht.eventually hone'] with y hy
    change g y + χ (θ y) * (f y - g y) = f y
    rw [hy]
    ring
  · intro x hx hxout
    have ht : ContinuousAt (fun y => |θ y|) x :=
      ((hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)).abs
    filter_upwards [ht (eventually_gt_nhds hxout)] with y hy
    exact hout y hy.le

def FlowCancellation.flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (S : Set X)
    (ε : ℝ) : Set X :=
  (fun q : ℝ × X => F q.1 q.2) '' (Set.Icc (-ε) ε ×ˢ S)

theorem FlowCancellation.isCompact_flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {S : Set X} (hS : IsCompact S) (ε : ℝ) : IsCompact (flowTube F S ε) :=
  (CompactIccSpace.isCompact_Icc.prod hS).image (F.continuous continuous_fst continuous_snd)

theorem FlowCancellation.exists_flowTube_subset {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S N : Set X} (hS : IsCompact S) (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ ε : ℝ, 0 < ε ∧ flowTube F S ε ⊆ N := by
  have hopen : IsOpen {t : ℝ | ∀ x ∈ S, F t x ∈ N} :=
    MorsePerturbation.isOpen_forall_mem_compact hS
      (hN.preimage (F.continuous continuous_fst continuous_snd))
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∀ x ∈ S, F t x ∈ N} := by
    intro x hx
    simpa only [F.map_zero_apply] using hSN hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  apply hball ?_ x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

theorem FlowCancellation.mem_flowTube_of_signedTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {ε : ℝ} {x : X} (hx : x ∈ levelBasin F f c)
    (ht : |signedLevelTime F f c x| ≤ ε) : x ∈ flowTube F {y | f y = c} ε := by
  refine
    ⟨(-signedLevelTime F f c x, F (signedLevelTime F f c x) x),
      ⟨?_, signedLevelTime_hits F f c hx⟩, ?_⟩
  · constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  · simp only [← F.map_add, neg_add_cancel, F.map_zero_apply]

theorem FlowCancellation.exists_compact_negative_margin {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {D : X → ℝ} (hD : ContinuousOn D S) (hneg : ∀ x ∈ S, D x < 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ S, D x < -μ := by
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hS.exists_isMaxOn hne hD
    refine ⟨-D p / 2, by linarith [hneg p hp], ?_⟩
    intro x hx
    have hle : D x ≤ D p := hmax hx
    linarith [hneg p hp]
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

theorem FlowCancellation.contMDiffOn_directionalDerivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U)
    {g : M → ℝ} (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) g x (V x)) U := by
  have ht :=
    (hg.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn).comp hV.contMDiffOn
      (fun x hx => hx)
  have hh := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn ht
  apply hh.congr
  intro x hx
  change
    (NormedSpace.fromTangentSpace (g x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (V x)) =
      (NormedSpace.fromTangentSpace (g x)) (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g U x (V x))
  rw [mfderivWithin_of_isOpen hU hx]

theorem FlowCancellation.exists_native_time_collar_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {U : Set M}
    (hU : IsOpen U) {f g : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ ε μ C : ℝ,
      0 < ε ∧
        0 < μ ∧
          0 ≤ C ∧
            ∀ x ∈ U,
              |signedLevelTime F f c x| < ε →
                mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
                  mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |signedLevelTime F f c x| :=
  by
  let S : Set M := {x | f x = c}
  have hS : IsCompact S := (isClosed_eq hf.continuous continuous_const).isCompact
  let Df (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let Dg (x : M) := mvfderiv 𝓘(ℝ, E) g x (V x)
  have hDf : Continuous Df := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hDg : ContinuousOn Dg U := (contMDiffOn_directionalDerivative hU hg hV).continuousOn
  have hmax : ContinuousOn (fun x => Max.max (Df x) (Dg x)) U :=
    continuous_max.comp_continuousOn (hDf.continuousOn.prodMk hDg)
  obtain ⟨μ, hμ, hmargin⟩ :=
    exists_compact_negative_margin hS (hmax.mono hlevel)
      (fun x hx => max_lt (hfc x hx) (hgc x hx))
  let N : Set M := U ∩ (fun x => Max.max (Df x) (Dg x)) ⁻¹' Set.Iio (-μ)
  have hN : IsOpen N := hmax.isOpen_inter_preimage hU isOpen_Iio
  have hSN : S ⊆ N := fun x hx => ⟨hlevel hx, hmargin x hx⟩
  obtain ⟨ε, hε, htube⟩ := exists_flowTube_subset F hS hN hSN
  let K := flowTube F S ε
  have hK : IsCompact K := isCompact_flowTube F hS ε
  have hKU : K ⊆ U := fun x hx => (htube hx).1
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hDf.continuousOn.sub (hDg.mono hKU))
  let C : ℝ := Max.max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : M) (hx : x ∈ K) : ‖Df x - Dg x‖ ≤ C := (hC₀ x hx).trans (le_max_left _ _)
  refine ⟨ε, μ, C, hε, hμ, hC, ?_⟩
  intro x hx hxε
  have hxK : x ∈ K := mem_flowTube_of_signedTime F f c (hbasin hx) hxε.le
  have hxN := htube hxK
  have hneg : Max.max (Df x) (Dg x) < -μ := hxN.2
  refine
    ⟨(lt_of_le_of_lt (le_max_left _ _) hneg).le, (lt_of_le_of_lt (le_max_right _ _) hneg).le, ?_⟩
  let θ := signedLevelTime F f c x
  let y := F θ x
  have hy : f y = c := signedLevelTime_hits F f c (hbasin hx)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : F t y ∈ K := ⟨(t, y), ⟨ht, hy⟩, rfl⟩
  let ℓ (t : ℝ) := f (F t y) - g (F t y)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : HasDerivAt ℓ (Df (F t y) - Dg (F t y)) t := by
    have hgpoint :=
      ((hg (F t y) (hKU (hpoint t ht))).contMDiffAt
            (hU.mem_nhds (hKU (hpoint t ht)))).mdifferentiableAt
        (by simp)
    exact
      (hasDerivAt_comp_native_integralCurve_at (hf.mdifferentiableAt (by simp)) (hcurve y)).sub
        (hasDerivAt_comp_native_integralCurve_at hgpoint (hcurve y))
  have h0 : (0 : ℝ) ∈ Set.Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hθ : -θ ∈ Set.Icc (-ε) ε := by
    constructor <;> linarith [(abs_lt.mp hxε).1, (abs_lt.mp hxε).2]
  have hmvt :=
    (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).differentiableAt)
      (fun t ht => by rw [(hd t ht).deriv]; exact hbound _ (hpoint t ht)) h0 hθ
  have hreturn : F (-θ) y = x := by
    dsimp [y]
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  simpa only [ℓ, F.map_zero_apply, hreturn, heq y hy, sub_self, sub_zero, Real.norm_eq_abs,
    abs_neg] using hmvt

theorem FlowCancellation.exists_boundary_germ_correction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {r : ℝ} (hr : 0 < r) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x ∈ U, r ≤ |signedLevelTime F f c x| → b =ᶠ[𝓝 x] g := by
  obtain ⟨ε₀, μ, C, hε₀, hμ, hC, hbounds⟩ :=
    exists_native_time_collar_bounds hU hf hg hV F hcurve hlevel hbasin heq hfc
      (fun x hx => hgneg x (hlevel hx))
  let ε := Min.min ε₀ (r / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hr)
  have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hfc
  have htime (x : M) (hx : x ∈ U) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 :=
    mvfderiv_signedLevelTime hf hV F hcurve hfc (hbasin hx)
  obtain ⟨b, hb, hbneg, hbone, -, hboff⟩ :=
    exists_native_descent_blend hU (hθ.mono hbasin) hf.contMDiffOn hg F hcurve htime hgneg hε hμ
      hC (fun x hx ht => hbounds x hx (lt_of_lt_of_le ht (min_le_left _ _)))
  refine ⟨b, hb, hbneg, ?_, fun x hx ht => hboff x hx (hεr.trans_le ht)⟩
  intro x hx
  apply hbone x (hlevel hx)
  let D (y : M) := mvfderiv 𝓘(ℝ, E) f y (V y)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  exact
    signedLevelTime_eq_zero F hf.continuous hD
      (fun y t => FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve y) t) hfc hx

theorem FlowCancellation.exists_signedTime_level_separation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hlevel : {x | f x = d} ⊆ levelBasin F f c) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, f x = d → r < |signedLevelTime F f c x| := by
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  have hS : IsCompact {x | f x = d} := (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨r, hr, hmargin⟩ :=
    exists_compact_negative_margin hS ((hθ.continuousOn.mono hlevel).abs.neg)
      (fun x hx => by
        apply neg_neg_of_pos
        apply abs_pos.mpr
        intro hz
        have hhit := signedLevelTime_hits F f c (hlevel hx)
        rw [hz, F.map_zero_apply] at hhit
        exact hcd (hhit.symm.trans hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  have hh : -|signedLevelTime F f c x| < -r := hmargin x hx
  linarith

theorem FlowCancellation.exists_boundary_correction_preserving_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hcU : {x | f x = c} ⊆ U) (hdU : {x | f x = d} ⊆ U) (hbasin : U ⊆ levelBasin F f c)
    (heq : ∀ x, f x = c → g x = f x) (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x, f x = d → b =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hsep⟩ :=
    exists_signedTime_level_separation hf hV F hcurve hcd hfc (hdU.trans hbasin)
  obtain ⟨b, hb, hbneg, hbc, hboff⟩ :=
    exists_boundary_germ_correction hU hf hg hV F hcurve hcU hbasin heq hfc hgneg hr
  exact ⟨b, hb, hbneg, hbc, fun x hx => hboff x (hdU hx) (hsep x hx).le⟩

theorem FlowCancellation.band_subset_crossingBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {c d T : ℝ} (hT : 0 < T)
    (hforward : ∀ x, f x ≤ d → f (F T x) < c) (hbackward : ∀ x, c ≤ f x → d < f (F (-T) x)) :
    f ⁻¹' Set.Icc c d ⊆ crossingBasin F f c d := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  constructor
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' hT.le hcont.continuousOn
        (show c ∈ Set.Icc (f (F T x)) (f (F 0 x)) from
          ⟨(hforward x hx.2).le, by simpa only [F.map_zero_apply] using hx.1⟩)
    exact ⟨t, ht⟩
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' (show -T ≤ (0 : ℝ) by linarith) hcont.continuousOn
        (show d ∈ Set.Icc (f (F 0 x)) (f (F (-T) x)) from
          ⟨by simpa only [F.map_zero_apply] using hx.2, (hbackward x hx.1).le⟩)
    exact ⟨t, ht⟩

theorem FlowCancellation.exists_smooth_band_height_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ (U : Set M) (g : M → ℝ),
      IsOpen U ∧
        f ⁻¹' Set.Icc c d ⊆ U ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧
            (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧ ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f := by
  let U := crossingBasin F f c d
  let g := flowBandHeight F f c d
  obtain ⟨hU, hg, hgder⟩ := smooth_flowBandHeight hf hV F hcurve hcd hc hd
  obtain ⟨T, hT, hforward, hbackward⟩ := hcross
  have hband : f ⁻¹' Set.Icc c d ⊆ U :=
    band_subset_crossingBasin F hf.continuous hT hforward hbackward
  have hcU : {x | f x = c} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx], by rw [hx]; exact hcd.le⟩)
  have hdU : {x | f x = d} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx]; exact hcd.le, by rw [hx]⟩)
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hgc (x : M) (hx : f x = c) : g x = f x :=
    (flowBandHeight_lower F hf.continuous hD hder hc hx).trans hx.symm
  have hgd (x : M) (hx : f x = d) : g x = f x :=
    (flowBandHeight_upper F hf.continuous hD hder hc hd hcd (hdU hx) hx).trans hx.symm
  obtain ⟨b, hb, hbneg, hbc, hbd⟩ :=
    exists_boundary_correction_preserving_level hU hf hg hV F hcurve hcd.ne hcU hdU
      Set.inter_subset_left hgc hc (fun x hx => (hgder x hx).2)
  have hbdval (x : M) (hx : f x = d) : b x = f x := (hbd x hx).eq_of_nhds.trans (hgd x hx)
  obtain ⟨k, hk, hkneg, hkd, hkc⟩ :=
    exists_boundary_correction_preserving_level hU hf hb hV F hcurve hcd.ne' hdU hcU
      Set.inter_subset_right hbdval hd hbneg
  refine ⟨U, k, hU, hband, hk, hkneg, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hkc x hx).trans (hbc x hx)
  · exact hkd x hx

def FlowCancellation.bandReplacement {X : Type*} (f g : X → ℝ) (c d : ℝ) (x : X) : ℝ := by
  classical exact if f x ∈ Set.Ioo c d then g x else f x

theorem FlowCancellation.bandReplacement_germ_boundary {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} {x : X} (heq : g =ᶠ[𝓝 x] f) :
    bandReplacement f g c d =ᶠ[𝓝 x] f ∧ bandReplacement f g c d =ᶠ[𝓝 x] g := by
  have hh : bandReplacement f g c d =ᶠ[𝓝 x] f := by
    filter_upwards [heq] with y hy
    simp only [bandReplacement, hy, ite_self]
  exact ⟨hh, hh.trans heq.symm⟩

theorem FlowCancellation.bandReplacement_germ_interior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∈ Set.Ioo c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_Ioo.preimage hf).mem_nhds hx] with y hy
  exact if_pos hy

theorem FlowCancellation.bandReplacement_germ_exterior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∉ Set.Icc c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] f := by
  filter_upwards [((isClosed_Icc.preimage hf).isOpen_compl).mem_nhds hx] with y hy
  exact if_neg (fun h => hy ⟨h.1.le, h.2.le⟩)

theorem FlowCancellation.bandReplacement_germ_on_closed {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∈ Set.Icc c d) : bandReplacement f g c d =ᶠ[𝓝 x] g := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).2
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).2
  exact
    bandReplacement_germ_interior hf ⟨lt_of_le_of_ne hx.1 (Ne.symm hc), lt_of_le_of_ne hx.2 hd⟩

theorem FlowCancellation.bandReplacement_germ_off_open {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∉ Set.Ioo c d) : bandReplacement f g c d =ᶠ[𝓝 x] f := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).1
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).1
  apply bandReplacement_germ_exterior hf
  intro h
  exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hc), lt_of_le_of_ne h.2 hd⟩

theorem FlowCancellation.contMDiff_bandReplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {c d : ℝ} {U : Set M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (hU : IsOpen U)
    (hband : f ⁻¹' Set.Icc c d ⊆ U) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (bandReplacement f g c d) := by
  intro x
  by_cases hx : f x ∈ Set.Icc c d
  · exact
      ((hg x (hband hx)).contMDiffAt (hU.mem_nhds (hband hx))).congr_of_eventuallyEq
        (bandReplacement_germ_on_closed hf.continuous hboundary hx)
  · exact hf.contMDiffAt.congr_of_eventuallyEq (bandReplacement_germ_exterior hf.continuous hx)

theorem FlowCancellation.mvfderiv_eq_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f g : M → ℝ} {x : M} (heq : f =ᶠ[𝓝 x] g) :
    mvfderiv 𝓘(ℝ, E) f x (V x) = mvfderiv 𝓘(ℝ, E) g x (V x) := by
  unfold mvfderiv
  rw [heq.mfderiv_eq, heq.eq_of_nhds]

theorem FlowCancellation.exists_global_band_lyapunov {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ b : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
        (∀ x, f x ∈ Set.Icc c d → mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          ∀ x, f x ∉ Set.Ioo c d → b =ᶠ[𝓝 x] f := by
  obtain ⟨U, g, hU, hband, hg, hgneg, hgerm⟩ :=
    exists_smooth_band_height_germs hf hV F hcurve hcd hc hd hcross
  refine ⟨bandReplacement f g c d, contMDiff_bandReplacement hf hg hU hband hgerm, ?_, ?_⟩
  · intro x hx
    rw [mvfderiv_eq_of_germ (V := V) (bandReplacement_germ_on_closed hf.continuous hgerm hx)]
    exact hgneg x (hband hx)
  · intro x hx
    exact bandReplacement_germ_off_open hf.continuous hgerm hx

def MorseCancellation.hessian {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : Model m →L[ℝ] Model m →L[ℝ] ℝ :=
  (2 * p.1) •
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).smulRight
        (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) +
    ∑ i,
      (2 * σ i) •
        (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).smulRight
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))

theorem MorseCancellation.hessian_apply {m : ℕ} (σ : Fin m → ℝ) (p v w : Model m) :
    hessian σ p v w = 2 * p.1 * v.1 * w.1 + ∑ i, 2 * σ i * v.2 i * w.2 i := by
  simp [hessian, mul_assoc]

theorem MorseCancellation.hasFDerivAt_differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (differential σ t) (hessian σ p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  let L (i : Fin m) : Model m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))
  have hq :=
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (((L i).hasFDerivAt (x := p)).const_mul (2 * σ i)).smul_const (L i))
  convert
      (((hx.pow 2).add_const t).smul_const (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ))).add hq using
      1 <;>
    first
    | rfl
    | ( apply ContinuousLinearMap.ext; intro v
        apply ContinuousLinearMap.ext; intro w
        simp [hessian, L, mul_assoc])

theorem MorseCancellation.fderiv_cubic_hessian {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (fderiv ℝ (cubic σ t)) p = hessian σ p := by
  rw [show fderiv ℝ (cubic σ t) = differential σ t from funext (fderiv_cubic σ t)]
  exact (hasFDerivAt_differential σ t p).fderiv

theorem MorseCancellation.hessian_bijective {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {p : Model m}
    (hp : p.1 ≠ 0) : Function.Bijective (hessian σ p) := by
  have hi : Function.Injective (hessian σ p) := by
    apply (injective_iff_map_eq_zero (hessian σ p)).mpr
    intro v hv
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hv
    have hx' : 2 * p.1 * v.1 = 0 := by simpa [hessian_apply] using hx
    have hvx : v.1 = 0 := (mul_eq_zero.mp hx').resolve_left (mul_ne_zero (by norm_num) hp)
    apply Prod.ext hvx
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hv
    have hy' : 2 * σ i * v.2 i = 0 := by simpa [hessian_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  have hd : Module.finrank ℝ (Model m) = Module.finrank ℝ (Model m →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (Model m →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = _ :=
        (LinearMap.toContinuousLinearMap : (Model m →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Model m →L[ℝ] ℝ)).finrank_eq
  exact
    ⟨hi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (hessian σ p).toLinearMap)
            hd).mp
        hi⟩

theorem MorseCancellation.cubic_isMorse {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) : MorsePerturbation.IsMorse (cubic σ t) := by
  intro p hcrit
  rw [fderiv_cubic_hessian]
  apply hessian_bijective σ hσ
  intro hp
  have h := ((critical_iff σ hσ t p).mp hcrit).1
  exact ht (by simpa [hp] using h)

theorem NativeCubicCancellation.exists_cutoff {m : ℕ} {V : Set (MorseCancellation.Model m)}
    (hV : IsOpen V) (h0 : (0 : MorseCancellation.Model m) ∈ V) :
    ∃ φ : MorseCancellation.Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ V ∧
            ∃ U : Set (MorseCancellation.Model m),
              IsOpen U ∧ (0 : MorseCancellation.Model m) ∈ U ∧ Set.EqOn φ (fun _ => 1) U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let φ : ContDiffBump (0 : MorseCancellation.Model m) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine
    ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, Metric.ball 0 (r / 4), Metric.isOpen_ball,
      Metric.mem_ball_self (by positivity), ?_⟩
  · rw [φ.tsupport_eq]
    intro p hp
    apply hball
    exact lt_of_le_of_lt hp (by change r / 2 < r; linarith)
  · intro p hp
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hp)

theorem MorseCancellationPreservation.isMorseAt_of_same_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {x : M} (hf : ManifoldMorse.IsMorseAt E f x) (heq : g =ᶠ[𝓝 x] f) :
    ManifoldMorse.IsMorseAt E g x := by
  obtain ⟨e, he, hx, hgood⟩ := hf
  refine ⟨e, he, hx, ?_⟩
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.symm.continuousAt (e.map_source hx)
    rw [ContinuousAt, e.left_inv hx] at h
    exact h
  have hc : g ∘ e.symm =ᶠ[𝓝 (e x)] f ∘ e.symm := heq.comp_tendsto ht
  rw [hc.fderiv_eq, (hc.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact hgood

theorem MorseCancellationPreservation.isMorseAt_of_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {x : M}
    (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x ≠ 0) : ManifoldMorse.IsMorseAt E g x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  refine ⟨e, he, hx, Or.inl ?_⟩
  intro hc
  exact hreg ((ManifoldMorse.mem_criticalPoints_iff hg he hx).mpr hc)

theorem MorseCancellationPreservation.isMorse_of_critical_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} (hf : ManifoldMorse.IsMorse E f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hkeep : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 → g =ᶠ[𝓝 x] f) :
    ManifoldMorse.IsMorse E g := by
  intro x
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
  · exact isMorseAt_of_same_germ (hf x) (hkeep x hx)
  · exact isMorseAt_of_regular hg hx

theorem FlowCancellation.not_critical_of_directional_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {g : M → ℝ} {x : M}
    (hneg : mvfderiv 𝓘(ℝ, E) g x (V x) < 0) : x ∉ ManifoldMorse.criticalPoints E g := by
  intro hx
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 at hx
  unfold mvfderiv at hneg
  rw [hx] at hneg
  simp at hneg

theorem FlowCancellation.remove_morse_band_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x))
    {p q : M} (hpq : p ≠ q) (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpc : f p ∈ Set.Icc c d)
    (hqc : f q ∈ Set.Icc c d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, hneg, hgerm⟩ := exists_global_band_lyapunov hf hV F hcurve hcd hc hd hcross
  have hreg (x : M) (hx : f x ∈ Set.Icc c d) : x ∉ ManifoldMorse.criticalPoints E g :=
    not_critical_of_directional_neg (hneg x hx)
  have hnew (x : M) :
    x ∈ ManifoldMorse.criticalPoints E g ↔
      x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q := by
    constructor
    · intro hx
      have hout : f x ∉ Set.Icc c d := fun h => hreg x h hx
      have he := hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)
      have hcrit : x ∈ ManifoldMorse.criticalPoints E f := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
        rw [← he.mfderiv_eq]
        exact hx
      exact ⟨hcrit, fun h => hout (h ▸ hpc), fun h => hout (h ▸ hqc)⟩
    · rintro ⟨hx, hxp, hxq⟩
      have hout : f x ∉ Set.Icc c d := fun h => (hpair x hx h).elim hxp hxq
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [(hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)).mfderiv_eq]
      exact hx
  have hmg : ManifoldMorse.IsMorse E g := by
    apply MorseCancellationPreservation.isMorse_of_critical_germs hm hg
    intro x hx
    apply hgerm x
    intro h
    exact hreg x ⟨h.1.le, h.2.le⟩ hx
  have heq :
    ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f \ { p, q } := by
    ext x
    simpa only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hnew x
  have hsub : { p, q } ⊆ ManifoldMorse.criticalPoints E f := by
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · exact Set.mem_singleton_iff.mp hx ▸ hq
  refine ⟨g, hg, hmg, ?_, hnew, hgerm⟩
  rw [heq, ← Set.ncard_pair hpq]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub (ManifoldMorse.finite_criticalPoints hf hm)

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

attribute [local instance 100] Classical.propDecidable in
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

def MorseCancellation.NativeConnectionCancellationData.Transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ}
    {f : M → ℝ} {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    Prop :=
  NativeTransversality.At 𝓘(ℝ, MorseHandle.NegativeSpace D.σ)
    𝓘(ℝ, MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.slices.Q (x, 0))
    (fun y => D.slices.P (0, y)) 0 0

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

theorem TransverseGerms.derivative_first_of_time_independent_label {A Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : ℝ × A → Z × ℝ} {f : A → Z} (hF : DifferentiableAt ℝ F 0) (hf : DifferentiableAt ℝ f 0)
    (hlabel : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2)) :
    ∀ u : ℝ × A, (fderiv ℝ F 0 u).1 = fderiv ℝ f 0 u.2 := by
  have hsnd : HasFDerivAt (fun u : ℝ × A => u.2) (ContinuousLinearMap.snd ℝ ℝ A) 0 :=
    (ContinuousLinearMap.snd ℝ ℝ A).hasFDerivAt
  have hd :
    HasFDerivAt (fun u : ℝ × A => f u.2) ((fderiv ℝ f 0).comp (ContinuousLinearMap.snd ℝ ℝ A))
      0 :=
    hf.hasFDerivAt.comp (f := fun u : ℝ × A => u.2) 0 hsnd
  have heq : fderiv ℝ (fun u : ℝ × A => (F u).1) 0 = fderiv ℝ (fun u : ℝ × A => f u.2) 0 :=
    hlabel.fderiv_eq
  rw [hF.hasFDerivAt.fst.fderiv, hd.fderiv] at heq
  intro u
  exact congrArg (fun L : (ℝ × A) →L[ℝ] Z => L u) heq

theorem TransverseGerms.transverse_labels_of_time_independent_flow_sheets {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : ℝ × A → Z × ℝ} {G : ℝ × B → Z × ℝ} {f : A → Z}
    {g : B → Z} (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G 0)
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (G u).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : Function.Surjective ((fderiv ℝ F 0).coprod (fderiv ℝ G 0))) :
    Function.Surjective ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) := by
  have hfirstF := derivative_first_of_time_independent_label hF hf hlabelF
  have hfirstG := derivative_first_of_time_independent_label hG hg hlabelG
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := htrans (z, 0)
  refine ⟨(u.2, v.2), ?_⟩
  change fderiv ℝ f 0 u.2 + fderiv ℝ g 0 v.2 = z
  rw [← hfirstF u, ← hfirstG v]
  exact congrArg Prod.fst huv

theorem TransverseGerms.transverse_labels_of_native_flow_sheets {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) (hC0 : (0 : Z × ℝ) ∈ C.source)
    (F : ℝ × A → M) (G : ℝ × B → M) (hF : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F 0)
    (hG : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) G 0) (hF0 : F 0 = C 0) (hG0 : G 0 = C 0)
    {f : A → Z} {g : B → Z} (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (C.symm (F u)).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (C.symm (G u)).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) F G 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) f g 0 0 := by
  have hFt : F 0 ∈ C.target := hF0.symm ▸ C.map_source' hC0
  have hGt : G 0 ∈ C.target := hG0.symm ▸ C.map_source' hC0
  have hFb : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, Z × ℝ) (C.symm ∘ F) 0 :=
    (C.symm.mdifferentiableAt (by simp) hFt).comp (f := F) 0 hF
  have hGb : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z × ℝ) (C.symm ∘ G) 0 :=
    (C.symm.mdifferentiableAt (by simp) hGt).comp (f := G) 0 hG
  have hcross : G 0 = F 0 := hG0.trans hF0.symm
  have ht :=
    ChartMapPerturbation.transverse_in_chart C.symm hF hG hcross hFt (htrans hcross)
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at ht
  have hl :=
    transverse_labels_of_time_independent_flow_sheets hFb.differentiableAt hGb.differentiableAt hf
      hg hlabelF hlabelG ht
  intro _
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv]
  exact hl

def MorseCancellation.NativeConnectionCancellationData.outgoingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.NegativeSpace D.σ) : M :=
  D.flow (w.1 - D.Tq)
    (D.Φq
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm (w.2, 0), D.Tq)))

def MorseCancellation.NativeConnectionCancellationData.incomingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × MorseHandle.PositiveSpace D.σ) : M :=
  D.flow (w.1 - D.Tp)
    (D.Φp
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm (0, w.2), D.Tp)))

theorem MorseCancellation.NativeConnectionCancellationData.outgoingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, E) ∞ D.outgoingSheet 0 ∧
      D.outgoingSheet 0 = D.A 0 ∧
        (fun w : ℝ × MorseHandle.NegativeSpace D.σ =>
            (D.A.symm (D.outgoingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × MorseHandle.NegativeSpace D.σ => D.slices.Q (w.2, 0)) := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hh :=
    FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero
      (fun u =>
        D.Φq
          (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
            ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq)))
      D.slices.phaseQ D.Tq D.slices.smooth_phaseQ D.slices.zero_phaseQ D.slices.formulaQ
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

theorem MorseCancellation.NativeConnectionCancellationData.incomingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) ∞ D.incomingSheet 0 ∧
      D.incomingSheet 0 = D.A 0 ∧
        (fun w : ℝ × MorseHandle.PositiveSpace D.σ =>
            (D.A.symm (D.incomingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × MorseHandle.PositiveSpace D.σ => D.slices.P (0, w.2)) := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hh :=
    FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero
      (fun u =>
        D.Φp
          (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
            ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp)))
      D.slices.phaseP D.Tp D.slices.smooth_phaseP D.slices.zero_phaseP D.slices.formulaP
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

theorem MorseCancellation.NativeConnectionCancellationData.transverse_of_native_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ)
        𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) D.outgoingSheet D.incomingSheet 0
        0) :
    D.Transverse := by
  obtain ⟨hout, hout0, houtlabel⟩ := D.outgoingSheet_properties
  obtain ⟨hin, hin0, hinlabel⟩ := D.incomingSheet_properties
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hQdiff :=
    (D.slices.Q.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.Q.open_source.mem_nhds hQ0)).differentiableAt
      (by simp)
  have hPdiff :=
    (D.slices.P.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.P.open_source.mem_nhds hP0)).differentiableAt
      (by simp)
  have hq :
    DifferentiableAt ℝ (fun x : MorseHandle.NegativeSpace D.σ => D.slices.Q (x, 0)) 0 :=
    hQdiff.comp (f := fun x : MorseHandle.NegativeSpace D.σ => (x, 0)) 0
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
          (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hp :
    DifferentiableAt ℝ (fun y : MorseHandle.PositiveSpace D.σ => D.slices.P (0, y)) 0 :=
    hPdiff.comp (f := fun y : MorseHandle.PositiveSpace D.σ => (0, y)) 0
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
          (MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hA0 : (0 : (Fin m → ℝ) × ℝ) ∈ D.A.source := by
    rw [D.slices.source]
    exact ⟨D.slices.zero_domain, Set.mem_univ _⟩
  exact
    TransverseGerms.transverse_labels_of_native_flow_sheets D.A hA0 D.outgoingSheet
      D.incomingSheet (hout.mdifferentiableAt (by simp)) (hin.mdifferentiableAt (by simp)) hout0
      hin0 hq hp houtlabel hinlabel htrans

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.NativeConnectionCancellationData.outgoing_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.outgoingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × MorseHandle.NegativeSpace D.σ => P ((w.2, 0), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q) ↔ w.1.2 = 0 := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  let S := fun u =>
    D.Φq
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm u, D.Tq))
  have hbasin (u) (hu : u ∈ D.slices.Q.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atBot (𝓝 q) ↔ u.2 = 0 :=
    MorseCancellation.outgoing_cubic_slice_basin D.σ D.signs (1 / 2) D.Tq D.Φq D.flow D.basinQ u
      (D.boxQ (D.slices.sliceQ u hu))
  obtain ⟨P, -, h0P, hP0, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero S D.slices.phaseQ D.Tq D.slices.smooth_phaseQ
      D.slices.zero_phaseQ D.slices.formulaQ
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q))
      (fun t y => MorseCancellation.flow_time_atBot_limit_iff D.flow t y q) (fun u => u.2 = 0) hbasin
  have heq :=
    FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.Q.open_source hQ0 D.flow S
      D.Tq hformula
      (ContinuousLinearMap.inl ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hP0, ?_, hplane⟩
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply] using heq

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.NativeConnectionCancellationData.incoming_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (MorseHandle.NegativeSpace D.σ × MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.incomingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × MorseHandle.PositiveSpace D.σ => P ((0, w.2), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p) ↔ w.1.1 = 0 := by
  have hflow :=
    FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  let S := fun u =>
    D.Φp
      (MorseCancellation.cubicFlowCylinder D.σ (1 / 2)
        ((MorseHandle.splitCoordinates D.σ).symm u, D.Tp))
  have hbasin (u) (hu : u ∈ D.slices.P.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atTop (𝓝 p) ↔ u.1 = 0 :=
    MorseCancellation.incoming_cubic_slice_basin D.σ (1 / 2) D.Tp D.Φp D.flow D.basinP u
      (D.boxP (D.slices.sliceP u hu))
  obtain ⟨P, -, h0P, hPzero, hformula, hplane⟩ :=
    FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero S D.slices.phaseP D.Tp D.slices.smooth_phaseP
      D.slices.zero_phaseP D.slices.formulaP
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p))
      (fun t y => MorseCancellation.flow_time_atTop_limit_iff D.flow t y p) (fun u => u.1 = 0) hbasin
  have heq :=
    FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.P.open_source hP0 D.flow S
      D.Tp hformula
      (ContinuousLinearMap.inr ℝ (MorseHandle.NegativeSpace D.σ)
        (MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hPzero, ?_, hplane⟩
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply] using heq

theorem TransverseGerms.native_transversality_of_sheet_factorizations
    {A B U V E HU HV HE X Y M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace HE]
    {I : ModelWithCorners ℝ U HU} {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y] [ChartedSpace HV Y]
    [TopologicalSpace M] [ChartedSpace HE M] {F : X → M} {G : Y → M} {f : A → M} {g : B → M}
    {u : X → A} {v : Y → B} {x : X} {y : Y} (hf : MDifferentiableAt 𝓘(ℝ, A) J f 0)
    (hg : MDifferentiableAt 𝓘(ℝ, B) J g 0) (hu : MDifferentiableAt I 𝓘(ℝ, A) u x)
    (hv : MDifferentiableAt I' 𝓘(ℝ, B) v y) (hu0 : u x = 0) (hv0 : v y = 0)
    (hF : F =ᶠ[𝓝 x] (f ∘ u)) (hG : G =ᶠ[𝓝 y] (g ∘ v)) (hcross : G y = F x)
    (htrans : NativeTransversality.At I I' J F G x y) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) J f g 0 0 := by
  have hfx : MDifferentiableAt 𝓘(ℝ, A) J f (u x) := hu0 ▸ hf
  have hgy : MDifferentiableAt 𝓘(ℝ, B) J g (v y) := hv0 ▸ hg
  have hFd :
    (mfderiv I J F x : U →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, A) J f 0 : A →L[ℝ] E).comp (mfderiv I 𝓘(ℝ, A) u x) := by
    have heq : (mfderiv I J F x : U →L[ℝ] E) = mfderiv I J (f ∘ u) x := hF.mfderiv_eq
    rw [heq, mfderiv_comp x hfx hu, hu0]
  have hGd :
    (mfderiv I' J G y : V →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, B) J g 0 : B →L[ℝ] E).comp (mfderiv I' 𝓘(ℝ, B) v y) := by
    have heq : (mfderiv I' J G y : V →L[ℝ] E) = mfderiv I' J (g ∘ v) y := hG.mfderiv_eq
    rw [heq, mfderiv_comp y hgy hv, hv0]
  intro _ z
  obtain ⟨⟨a, b⟩, hab⟩ := htrans hcross z
  refine ⟨(mfderiv I 𝓘(ℝ, A) u x a, mfderiv I' 𝓘(ℝ, B) v y b), ?_⟩
  rw [hFd, hGd] at hab
  exact hab

theorem TransverseGerms.exists_native_plane_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (fun y => P (L (u y))) := by
  let u : X → A := fun y => R (P.symm (F y))
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hi := (P.symm.mdifferentiableAt (by simp) hxt).comp x hF
  have hu : MDifferentiableAt I 𝓘(ℝ, A) u x := R.differentiableAt.mdifferentiableAt.comp x hi
  have hu0 : u x = 0 := by
    change R (P.symm (F x)) = 0
    have hi0 : P.symm (P 0) = 0 := P.left_inv' hP0
    rw [hx, hi0, map_zero]
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hplane] with y hy hplaneY
  obtain ⟨a, ha⟩ := hplaneY
  change F y = P (L (R (P.symm (F y))))
  rw [ha, hRL]
  exact (P.right_inv' hy).symm.trans (congrArg P ha)

theorem TransverseGerms.exists_native_plane_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) {f : A → M}
    (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  obtain ⟨u, hu, hu0, hfactor⟩ := exists_native_plane_factorization P hP0 L R hRL hF hx hplane
  have hut : Filter.Tendsto u (𝓝 x) (𝓝 (0 : A)) := hu0 ▸ hu.continuousAt
  have hcomp := hmodel.comp_tendsto hut
  exact ⟨u, hu, hu0, hfactor.trans hcomp.symm⟩

theorem TransverseGerms.exists_native_basin_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0) (Basin : M → Prop)
    (hbasin : ∀ z ∈ P.source, Basin (P z) → ∃ a, z = L a) (hFbasin : ∀ᶠ y in 𝓝 x, Basin (F y))
    {f : A → M} (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a := by
    filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hFbasin] with y hy hby
    have hb : Basin (P (P.symm (F y))) := (P.right_inv' hy).symm ▸ hby
    exact hbasin (P.symm (F y)) (P.map_target' hy) hb
  exact exists_native_plane_sheet_factorization P hP0 L R hRL hF hx hplane hmodel

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.NativeConnectionCancellationData.outgoing_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atBot (𝓝 q)) :
    ∃ u : X → ℝ × MorseHandle.NegativeSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.outgoingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.outgoing_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × A) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inl ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ A)).prod
      (ContinuousLinearMap.fst ℝ ℝ A)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × A) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × A) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.1), ?_⟩
    exact Prod.ext (Prod.ext rfl hz) rfl
  exact
    TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q)) hp
      hbasin hmodel

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.NativeConnectionCancellationData.incoming_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atTop (𝓝 p)) :
    ∃ u : X → ℝ × MorseHandle.PositiveSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.incomingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.incoming_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × B) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inr ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ B)).prod
      (ContinuousLinearMap.fst ℝ ℝ B)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × B) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × B) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.2), ?_⟩
    exact Prod.ext (Prod.ext hz rfl) rfl
  exact
    TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p)) hp
      hbasin hmodel

theorem MorseCancellation.NativeConnectionCancellationData.transverse_of_native_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y) : D.Transverse := by
  obtain ⟨u, hu, hu0, hFu⟩ := D.outgoing_basin_factorization hF hx hFbasin
  obtain ⟨v, hv, hv0, hGv⟩ := D.incoming_basin_factorization hG hy hGbasin
  apply D.transverse_of_native_sheets
  exact
    TransverseGerms.native_transversality_of_sheet_factorizations
      (D.outgoingSheet_properties.1.mdifferentiableAt (by simp))
      (D.incomingSheet_properties.1.mdifferentiableAt (by simp)) hu hv hu0 hv0 hFu hGv
      (hy.trans hx.symm) htrans

theorem MorseCancellation.NativeConnectionCancellationData.cancel_of_transverse_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancellation.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc c d → z = p ∨ z = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ z,
                z ∈ ManifoldMorse.criticalPoints E g ↔
                  z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
              ∀ z, f z ∉ Set.Ioo c d → g =ᶠ[𝓝 z] f :=
  D.cancel (D.transverse_of_native_basin_sheets hF hG hx hy hFbasin hGbasin htrans) hf hm hinj hp
    hq hpq hc hd hpair

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_unique_connection_of_transverse_basin_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q z : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x)
    {S : X → M} {T : Y → M} {x : X} {y : Y} (hS : MDifferentiableAt I 𝓘(ℝ, E) S x)
    (hT : MDifferentiableAt I' 𝓘(ℝ, E) T y) (hS0 : S x = z) (hT0 : T y = z)
    (hSbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (S u)) Filter.atBot (𝓝 q))
    (hTbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (T u)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) S T x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨D, -, hgeometry, t₀, ht₀⟩ :=
    exists_native_connection_cancellation_data cp cq hf hdim hindex V hV hzero hdesc F hF hpc hqc
      hpq hc hd hpair hp hq hunique heqp heqq
  let τ := SmoothODE.nativeFlowTimeDiffeomorph_of_field hV F hF t₀
  have hτ (u : M) : τ u = F t₀ u := rfl
  have hS' : MDifferentiableAt I 𝓘(ℝ, E) (τ ∘ S) x :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp x hS
  have hT' : MDifferentiableAt I' 𝓘(ℝ, E) (τ ∘ T) y :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp y hT
  have hS0' : (τ ∘ S) x = D.A 0 := by rw [Function.comp_apply, hτ, hS0, ht₀]
  have hT0' : (τ ∘ T) y = D.A 0 := by rw [Function.comp_apply, hτ, hT0, ht₀]
  have hSb : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => D.flow t ((τ ∘ S) u)) Filter.atBot (𝓝 q) := by
    filter_upwards [hSbasin] with u hu
    apply ((hgeometry ((τ ∘ S) u)).2.2 q).mpr
    exact (flow_time_atBot_limit_iff F t₀ (S u) q).mpr hu
  have hTb : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => D.flow t ((τ ∘ T) u)) Filter.atTop (𝓝 p) := by
    filter_upwards [hTbasin] with u hu
    apply ((hgeometry ((τ ∘ T) u)).2.1 p).mpr
    exact (flow_time_atTop_limit_iff F t₀ (T u) p).mpr hu
  have ht : NativeTransversality.At I I' 𝓘(ℝ, E) (τ ∘ S) (τ ∘ T) x y :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff τ.toPartialDiffeomorph
          hS hT (hT0.trans hS0.symm) (Set.mem_univ _)).mp
      htrans
  exact
    D.cancel_of_transverse_basin_sheets hS' hT' hS0' hT0' hSb hTb ht hf hm hinj hpc hqc hpq hc hd
      hpair

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_of_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (z : M) → TangentSpace 𝓘(ℝ, E) z)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0)
    (hdesc : ∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0)
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) {l u a b c : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (ha : a < c) (hb : c < b) (hpc' : f p < c) (hqc' : c < f q)
    (hband : ∀ z, f z ∈ Set.Icc a b → z ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f)
    (heqp : ∀ᶠ z in 𝓝 p, V z = cp.descentField z) (heqq : ∀ᶠ z in 𝓝 q, V z = cq.descentField z) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { z : M // f z = c } { z : M // f z = c } ∞,
      SupportedDiffeomorph.IsotopicToIdentity D →
        {z : { w : M // f w = c } |
                Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
                  Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)}.ncard =
            1 →
          ∀ (α : X → { z : M // f z = c }) (β : Y → { z : M // f z = c }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
                β y = α x →
                  NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
                    (∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => F t (α z)) Filter.atBot (𝓝 q)) →
                      (∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => F t (D (β z))) Filter.atTop (𝓝 p)) →
                        ∃ g : M → ℝ,
                          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                            ManifoldMorse.IsMorse E g ∧
                              (ManifoldMorse.criticalPoints E g).ncard + 2 =
                                  (ManifoldMorse.criticalPoints E f).ncard ∧
                                (∀ z,
                                    z ∈ ManifoldMorse.criticalPoints E g ↔
                                      z ∈ ManifoldMorse.criticalPoints E f ∧
                                        z ≠ p ∧ z ≠ q) ∧
                                  ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro D hD hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain
    ⟨r, C, W, V', H, G, -, -, -, -, -, -, hgeometry, hV', hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf hV hdesc F hF ha hb
      hband hreg (α x) D hD
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy F H G Subtype.val D
      (fun z => (hgeometry z).2.1) (fun z => (hgeometry z).2.2) hend hleft hright
  have hαb : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => G t (α z)) Filter.atBot (𝓝 q) := by
    filter_upwards [hαbasin] with z hz
    exact (hback (α z) q).mpr hz
  have hβb : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => G t (β z)) Filter.atTop (𝓝 p) := by
    filter_upwards [hβbasin] with z hz
    exact (hforward (β z) p).mpr hz
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hαq : Filter.Tendsto (fun t => F t (α x)) Filter.atBot (𝓝 q) := hαbasin.self_of_nhds
  have hαp : Filter.Tendsto (fun t => F t (D (α x))) Filter.atTop (𝓝 p) := by
    rw [← hcross]
    exact hβbasin.self_of_nhds
  have hαeq : α x = z₀ := by
    have hh :
      α x ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hαq, hαp⟩
    rw [hz₀] at hh
    exact Set.mem_singleton_iff.mp hh
  have huniq (z : { w : M // f w = c }) (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hzp : Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)) : z = α x := by
    have hh :
      z ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hzq, hzp⟩
    rw [hz₀] at hh
    exact (Set.mem_singleton_iff.mp hh).trans hαeq.symm
  obtain ⟨hqG, hpG, huniqueG⟩ :=
    FlowSuspension.unique_connection_of_level_basin_intersection F G hf.continuous hqc'
      hpc' D (fun z => hback z q) (fun z => hforward z p) (α x) hαq hαp huniq
  obtain ⟨hS, hT, hS0, hT0, hSb, hTb, ht⟩ :=
    FlowSuspension.native_transverse_basin_tubes_of_level_maps hf hreg hV' G hG
      (fun z hz => hneg z (hreg z hz)) α β x y hα hβ hcross htrans hαb hβb
  have hgermp : ∀ᶠ z in 𝓝 p, V' z = cp.descentField z := by
    filter_upwards [hgerms p hpc, heqp] with z hz hz'
    exact hz.trans hz'
  have hgermq : ∀ᶠ z in 𝓝 q, V' z = cq.descentField z := by
    filter_upwards [hgerms q hqc, heqq] with z hz hz'
    exact hz.trans hz'
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V' hV'
      (fun z hz => (hzeros z).mpr (hzero z hz)) hneg G hG hinj hpc hqc (hpc'.trans hqc') hl hu
      hpair hpG hqG huniqueG hgermp hgermq hS hT hS0 hT0 hSb hTb ht

def MorseCancellation.nativeMorseCount (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (k : ℕ) : ℕ :=
  {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.ncard

theorem MorseCancellation.indexed_criticalPoints_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    {z : M | z ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hzg, hindex⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hzg
    rw [nativeMorseIndex_congr_germ (hkeep z hzg)] at hindex
    exact ⟨⟨hzf, hindex⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hindex⟩, hzp, hzq⟩
    have hzg := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hzg, (nativeMorseIndex_congr_germ (hkeep z hzg)).trans hindex⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeMorseCount_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, if_pos hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, if_neg hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_after_pair_removal hcrit hkeep k]
  exact (Nat.add_assoc _ _ _).trans hc

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeMorseCount_adjacent_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ ManifoldMorse.criticalPoints E g ↔
          z ∈ ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) {k : ℕ}
    (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_after_pair_removal hfinite hp hq hpq hcrit hkeep
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

end Mathoverflow1973

end
