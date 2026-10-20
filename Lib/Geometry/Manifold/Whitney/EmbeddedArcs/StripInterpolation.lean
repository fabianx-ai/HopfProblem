/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips.NormalCoordinate
import Lib.Geometry.Manifold.Whitney.CleanStrips.StripModel
import Lib.Geometry.Manifold.Whitney.FrameField.FrameExtension

/-!
# Strips with prescribed germs at the two ends

A strip is a two-parameter map whose centre line is a given curve; its normal derivative is the
derivative across the centre line. Two germs of strips at the two ends with the prescribed centre
line and normal derivative are interpolated by one globally smooth strip
(`StripCoordinates.exists_smooth_strip_matching_germs`); a strip with nowhere-vanishing normal
derivative is a clean immersive embedding of a thin rectangle around the centre line
(`StripCoordinates.exists_clean_strip_neighborhood`); together, two local germs are joined by a
clean embedded strip keeping both germs
(`StripCoordinates.exists_clean_strip_matching_local_germs`), also inside an ambient chart clean for
a sheet (`exists_clean_strip_matching_germs_in_chart`).

These strips are the thickenings of the arcs in the Whitney trick, cf. Milnor, *Lectures on the
h-cobordism theorem*, §6.

## Tags

strip, interpolation, embedding
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- Two germs of strips at the two ends, with the prescribed centre line and normal derivative, are
interpolated by a globally smooth strip having that centre line and that normal derivative
everywhere. -/
theorem StripCoordinates.exists_smooth_strip_matching_germs {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center)
    (hn₀ : normalDerivative F₀ =ᶠ[𝓝 (0 : ℝ)] v) (hn₁ : normalDerivative F₁ =ᶠ[𝓝 (1 : ℝ)] v) :
    ∃ F : (ℝ × ℝ) → Space A B,
      ContDiff ℝ ∞ F ∧
        (∀ t, F (t, 0) = StripCoordinates.center t) ∧
          (∀ t, normalDerivative F t = v t) ∧ (F =ᶠ[𝓝 (0, 0)] F₀) ∧ (F =ᶠ[𝓝 (1, 0)] F₁) := by
  have hgood₀ :
    {t : ℝ |
        F₀ (t, 0) = StripCoordinates.center t ∧ normalDerivative F₀ t = v t ∧ t < 1 / 3} ∈
      𝓝 (0 : ℝ) := by
    filter_upwards [hc₀, hn₀, Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  have hgood₁ :
    {t : ℝ |
        F₁ (t, 0) = StripCoordinates.center t ∧ normalDerivative F₁ t = v t ∧ 2 / 3 < t} ∈
      𝓝 (1 : ℝ) := by
    filter_upwards [hc₁, hn₁, Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  obtain ⟨β₀, _, hβ₀⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (0 : ℝ)).mem_iff.mp hgood₀
  obtain ⟨β₁, _, hβ₁⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (1 : ℝ)).mem_iff.mp hgood₁
  have hcβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : F₀ (t, 0) = StripCoordinates.center t :=
    (hβ₀ (subset_tsupport β₀ ht)).1
  have hcβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : F₁ (t, 0) = StripCoordinates.center t :=
    (hβ₁ (subset_tsupport β₁ ht)).1
  have hnβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : normalDerivative F₀ t = v t :=
    (hβ₀ (subset_tsupport β₀ ht)).2.1
  have hnβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : normalDerivative F₁ t = v t :=
    (hβ₁ (subset_tsupport β₁ ht)).2.1
  have hβ₀zero : (β₀ : ℝ → ℝ) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (1 : ℝ) < 1 / 3 := (hβ₀ ht).2.2
    norm_num at hbad
  have hβ₁zero : (β₁ : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (2 / 3 : ℝ) < 0 := (hβ₁ ht).2.2
    norm_num at hbad
  let F := blend v F₀ F₁ β₀ β₁
  have hF : ContDiff ℝ ∞ F :=
    contDiff_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff
  refine
    ⟨F, hF, blend_zero hcβ₀ hcβ₁,
      normalDerivative_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff hnβ₀ hnβ₁, ?_,
      ?_⟩
  · have hp : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp β₀.eventuallyEq_one, hp hβ₁zero] with p hp₀ hp₁
    exact blend_eq_left hp₀ hp₁
  · have hp : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (1, 0)) (𝓝 1) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp hβ₀zero, hp β₁.eventuallyEq_one] with p hp₀ hp₁
    exact blend_eq_right hp₀ hp₁

/-- A strip with nowhere-vanishing normal derivative along the centre line is an embedding on a thin
rectangle around it, is clean (the sheet is the zero set of the normal coordinate) and immersive
there. -/
theorem StripCoordinates.exists_clean_strip_neighborhood {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (hD : ∀ t, normalDerivative F t = v t)
    (hn : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t ≠ 0) {O : Set (Space A B)} (hO : IsOpen O)
    (hcenterO : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              Set.InjOn F W ∧
                Set.MapsTo F W O ∧
                  (∀ p ∈ W, Function.Injective (fderiv ℝ F p)) ∧
                    (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
                      Topology.IsClosedEmbedding
                        (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => F p) := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have hFK : Set.InjOn F K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := by
      simpa only [hc, StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.1) heq
    exact Prod.ext htu rfl
  have hiF : ∀ p ∈ K, Function.Injective (fderiv ℝ F p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    apply injective_fderiv_at_center (hF.contDiffAt.differentiableAt (by simp)) hc
    rw [hD t]
    exact hn t ht
  have hiFM : ∀ p ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Space A B) F p) := by
    intro p hp
    rw [mfderiv_eq_fderiv]
    exact hiF p hp
  obtain ⟨V, hV, hKV, hinjV⟩ :=
    ManifoldImmersion.exists_open_injOn_near_compact hF.contMDiff hK hFK hiFM
  let Q := detector v F
  have hQ : ContDiff ℝ ∞ Q := contDiff_detector hv hF
  have hQK : Set.InjOn Q K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := congrArg Prod.fst heq
    exact Prod.ext htu rfl
  have hiQ : ∀ p ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) Q p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    rw [mfderiv_eq_fderiv]
    exact injective_fderiv_detector_at_center hv hF hc hD (hn t ht)
  obtain ⟨T, hT, hKT, hinjT⟩ :=
    ManifoldImmersion.exists_open_injOn_near_compact hQ.contMDiff hK hQK hiQ
  let I := {p : ℝ × ℝ | Function.Injective (fderiv ℝ F p)}
  have hI : IsOpen I :=
    ContinuousLinearMap.isOpen_injective.preimage (hF.continuous_fderiv (by simp))
  let W := ((V ∩ T) ∩ I) ∩ (F ⁻¹' O ∩ (fun p : ℝ × ℝ => (p.1, 0)) ⁻¹' T)
  have hW : IsOpen W :=
    ((hV.inter hT).inter hI).inter
      ((hO.preimage hF.continuous).inter (hT.preimage (continuous_fst.prodMk continuous_const)))
  have hKW : K ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have hpK : (t, (0 : ℝ)) ∈ K := ⟨ht, rfl⟩
    refine ⟨⟨⟨hKV hpK, hKT hpK⟩, hiF _ hpK⟩, ⟨?_, hKT hpK⟩⟩
    change F (t, 0) ∈ O
    rw [hc]
    exact hcenterO ht
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hW hKW
  have hrect : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  have hinjW : Set.InjOn F W := hinjV.mono (fun _ hp => hp.1.1.1)
  refine ⟨ε, hε, W, hW, hrect, hinjW, fun _ hp => hp.2.1, fun _ hp => hp.1.2, ?_, ?_⟩
  · rintro ⟨t, s⟩ hp
    constructor
    · intro hz
      have heq : Q (t, s) = Q (t, 0) := by
        change detector v F (t, s) = detector v F (t, 0)
        rw [detector_zero hc]
        change (t, ⟪v t, (F (t, s)).2⟫_ℝ) = (t, 0)
        rw [hz, inner_zero_right]
      exact congrArg Prod.snd (hinjT hp.1.1.2 hp.2.2 heq)
    · intro hs
      change s = 0 at hs
      subst s
      rw [hc]
      rfl
  · let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply (hF.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjW (hrect p.property) (hrect q.property) hpq)

/-- The normal derivative of a smooth strip is smooth. -/
theorem StripCoordinates.contDiff_normalDerivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (normalDerivative F) :=
  ((hF.snd.fderiv_right (by simp)).clm_apply contDiff_const).comp
    (contDiff_id.prodMk contDiff_const)

/-- The normal derivative at a parameter depends only on the germ of the strip at the corresponding
centre point. -/
theorem StripCoordinates.normalDerivative_congr_germ {A B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {F G : (ℝ × ℝ) → Space A B} {t : ℝ} (heq : F =ᶠ[𝓝 (t, 0)] G) :
    normalDerivative F t = normalDerivative G t := by
  have heq' : (fun p => (F p).2) =ᶠ[𝓝 (t, (0 : ℝ))] (fun p => (G p).2) := by
    filter_upwards [heq] with p hp
    exact congrArg Prod.snd hp
  have hd : fderiv ℝ (fun p => (F p).2) (t, 0) = fderiv ℝ (fun p => (G p).2) (t, 0) :=
    heq'.fderiv_eq
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] B => L (0, 1)) hd

/-- Combination of the previous two statements: two local germs with nonzero normal derivative at
the ends are joined by a globally smooth strip which keeps both germs and is a clean embedding
of a thin rectangle. -/
theorem StripCoordinates.exists_clean_strip_matching_local_germs {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {U₀ U₁ : Set (ℝ × ℝ)} (hF₀ : ContDiffOn ℝ ∞ F₀ U₀) (hF₁ : ContDiffOn ℝ ∞ F₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center)
    (hn₀ : normalDerivative F₀ 0 ≠ 0) (hn₁ : normalDerivative F₁ 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) {O : Set (Space A B)} (hO : IsOpen O)
    (hcenterO : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) O) :
    ∃ F : (ℝ × ℝ) → Space A B,
      ContDiff ℝ ∞ F ∧
        (∀ t, F (t, 0) = StripCoordinates.center t) ∧
          (F =ᶠ[𝓝 (0, 0)] F₀) ∧
            (F =ᶠ[𝓝 (1, 0)] F₁) ∧
              ∃ ε : ℝ,
                0 < ε ∧
                  ∃ W : Set (ℝ × ℝ),
                    IsOpen W ∧
                      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
                        Set.InjOn F W ∧
                          Set.MapsTo F W O ∧
                            (∀ p ∈ W, Function.Injective (fderiv ℝ F p)) ∧
                              (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
                                Topology.IsClosedEmbedding
                                    (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => F p) ∧
                                  (∀ t, normalDerivative F t ≠ 0) := by
  obtain ⟨G₀, hG₀, heq₀⟩ := exists_smooth_extension_near_point hF₀.contMDiffOn hU₀ h0U₀
  obtain ⟨G₁, hG₁, heq₁⟩ := exists_smooth_extension_near_point hF₁.contMDiffOn hU₁ h1U₁
  have hnG₀ : normalDerivative G₀ 0 ≠ 0 := by rwa [normalDerivative_congr_germ heq₀]
  have hnG₁ : normalDerivative G₁ 1 ≠ 0 := by rwa [normalDerivative_congr_germ heq₁]
  obtain ⟨v, hv, hvne, hv₀, hv₁⟩ :=
    DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs
      (contDiff_normalDerivative hG₀.contDiff).contDiffOn
      (contDiff_normalDerivative hG₁.contDiff).contDiffOn isOpen_univ isOpen_univ (Set.mem_univ _)
      (Set.mem_univ _) hnG₀ hnG₁ hdim
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center := by
    have hi : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₀.comp_tendsto hi).trans hc₀
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center := by
    have hi : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 1) (𝓝 (1, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₁.comp_tendsto hi).trans hc₁
  obtain ⟨F, hF, hc, hD, hFG₀, hFG₁⟩ :=
    exists_smooth_strip_matching_germs hv hG₀.contDiff hG₁.contDiff hcG₀ hcG₁ hv₀.symm hv₁.symm
  obtain ⟨ε, hε, W, hW, hrect, hinj, hmap, hi, hclean, hemb⟩ :=
    exists_clean_strip_neighborhood hv hF hc hD (fun t _ => hvne t) hO hcenterO
  exact
    ⟨F, hF, hc, hFG₀.trans heq₀, hFG₁.trans heq₁, ε, hε, W, hW, hrect, hinj, hmap, hi, hclean,
      hemb, fun t => by rw [hD t]; exact hvne t⟩

/-- Chart form of the strip interpolation: inside an ambient chart clean for a sheet, two germs at
the two ends are joined by a clean embedded strip along the centre line with nowhere-vanishing
normal derivative. -/
theorem exists_clean_strip_matching_germs_in_chart {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M
        ∞)
    (hline : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) Φ.source) {S : Set M}
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ S ↔ q.2 = 0) {k₀ k₁ : (ℝ × ℝ) → M} {U₀ U₁ : Set (ℝ × ℝ)}
    (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t))
    (hc₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t))
    (hn₀ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₀) (0, 0) (0, 1) ≠ 0)
    (hn₁ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (1, 0) (0, 1) ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              ∃ k : (ℝ × ℝ) → M,
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
                  Set.InjOn k W ∧
                    Set.MapsTo k W Φ.target ∧
                      Topology.IsClosedEmbedding
                          (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                          (∀ p ∈ W, k p ∈ S ↔ p.2 = 0) ∧
                            (∀ t, k (t, 0) = Φ (StripCoordinates.center t)) ∧
                              (k =ᶠ[𝓝 (0, 0)] k₀) ∧
                                (k =ᶠ[𝓝 (1, 0)] k₁) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                    fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k) (t, 0)
                                        (0, 1) ≠
                                      0) := by
  let C₀ := U₀ ∩ k₀ ⁻¹' Φ.target
  let C₁ := U₁ ∩ k₁ ⁻¹' Φ.target
  have hC₀ : IsOpen C₀ := hk₀.continuousOn.isOpen_inter_preimage hU₀ Φ.open_target
  have hC₁ : IsOpen C₁ := hk₁.continuousOn.isOpen_inter_preimage hU₁ Φ.open_target
  have hline₀ : StripCoordinates.center (0 : ℝ) ∈ Φ.source := hline (by simp)
  have hline₁ : StripCoordinates.center (1 : ℝ) ∈ Φ.source := hline (by simp)
  have h0C₀ : (0, 0) ∈ C₀ := by
    refine ⟨h0U₀, ?_⟩
    change k₀ (0, 0) ∈ Φ.target
    rw [hc₀.eq_of_nhds]
    exact Φ.map_source' hline₀
  have h1C₁ : (1, 0) ∈ C₁ := by
    refine ⟨h1U₁, ?_⟩
    change k₁ (1, 0) ∈ Φ.target
    rw [hc₁.eq_of_nhds]
    exact Φ.map_source' hline₁
  let G₀ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₀
  let G₁ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₁
  have hG₀ : ContDiffOn ℝ ∞ G₀ C₀ :=
    (Φ.contMDiffOn_invFun.comp (hk₀.mono Set.inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hG₁ : ContDiffOn ℝ ∞ G₁ C₁ :=
    (Φ.contMDiffOn_invFun.comp (hk₁.mono Set.inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hc₀, hsource] with t hkt ht
    change Φ.invFun (k₀ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    filter_upwards [hc₁, hsource] with t hkt ht
    change Φ.invFun (k₁ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  obtain
    ⟨F, hF, hFc, hFG₀, hFG₁, ε, hε, W, hW, hrect, hinjF, hsource, hiF, hcleanF, _, hnormalF⟩ :=
    StripCoordinates.exists_clean_strip_matching_local_germs hG₀ hG₁ hC₀ hC₁ h0C₀ h1C₁ hcG₀ hcG₁
      hn₀ hn₁ hdim Φ.open_source hline
  let k := Φ ∘ F
  have hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W :=
    Φ.contMDiffOn_toFun.comp hF.contMDiff.contMDiffOn hsource
  have hinjk : Set.InjOn k W := by
    intro p hp q hq heq
    exact hinjF hp hq (Φ.toPartialEquiv.injOn (hsource hp) (hsource hq) heq)
  have hemb : Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) := by
    let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply
      (continuousOn_iff_continuous_domRestrict.mp (hk.continuousOn.mono hrect)).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hrect p.property) (hrect q.property) hpq)
  refine
    ⟨ε, hε, W, hW, hrect, k, hk, hinjk, fun _ hp => Φ.map_source' (hsource hp), hemb, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · intro p hp
    have hiFM : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, StripCoordinates.Space A B) F p) := by
      rw [mfderiv_eq_fderiv]
      exact hiF p hp
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Φ ∘ F) p)
    rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) (hsource hp))
        (hF.contMDiff.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ (hsource hp)).1.comp hiFM
  · intro p hp
    exact (hclean (F p) (hsource hp)).trans (hcleanF p hp)
  · intro t
    exact congrArg Φ (hFc t)
  · filter_upwards [hFG₀, hC₀.mem_nhds h0C₀] with p hFp hp
    change Φ (F p) = k₀ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · filter_upwards [hFG₁, hC₁.mem_nhds h1C₁] with p hFp hp
    change Φ (F p) = k₁ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · intro t ht
    have hp : (t, (0 : ℝ)) ∈ W := hrect ⟨ht, ⟨neg_nonpos.mpr hε.le, hε.le⟩⟩
    have heq : (TransverseCoordinates.normalCoordinate Φ ∘ k) =ᶠ[𝓝 (t, 0)] (fun p => (F p).2) := by
      filter_upwards [hW.mem_nhds hp] with p hpW
      change (Φ.invFun (Φ (F p))).2 = (F p).2
      rw [Φ.left_inv' (hsource hpW)]
    rw [heq.fderiv_eq]
    exact hnormalF t

end
