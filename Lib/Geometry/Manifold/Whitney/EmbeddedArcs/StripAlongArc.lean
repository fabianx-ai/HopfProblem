/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.CornerCharts
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.TransverseCoordinates
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripInterpolation

/-!
# A clean strip along an arc with prescribed corners

If a strip meets a closed set exactly in its two endpoint fibres near the ends and nowhere in the
open middle, it meets it exactly there on a thin rectangle
(`exists_strip_neighborhood_with_exact_endpoint_contacts`). Along an embedded arc in a sheet,
transverse to a second sheet at both endpoints with prescribed corner parametrisations, there is a
clean embedded strip with the given corner germs meeting the second sheet only at the corners
(`exists_strip_along_arc_matching_parametrized_corners`), packaged with its strip normal data as a
clean strip patch between two clean corner patches
(`exists_cleanStripPatch_of_tubular_arc_corners`).

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

strip, Whitney trick, transversality
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- If a strip meets a closed set exactly at its two endpoint fibres near the ends and nowhere in
the open middle of the centre line, then it meets it exactly in those two fibres on a thin
rectangle. -/
theorem exists_strip_neighborhood_with_exact_endpoint_contacts {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ k W) (hW : IsOpen W)
    (hKW : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ W) {B : Set M} (hB : IsClosed B)
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, k (t, 0) ∉ B)
    (hc₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 0)
    (hc₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 1) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U ∧
              U ⊆ W ∧ ∀ p ∈ U, k p ∈ B ↔ p.1 = 0 ∨ p.1 = 1 := by
  obtain ⟨V₀, hV₀sub, hV₀, h0V₀⟩ := _root_.mem_nhds_iff.mp hc₀
  obtain ⟨V₁, hV₁sub, hV₁, h1V₁⟩ := _root_.mem_nhds_iff.mp hc₁
  let L := V₀ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Iio (1 / 3)
  let R := V₁ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioi (2 / 3)
  let C := (W ∩ k ⁻¹' Bᶜ) ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioo 0 1
  have hL : IsOpen L := hV₀.inter (isOpen_Iio.preimage continuous_fst)
  have hR : IsOpen R := hV₁.inter (isOpen_Ioi.preimage continuous_fst)
  have hC : IsOpen C :=
    (hk.continuousOn.isOpen_inter_preimage hW hB.isOpen_compl).inter
      (isOpen_Ioo.preimage continuous_fst)
  let U := W ∩ ((L ∪ R) ∪ C)
  have hU : IsOpen U := hW.inter ((hL.union hR).union hC)
  have hKU : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ U := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have htW := hKW ⟨ht, rfl⟩
    refine ⟨htW, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (Or.inl ⟨h0V₀, by change (0 : ℝ) < 1 / 3; norm_num⟩)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (Or.inr ⟨h1V₁, by change (2 / 3 : ℝ) < 1; norm_num⟩)
    have hti : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact Or.inr ⟨⟨htW, havoid t hti⟩, hti⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hU hKU
  refine ⟨ε, hε, U, hU, ?_, Set.inter_subset_left, ?_⟩
  · rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  · intro p hp
    rcases hp.2 with (hpL | hpR) | hpC
    · have hcontact : k p ∈ B ↔ p.1 = 0 := hV₀sub hpL.1
      have hlt : p.1 < 1 / 3 := hpL.2
      constructor
      · exact fun h => Or.inl (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · exact hcontact.mpr h0
        · rw [h1] at hlt
          norm_num at hlt
    · have hcontact : k p ∈ B ↔ p.1 = 1 := hV₁sub hpR.1
      have hgt : 2 / 3 < p.1 := hpR.2
      constructor
      · exact fun h => Or.inr (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · rw [h0] at hgt
          norm_num at hgt
        · exact hcontact.mpr h1
    · have hnot : k p ∉ B := hpC.1.2
      have hti : p.1 ∈ Set.Ioo (0 : ℝ) 1 := hpC.2
      constructor
      · exact fun h => (hnot h).elim
      · intro h
        rcases h with h0 | h1
        · exact (hti.1.ne' h0).elim
        · exact (hti.2.ne h1).elim

/-- The main strip-existence statement: along an embedded arc in a sheet, transverse to a second
sheet at both endpoints with prescribed corner parametrisations, there is a clean embedded strip
having the given corner germs, meeting the first sheet exactly along the centre line and the
second sheet exactly in the two end fibres, and carrying strip normal data. -/
theorem exists_strip_along_arc_matching_parametrized_corners {E M D Z Z₀ Z₁ N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup Z₀] [NormedSpace ℝ Z₀]
    [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P] [ChartedSpace Z P] [T2Space N] [CompactSpace N]
    [CompactSpace P] {F : N → M} {G : P → M} {f : ℝ → N} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (c₀ : PartialDiffeomorph 𝓘(ℝ, Z₀) 𝓘(ℝ, Z) Z₀ P ∞)
    (c₁ : PartialDiffeomorph 𝓘(ℝ, Z₁) 𝓘(ℝ, Z) Z₁ P ∞) (hc₀ : (0 : Z₀) ∈ c₀.source)
    (hc₁ : (0 : Z₁) ∈ c₁.source) (hcross₀ : G (c₀ 0) = F (f 0)) (hcross₁ : G (c₁ 0) = F (f 1))
    (ht₀ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₀ 0))))
    (ht₁ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₁ 0))))
    (n : ℕ) (hsheet : 1 + n = Module.finrank ℝ D)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (hdimZ : 2 ≤ Module.finrank ℝ Z) {v₀ : Z₀} {v₁ : Z₁} (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G) {k₀ k₁ : (ℝ × ℝ) → M}
    {U₀ U₁ : Set (ℝ × ℝ)} (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0 : ℝ × ℝ) ∈ U₀) (h0U₁ : (0 : ℝ × ℝ) ∈ U₁)
    (hl₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] (F ∘ f))
    (hl₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)))
    (hr₀ : ∀ s, (0, s) ∈ U₀ → k₀ (0, s) = G (c₀ (s • v₀)))
    (hr₁ : ∀ s, (0, s) ∈ U₁ → k₁ (0, s) = G (c₁ (s • v₁)))
    (hcG₀ : ∀ p ∈ U₀, k₀ p ∈ Set.range G ↔ p.1 = 0)
    (hcG₁ : ∀ p ∈ U₁, k₁ p ∈ Set.range G ↔ p.1 = 0) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              ∃ k : (ℝ × ℝ) → M,
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
                  Set.InjOn k W ∧
                    Set.MapsTo k W O ∧
                      Topology.IsClosedEmbedding
                          (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                          (∀ p ∈ W, k p ∈ Set.range F ↔ p.2 = 0) ∧
                            (∀ p ∈ W, k p ∈ Set.range G ↔ p.1 = 0 ∨ p.1 = 1) ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, k (t, 0) = F (f t)) ∧
                                (k =ᶠ[𝓝 (0, 0)] k₀) ∧
                                  (k =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse) ∧
                                    Nonempty
                                      (StripNormalData (EuclideanSpace ℝ (Fin n))
                                        (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) (E := E)
                                        (Set.range F) k) := by
  obtain ⟨Φ, hline, htarget, hzero, hclean⟩ :=
    exists_clean_ambient_chart_along_embedded_arc hF hembF hiF hf hinjf hif n (Module.finrank ℝ Z)
      hsheet hcodim hO hfO
  have hline₀ := hline (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  have hline₁ := hline (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  have hx₀ : F (f 0) ∈ Φ.target := by
    have h := Φ.map_source' hline₀
    rwa [hzero 0 hline₀] at h
  have hx₁ : F (f 1) ∈ Φ.target := by
    have h := Φ.map_source' hline₁
    rwa [hzero 1 hline₁] at h
  have hdim :
    Module.finrank ℝ Z = Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) :=
    finrank_euclideanSpace_fin.symm
  have hn₀ :=
    (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean c₀ hc₀ hx₀ hcross₀ ht₀
        hdim hk₀ hU₀ h0U₀ hv₀ hr₀).1
  have hn₁ :=
    (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean c₁ hc₁ hx₁ hcross₁ ht₁
        hdim hk₁ hU₁ h0U₁ hv₁ hr₁).1
  let k₁' := k₁ ∘ StripCoordinates.reverse
  let U₁' := StripCoordinates.reverse ⁻¹' U₁
  have hU₁' : IsOpen U₁' := hU₁.preimage StripCoordinates.contDiff_reverse.continuous
  have h1U₁' : (1, 0) ∈ U₁' := by
    change StripCoordinates.reverse (1, 0) ∈ U₁
    rw [StripCoordinates.reverse_one_zero]
    exact h0U₁
  have hk₁' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁' U₁' :=
    hk₁.comp StripCoordinates.contDiff_reverse.contMDiff.contMDiffOn (fun _ hp => hp)
  have hk₁zero : k₁ (0, 0) = F (f 1) := by simpa only [sub_zero] using hl₁.eq_of_nhds
  have hk₁Phi : k₁ (0, 0) ∈ Φ.target := hk₁zero.symm ▸ hx₁
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Φ).contMDiffAt
      (Φ.open_target.mem_nhds hk₁Phi)
  have hH₁ : DifferentiableAt ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (0, 0) :=
    (hnormal.comp (0, 0) (hk₁.contMDiffAt (hU₁.mem_nhds h0U₁))).contDiffAt.differentiableAt
      (by simp)
  have hn₁' : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁') (1, 0) (0, 1) ≠ 0 := by
    change
      fderiv ℝ ((TransverseCoordinates.normalCoordinate Φ ∘ k₁) ∘ StripCoordinates.reverse) (1, 0)
          (0, 1) ≠
        0
    rw [StripCoordinates.vertical_derivative_reverse hH₁]
    exact hn₁
  have hcenter :
    Continuous
      (StripCoordinates.center :
        ℝ →
          StripCoordinates.Space (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)))) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hmatch₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hsource, hl₀] with t hs heq
    exact heq.trans (hzero t hs).symm
  have hrev : Filter.Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
    have he : Filter.Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
      (show Continuous (fun t : ℝ => 1 - t) by fun_prop).continuousAt
    simpa only [sub_self] using he
  have hmatch₁ : (fun t : ℝ => k₁' (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    have hleft := hl₁.comp_tendsto hrev
    filter_upwards [hsource, hleft] with t hs heq
    change k₁ (1 - t, 0) = Φ (StripCoordinates.center t)
    change k₁ (1 - t, 0) = F (f (1 - (1 - t))) at heq
    rw [heq, hzero t hs]
    congr 2
    ring
  obtain ⟨a, ha, V, hV, hrectV, k, hk, hinjk, hmap, _, hik, hcF, hkc, hkk₀, hkk₁, hnormal⟩ :=
    exists_clean_strip_matching_germs_in_chart Φ hline hclean hk₀ hk₁' hU₀ hU₁' h0U₀ h1U₁' hmatch₀
      hmatch₁ hn₀ hn₁' (by simpa only [finrank_euclideanSpace_fin] using hdimZ)
  have hkc' : ∀ t ∈ Set.Icc (0 : ℝ) 1, k (t, 0) = F (f t) := by
    intro t ht
    exact (hkc t).trans (hzero t (hline ht))
  have hKV : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact hrectV ⟨ht, ⟨neg_nonpos.mpr ha.le, ha.le⟩⟩
  have havoidk : ∀ t ∈ Set.Ioo (0 : ℝ) 1, k (t, 0) ∉ Set.range G := by
    intro t ht
    rw [hkc' t ⟨ht.1.le, ht.2.le⟩]
    exact havoid t ht
  have hcontact₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ Set.range G ↔ p.1 = 0 := by
    filter_upwards [hkk₀, hU₀.mem_nhds h0U₀] with p heq hp
    rw [heq]
    exact hcG₀ p hp
  have hcontact₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ Set.range G ↔ p.1 = 1 := by
    filter_upwards [hkk₁, hU₁'.mem_nhds h1U₁'] with p heq hp
    have h : k p ∈ Set.range G ↔ (StripCoordinates.reverse p).1 = 0 := by
      rw [heq]
      exact hcG₁ (StripCoordinates.reverse p) hp
    change (k p ∈ Set.range G ↔ 1 - p.1 = 0) at h
    rw [sub_eq_zero] at h
    exact h.trans eq_comm
  obtain ⟨ε, hε, W, hW, hrectW, hWV, hcG⟩ :=
    exists_strip_neighborhood_with_exact_endpoint_contacts hk hV hKV
      (isCompact_range hG.continuous).isClosed havoidk hcontact₀ hcontact₁
  have hemb : Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) := by
    let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply
      (continuousOn_iff_continuous_domRestrict.mp
          (hk.continuousOn.mono (hrectW.trans hWV))).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hWV (hrectW p.property)) (hWV (hrectW q.property)) hpq)
  exact
    ⟨ε, hε, W, hW, hrectW, k, hk.mono hWV, hinjk.mono hWV, fun _ hp => htarget (hmap (hWV hp)),
      hemb, fun p hp => hik p (hWV hp), fun p hp => hcF p (hWV hp), hcG, hkc', hkk₀, hkk₁,
      ⟨{  chart := Φ
          line := hline
          sheet := hclean
          center := hkc
          normal_nonzero := hnormal }⟩⟩

/-- Packaged form of the strip-existence statement: the clean strip patch along the arc, with its
strip normal data, exists between two given clean corner patches. -/
theorem exists_cleanStripPatch_of_tubular_arc_corners {E M D Z B N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [T2Space N] [CompactSpace N] [CompactSpace P] {F : N → M} {G : P → M}
    {f : ℝ → N} {g : ℝ → P} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) (hd : ∀ t, d (t, 0) = g t)
    (hd₀ : ((0 : ℝ), (0 : B)) ∈ d.source) (hd₁ : ((1 : ℝ), (0 : B)) ∈ d.source)
    (hcross₀ : G (g 0) = F (f 0)) (hcross₁ : G (g 1) = F (f 1))
    (ht₀ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0))))
    (ht₁ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1))))
    (n : ℕ) (hsheet : 1 + n = Module.finrank ℝ D)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (hdimZ : 2 ≤ Module.finrank ℝ Z) (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G)
    (c₀ : CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) (G ∘ g))
    (c₁ :
      CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun t => F (f (1 - t)))
        (fun t => G (g (1 - t))))
    {O : Set M} (hO : IsOpen O) (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ k : CleanStripPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) c₀.map c₁.map,
      Nonempty
          (StripNormalData (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) (E := E) (Set.range F) k.map) ∧
        Set.MapsTo k.map k.domain O := by
  let d' := (NativeParametrization.translation ((1 : ℝ), (0 : B))).toPartialDiffeomorph.trans d
  have hd'₀ : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + ((1 : ℝ), (0 : B)) ∈ d.source
    rw [zero_add]
    exact hd₁
  have hd0 : d (0 : ℝ × B) = g 0 := hd 0
  have hd1 : d' (0 : ℝ × B) = g 1 := by
    change d (0 + ((1 : ℝ), (0 : B))) = g 1
    rw [zero_add, hd]
  have hcross₀' : G (d 0) = F (f 0) := by rw [hd0]; exact hcross₀
  have hcross₁' : G (d' 0) = F (f 1) := by rw [hd1]; exact hcross₁
  have ht₀' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hd0]; exact ht₀
  have ht₁' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hd1]; exact ht₁
  have hv₀ : ((1 : ℝ), (0 : B)) ≠ 0 := fun he => one_ne_zero (congrArg Prod.fst he)
  have hv₁ : ((-1 : ℝ), (0 : B)) ≠ 0 := by
    intro he
    have he' : (-1 : ℝ) = 0 := congrArg Prod.fst he
    norm_num at he'
  have hleft₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0] (F ∘ f) := by
    have haxis :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (c₀.open_domain.mem_nhds c₀.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₀.axis_first t ht
  have hleft₁ : (fun t : ℝ => c₁.map (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)) := by
    have haxis :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (c₁.open_domain.mem_nhds c₁.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₁.axis_first t ht
  have hcurve₀ (s : ℝ) : d (s • ((1 : ℝ), (0 : B))) = g s := by
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hd s
  have hcurve₁ (s : ℝ) : d' (s • ((-1 : ℝ), (0 : B))) = g (1 - s) := by
    change d (s • ((-1 : ℝ), (0 : B)) + (1, 0)) = g (1 - s)
    have he : s • ((-1 : ℝ), (0 : B)) + (1, 0) = (1 - s, 0) := by
      simp [smul_eq_mul, sub_eq_add_neg, add_comm]
    rw [he, hd]
  obtain
    ⟨ε, hε, W, hW, hrect, k, hk, hinj, hmap, hemb, hi, hfirst, hsecond, hcenter, hleft, hright,
      hnormal⟩ :=
    exists_strip_along_arc_matching_parametrized_corners hF hG hembF hiF hf hinjf hif d d' hd₀
      hd'₀ hcross₀' hcross₁' ht₀' ht₁' n hsheet hcodim hdimZ hv₀ hv₁ havoid c₀.smooth c₁.smooth
      c₀.open_domain c₁.open_domain c₀.contains_zero c₁.contains_zero hleft₀ hleft₁
      (fun s hs => (c₀.axis_second s hs).trans (congrArg G (hcurve₀ s).symm))
      (fun s hs => (c₁.axis_second s hs).trans (congrArg G (hcurve₁ s).symm))
      (fun p hp => (c₀.sheets p hp).2) (fun p hp => (c₁.sheets p hp).2) hO hfO
  let strip : CleanStripPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) c₀.map c₁.map :=
    { width := ε, width_pos := hε, domain := W, open_domain := hW, contains_strip := hrect,
      map := k, smooth := hk, injective := hinj, closed_embedding := hemb,
      derivative_injective := hi, first_sheet := hfirst, second_sheet := hsecond,
      center := hcenter, left_germ := hleft, right_germ := hright }
  exact ⟨strip, hnormal, hmap⟩

end
