/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.Arcs
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripAlongArc

/-!
# Clean strip pairs along two arcs

Two clean strips along two arcs that meet only at their two shared corners have thin rectangular
neighbourhoods on which the only coincidences are the two corner identifications
(`exists_clean_strip_pair_neighborhoods`, from the point-set lemmas
`exists_open_neighborhoods_with_coincidences_in` and `exists_open_corner_overlap`); a clean strip
patch restricts to thinner rectangles (`CleanStripPatch.restrict`).

The main arc-pair statement in codimension two: two transverse intersection points of two embedded
sheets, joined by paths, are joined by embedded arcs, one in each sheet, meeting only at the two
intersection points and carrying a clean strip pair
(`exists_shared_corner_strip_pair_of_two_le_finrank`). This is the boundary of the Whitney disc, cf.
Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

Whitney trick, strip, embedded arc
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- Two compact sets whose coincidence pairs all lie in a given open set have open neighbourhoods
whose coincidence pairs still lie in that open set. -/
theorem exists_open_neighborhoods_with_coincidences_in {X Y M : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace M] [T2Space M] {K : Set X} {L : Set Y}
    (hK : IsCompact K) (hL : IsCompact L) {f : X → M} {g : Y → M} (hf : ∀ x ∈ K, ContinuousAt f x)
    (hg : ∀ y ∈ L, ContinuousAt g y) {O : Set (X × Y)} (hO : IsOpen O)
    (hcoinc : ∀ x ∈ K, ∀ y ∈ L, f x = g y → (x, y) ∈ O) :
    ∃ U : Set X,
      ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ K ⊆ U ∧ L ⊆ V ∧ ∀ x ∈ U, ∀ y ∈ V, f x = g y → (x, y) ∈ O := by
  let R : Set (X × Y) := {p | f p.1 ≠ g p.2} ∪ O
  have hKR : K ×ˢ L ⊆ interior R := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply mem_interior_iff_mem_nhds.mpr
    by_cases hxy : f x = g y
    · exact Filter.mem_of_superset (hO.mem_nhds (hcoinc x hx y hy hxy)) (fun _ hp => Or.inr hp)
    · have hfc : ContinuousAt (fun p : X × Y => f p.1) (x, y) := (hf x hx).comp continuousAt_fst
      have hgc : ContinuousAt (fun p : X × Y => g p.2) (x, y) := (hg y hy).comp continuousAt_snd
      have hne : ∀ᶠ p : X × Y in 𝓝 (x, y), f p.1 ≠ g p.2 := (hfc.ne_iff_eventually_ne hgc).mp hxy
      exact Filter.mem_of_superset hne (fun _ hp => Or.inl hp)
  obtain ⟨U, V, hU, hV, hKU, hLV, hUV⟩ := generalized_tube_lemma hK hL isOpen_interior hKR
  refine ⟨U, V, hU, hV, hKU, hLV, ?_⟩
  intro x hx y hy hxy
  exact (interior_subset (hUV ⟨hx, hy⟩)).resolve_left (fun hne => hne hxy)

/-- If two maps agree near two points with the composites of a locally injective map with two
continuous maps, then on small neighbourhoods their coincidences are exactly the coincidences of
those two maps. -/
theorem exists_open_corner_overlap {X Y D M : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace D] {k : X → M} {l : Y → M} {c : D → M} {a : X → D}
    {b : Y → D} {x₀ : X} {y₀ : Y} {W : Set D} (hW : IsOpen W) (hc : Set.InjOn c W)
    (ha : ContinuousAt a x₀) (hb : ContinuousAt b y₀) (haW : a x₀ ∈ W) (hbW : b y₀ ∈ W)
    (hk : k =ᶠ[𝓝 x₀] c ∘ a) (hl : l =ᶠ[𝓝 y₀] c ∘ b) :
    ∃ U : Set X,
      ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧ ∀ x ∈ U, ∀ y ∈ V, k x = l y ↔ a x = b y := by
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (hk.and (ha.preimage_mem_nhds (hW.mem_nhds haW)))
  obtain ⟨V, hVsub, hV, hyV⟩ := mem_nhds_iff.mp (hl.and (hb.preimage_mem_nhds (hW.mem_nhds hbW)))
  refine ⟨U, V, hU, hV, hxU, hyV, ?_⟩
  intro x hx y hy
  obtain ⟨hkx, hax⟩ := hUsub hx
  obtain ⟨hly, hby⟩ := hVsub hy
  rw [hkx, hly]
  exact ⟨hc hax hby, congrArg c⟩

/-- Two clean strips along two arcs meeting only at the two shared corners have thin rectangular
neighbourhoods on which the only coincidences are the two corner identifications. -/
theorem exists_clean_strip_pair_neighborhoods {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ δ : ℝ,
          0 < δ ∧
            ∃ U : Set (ℝ × ℝ),
              ∃ V : Set (ℝ × ℝ),
                IsOpen U ∧
                  IsOpen V ∧
                    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U ∧
                      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-δ) δ ⊆ V ∧
                        U ⊆ k.domain ∧
                          V ⊆ l.domain ∧
                            ∀ p ∈ U,
                              ∀ q ∈ V,
                                k.map p = l.map q →
                                  p = q.swap ∨
                                    StripCoordinates.reverse p =
                                      (StripCoordinates.reverse q).swap := by
  have hswap : Continuous (Prod.swap : (ℝ × ℝ) → ℝ × ℝ) := by fun_prop
  have hrev := StripCoordinates.contDiff_reverse.continuous
  obtain ⟨U₀, V₀, hU₀, hV₀, h0U₀, h0V₀, hover₀⟩ :=
    exists_open_corner_overlap c₀.open_domain c₀.injective
      (continuousAt_id : ContinuousAt (id : (ℝ × ℝ) → ℝ × ℝ) (0, 0))
      (hswap.continuousAt (x := (0, 0))) c₀.contains_zero c₀.contains_zero k.left_germ l.left_germ
  obtain ⟨U₁, V₁, hU₁, hV₁, h1U₁, h1V₁, hover₁⟩ :=
    exists_open_corner_overlap c₁.open_domain c₁.injective (hrev.continuousAt (x := (1, 0)))
      ((hswap.comp hrev).continuousAt (x := (1, 0)))
      (by rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      (by
        change (StripCoordinates.reverse (1, 0)).swap ∈ c₁.domain
        rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      k.right_germ l.right_germ
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have hKk : K ⊆ k.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hKl : K ⊆ l.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hk : ∀ p ∈ K, ContinuousAt k.map p := fun p hp =>
    k.smooth.continuousOn.continuousAt (k.open_domain.mem_nhds (hKk hp))
  have hl : ∀ p ∈ K, ContinuousAt l.map p := fun p hp =>
    l.smooth.continuousOn.continuousAt (l.open_domain.mem_nhds (hKl hp))
  let O := (U₀ ×ˢ V₀) ∪ (U₁ ×ˢ V₁)
  have hO : IsOpen O := (hU₀.prod hV₀).union (hU₁.prod hV₁)
  have hcenter : ∀ p ∈ K, ∀ q ∈ K, k.map p = l.map q → (p, q) ∈ O := by
    rintro ⟨t, r⟩ ⟨ht, hr⟩ ⟨s, v⟩ ⟨hs, hv⟩ heq
    have hr0 : r = 0 := hr
    have hv0 : v = 0 := hv
    subst r
    subst v
    rw [k.center t ht, l.center s hs] at heq
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨h0U₀, h0V₀⟩
    · exact Or.inr ⟨h1U₁, h1V₁⟩
  obtain ⟨U', V', hU', hV', hKU', hKV', hcoinc'⟩ :=
    exists_open_neighborhoods_with_coincidences_in hK hK hk hl hO hcenter
  let U := U' ∩ k.domain
  let V := V' ∩ l.domain
  have hU : IsOpen U := hU'.inter k.open_domain
  have hV : IsOpen V := hV'.inter l.open_domain
  have hKU : K ⊆ U := fun p hp => ⟨hKU' hp, hKk hp⟩
  have hKV : K ⊆ V := fun p hp => ⟨hKV' hp, hKl hp⟩
  obtain ⟨ε, hε, hεU⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hU hKU
  obtain ⟨δ, hδ, hδV⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hV hKV
  have hrect {r : ℝ} {W : Set (ℝ × ℝ)} (h : Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 r ⊆ W) :
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-r) r ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply h
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  refine
    ⟨ε, hε, δ, hδ, U, V, hU, hV, hrect hεU, hrect hδV, Set.inter_subset_right,
      Set.inter_subset_right, ?_⟩
  intro p hp q hq heq
  rcases hcoinc' p hp.1 q hq.1 heq with hleft | hright
  · exact Or.inl ((hover₀ p hleft.1 q hleft.2).mp heq)
  · exact Or.inr ((hover₁ p hright.1 q hright.2).mp heq)

/-- The restriction of a clean strip patch to a thinner rectangle inside its domain. -/
def CleanStripPatch.restrict {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁) {ε : ℝ} (hε : 0 < ε)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hrect : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U)
    (hUk : U ⊆ k.domain) : CleanStripPatch (E := E) S T a k₀ k₁ := by
  refine
    { width := ε
      width_pos := hε
      domain := U
      open_domain := hU
      contains_strip := hrect
      map := k.map
      smooth := k.smooth.mono hUk
      injective := k.injective.mono hUk
      closed_embedding := ?_
      derivative_injective := fun p hp => k.derivative_injective p (hUk hp)
      first_sheet := fun p hp => k.first_sheet p (hUk hp)
      second_sheet := fun p hp => k.second_sheet p (hUk hp)
      center := k.center
      left_germ := k.left_germ
      right_germ := k.right_germ }
  let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
  let : CompactSpace R :=
    isCompact_iff_compactSpace.mp
      (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
  have hc : Continuous (fun p : R => k.map p) :=
    continuousOn_iff_continuous_domRestrict.mp (k.smooth.continuousOn.mono (hrect.trans hUk))
  apply hc.isClosedEmbedding
  intro p q hpq
  exact Subtype.ext (k.injective (hUk (hrect p.property)) (hUk (hrect q.property)) hpq)

/-- The main arc-pair statement in codimension two: two transverse intersection points of two
embedded sheets, joined by paths, are joined by embedded arcs, one in each sheet, meeting only
at the two intersection points, and carrying clean corner patches, clean strip patches and strip
normal data on both sides. -/
theorem exists_shared_corner_strip_pair_of_two_le_finrank {E M D Z N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
    [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Function.Injective F) (hinjG : Function.Injective G)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Function.Injective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)) (hdimD : 2 ≤ Module.finrank ℝ D)
    (hdimZ : 2 ≤ Module.finrank ℝ Z)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁) (hxy : x₀ ≠ x₁)
    (γ : Path x₀ x₁) (η : Path y₀ y₁) :
    ∃ f : C(ℝ, N),
      ∃ g : C(ℝ, P),
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ g ∧
            f 0 = x₀ ∧
              f 1 = x₁ ∧
                g 0 = y₀ ∧
                  g 1 = y₁ ∧
                    Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
                      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
                        (∀ t ∈ Set.Icc (0 : ℝ) 1,
                            Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
                          (∀ t ∈ Set.Icc (0 : ℝ) 1,
                              Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) g t)) ∧
                            (∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G) ∧
                              (∀ t ∈ Set.Ioo (0 : ℝ) 1, G (g t) ∉ Set.range F) ∧
                                Set.range (fun t : unitInterval => F (f t)) ∩
                                      Set.range (fun t : unitInterval => G (g t)) =
                                    {F x₀, F x₁} ∧
                                  ∃ c₀ :
                                    CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f)
                                      (G ∘ g),
                                    ∃ c₁ :
                                      CleanCornerPatch (E := E) (Set.range F) (Set.range G)
                                        (fun t => F (f (1 - t))) (fun t => G (g (1 - t))),
                                      ∃ k :
                                        CleanStripPatch (E := E) (Set.range F) (Set.range G)
                                          (F ∘ f) c₀.map c₁.map,
                                        ∃ l :
                                          CleanStripPatch (E := E) (Set.range G) (Set.range F)
                                            (G ∘ g) c₀.swap.map c₁.swap.map,
                                          Nonempty
                                              (StripNormalData
                                                (EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))
                                                (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)))
                                                (E := E) (Set.range F) k.map) ∧
                                            Nonempty
                                                (StripNormalData
                                                  (EuclideanSpace ℝ
                                                    (Fin (Module.finrank ℝ Z - 1)))
                                                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ D)))
                                                  (E := E) (Set.range G) l.map) ∧
                                              (∀ p ∈ k.domain,
                                                  ∀ q ∈ l.domain,
                                                    k.map p = l.map q →
                                                      p = q.swap ∨
                                                        StripCoordinates.reverse p =
                                                          (StripCoordinates.reverse q).swap) ∧
                                                ∀ h : ℝ,
                                                  0 < h →
                                                    Nonempty
                                                      (CleanBigonBoundary (E := E) (Set.range F)
                                                        (Set.range G) (F ∘ f) (G ∘ g) k.map l.map
                                                        h) := by
  have hfinite : (Set.range F ∩ Set.range G).Finite :=
    finite_transverse_intersections hF hG hinjF hinjG hcodim ht
  have hSF : (F ⁻¹' Set.range G).Finite := by
    have hpre : F ⁻¹' (Set.range F ∩ Set.range G) = F ⁻¹' Set.range G := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_right (Set.mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjF.injOn
  have hSG : (G ⁻¹' Set.range F).Finite := by
    have hpre : G ⁻¹' (Set.range F ∩ Set.range G) = G ⁻¹' Set.range F := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_left (Set.mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjG.injOn
  have hy : y₀ ≠ y₁ := by
    intro heq
    apply hxy
    exact hinjF (hcross₀.symm.trans ((congrArg G heq).trans hcross₁))
  obtain ⟨f, hf, hf0, hf1, hembf, hif, havoidf, ρ, hρ, c, hsourceC, hzeroC, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero γ hxy hdimD
      (Module.finrank ℝ D - 1) (by omega) hSF
  obtain ⟨g, hg, hg0, hg1, hembg, hig, havoidg, σ, hσ, d, hsourceD, hzeroD, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero η hy hdimZ
      (Module.finrank ℝ Z - 1) (by omega) hSG
  have hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembf.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinjg : Set.InjOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembg.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinter :
    Set.range (fun t : unitInterval => F (f t)) ∩ Set.range (fun t : unitInterval => G (g t)) =
      {F x₀, F x₁} := by
    ext w
    constructor
    · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
      by_cases ht0 : (t : ℝ) = 0
      · simp only [ht0, hf0]
        exact Set.mem_insert _ _
      by_cases ht1 : (t : ℝ) = 1
      · simp only [ht1, hf1]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      have hti : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
      exact (havoidf t hti ⟨g s, hs⟩).elim
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨⟨0, congrArg F hf0⟩, ⟨0, (congrArg G hg0).trans hcross₀⟩⟩
      · exact ⟨⟨1, congrArg F hf1⟩, ⟨1, (congrArg G hg1).trans hcross₁⟩⟩
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  have hc₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, Metric.mem_closedBall_self hρ.le⟩
  have hc₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, Metric.mem_closedBall_self hρ.le⟩
  have hd₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, Metric.mem_closedBall_self hσ.le⟩
  have hd₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, Metric.mem_closedBall_self hσ.le⟩
  have hcross₀' : G (g 0) = F (f 0) := by rw [hf0, hg0]; exact hcross₀
  have hcross₁' : G (g 1) = F (f 1) := by rw [hf1, hg1]; exact hcross₁
  have ht₀ := ht (f 0) (g 0) hcross₀'
  have ht₁ := ht (f 1) (g 1) hcross₁'
  have hcoord :
    Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1))) +
        Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1))) =
      Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
    omega
  have hcorner₀ :
    Nonempty (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) (G ∘ g)) := by
    simpa only [zero_add, mul_one, Function.comp_def] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD hc₀ hd₀
        hcross₀' hcoord ht₀ (σ := 1) (τ := 1) one_ne_zero one_ne_zero
  have hcorner₁ :
    Nonempty
      (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun t => F (f (1 - t)))
        (fun t => G (g (1 - t)))) := by
    simpa only [mul_neg_one, ← sub_eq_add_neg] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD hc₁ hd₁
        hcross₁' hcoord ht₁ (σ := -1) (τ := -1) (by norm_num) (by norm_num)
  obtain ⟨c₀⟩ := hcorner₀
  obtain ⟨c₁⟩ := hcorner₁
  obtain ⟨stripF, hnormalF, _⟩ :=
    exists_cleanStripPatch_of_tubular_arc_corners hF hG hembF hiF hf hinjf hif d hzeroD hd₀ hd₁
      hcross₀' hcross₁' ht₀ ht₁ (Module.finrank ℝ D - 1) (by omega) hcodim hdimZ havoidf c₀ c₁
      isOpen_univ (fun _ _ => Set.mem_univ _)
  let DF₀ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)
  let DF₁ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)
  let DG₀ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0)
  let DG₁ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1)
  have ht₀' : Function.Surjective (DG₀.coprod DF₀) :=
    TransverseCoordinates.surjective_coprod_swap DF₀ DG₀ ht₀
  have ht₁' : Function.Surjective (DG₁.coprod DF₁) :=
    TransverseCoordinates.surjective_coprod_swap DF₁ DG₁ ht₁
  have hcodim' : Module.finrank ℝ Z + Module.finrank ℝ D = Module.finrank ℝ E := by omega
  obtain ⟨stripG, hnormalG, _⟩ :=
    exists_cleanStripPatch_of_tubular_arc_corners hG hF hembG hiG hg hinjg hig c hzeroC hc₀ hc₁
      hcross₀'.symm hcross₁'.symm ht₀' ht₁' (Module.finrank ℝ Z - 1) (by omega) hcodim' hdimD
      havoidg c₀.swap c₁.swap isOpen_univ (fun _ _ => Set.mem_univ _)
  have hcoinc :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, (F ∘ f) t = (G ∘ g) s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
    intro t ht s hs heq
    have hmem : F (f t) ∈ ({F x₀, F x₁} : Set M) := by
      rw [← hinter]
      exact ⟨⟨⟨t, ht⟩, rfl⟩, ⟨⟨s, hs⟩, heq.symm⟩⟩
    change F (f t) = F x₀ ∨ F (f t) = F x₁ at hmem
    have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    rcases hmem with hleft | hright
    · left
      constructor
      · exact hinjf ht h0 (hinjF (hleft.trans (congrArg F hf0).symm))
      · apply hinjg hs h0
        apply hinjG
        exact heq.symm.trans (hleft.trans ((congrArg G hg0).trans hcross₀).symm)
    · right
      constructor
      · exact hinjf ht h1 (hinjF (hright.trans (congrArg F hf1).symm))
      · apply hinjg hs h1
        apply hinjG
        exact heq.symm.trans (hright.trans ((congrArg G hg1).trans hcross₁).symm)
  obtain ⟨ε', hε', δ', hδ', U', V', hU', hV', hrectU', hrectV', hU'sub, hV'sub, hoverlap⟩ :=
    exists_clean_strip_pair_neighborhoods c₀ c₁ stripF stripG hcoinc
  let k' := stripF.restrict hε' hU' hrectU' hU'sub
  let l' := stripG.restrict hδ' hV' hrectV' hV'sub
  have hoverlap' :
    ∀ p ∈ k'.domain,
      ∀ q ∈ l'.domain,
        k'.map p = l'.map q →
          p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap :=
    hoverlap
  refine
    ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg, hinter, c₀, c₁,
      k', l', hnormalF, hnormalG, hoverlap', ?_⟩
  intro h hh
  exact nonempty_cleanBigonBoundary hh c₀ c₁ k' l' hoverlap'

end
