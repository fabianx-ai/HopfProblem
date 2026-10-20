/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.InnerBigon

/-!
# Filling a clean bigon boundary by an embedded Whitney disc

A clean bigon boundary (`CleanBigonBoundary`) between two sheets: two arcs, one in each sheet,
meeting at their endpoints. Contracting it into the interior gives, near the boundary, a smooth
injective immersion avoiding the sheets (`CleanBigonBoundary.exists_inner_clean_neighborhood`). When
every circle in the complement of the second sheet is null-homotopic the contracted boundary
extends over the bigon; under the general-position dimension hypotheses the
extension is an embedding avoiding the first sheet and the collar
(`CleanBigonBoundary.exists_collar_disjoint_inner_extension_in_open`), and gluing gives an embedded
filling of the bigon that agrees with the boundary map near the boundary
(`exists_filled_clean_bigon_of_collar_disjoint_inner`,
`CleanBigonBoundary.exists_filled_bigon_of_complement_contractions`). The filled bigon carries a
tubular neighbourhood (`CleanBigonBoundary.nonempty_tubularBigon_of_complement_contractions`).

This is the construction of the Whitney disc: Milnor, *Lectures on the h-cobordism theorem*, §6
(proof of the Whitney lemma, ambient dimension at least five).

## Tags

Whitney trick, Whitney disc, general position, embedding
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- A clean bigon boundary admits a contraction whose collar lies in the domain and whose composite
with the boundary map is, on a neighbourhood of the boundary of the bigon, a smooth injective
immersion into the interior avoiding the two sheets. -/
theorem CleanBigonBoundary.exists_inner_clean_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ V : Set (ℝ × ℝ),
            IsOpen V ∧
              frontier (WhitneyPairModel.bigon h) ⊆ V ∧
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
                    (d.map ∘ WhitneyPairModel.innerBigonMap h r) V ∧
                  Set.InjOn (d.map ∘ WhitneyPairModel.innerBigonMap h r) V ∧
                    (∀ p ∈ V,
                        Function.Injective
                          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E)
                            (d.map ∘ WhitneyPairModel.innerBigonMap h r) p)) ∧
                      Set.MapsTo (WhitneyPairModel.innerBigonMap h r) V
                          (d.domain ∩ interior (WhitneyPairModel.bigon h)) ∧
                        ∀ p ∈ V, d.map (WhitneyPairModel.innerBigonMap h r p) ∉ S ∪ T := by
  have hfrontD : frontier (WhitneyPairModel.bigon h) ⊆ d.domain :=
    d.boundary_covered.trans (interior_subset.trans d.neighborhood_subset)
  obtain ⟨r, hr, hcollar, hfront⟩ :=
    WhitneyPairModel.exists_inner_bigon_collar_in_open d.height_pos d.open_domain hfrontD
  let c := WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne'
  let V : Set (ℝ × ℝ) :=
    WhitneyPairModel.innerBigonMap h r ⁻¹'
      (d.domain ∩ interior (WhitneyPairModel.bigon h))
  have hc : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (WhitneyPairModel.innerBigonMap h r) :=
    c.contMDiff
  have hV : IsOpen V := (d.open_domain.inter isOpen_interior).preimage hc.continuous
  have hsmooth :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (d.map ∘ WhitneyPairModel.innerBigonMap h r) V :=
    d.smooth.comp hc.contMDiffOn (fun _ hp => hp.1)
  have hinj : Set.InjOn (d.map ∘ WhitneyPairModel.innerBigonMap h r) V := by
    intro p hp q hq hpq
    exact c.injective (d.injective hp.1 hq.1 hpq)
  refine ⟨r, hr, hcollar, V, hV, hfront, hsmooth, hinj, ?_, fun _ hp => hp, ?_⟩
  · intro p hp
    have hdf := (d.smooth.contMDiffAt (d.open_domain.mem_nhds hp.1)).mdifferentiableAt (by simp)
    rw [mfderiv_comp p hdf (hc.mdifferentiableAt (by simp))]
    exact
      (d.derivative_injective _ hp.1).comp
        (WhitneyPairModel.bijective_mfderiv_innerBigonMap h r hr.1.ne' p).injective
  · intro p hp
    exact d.interior_avoids _ hp

/-- If the complement of the two sheets has trivial fundamental group in the relevant range, the
contracted boundary map extends to a globally smooth map of the plane into that complement,
still injective and immersive near the boundary of the bigon. -/
theorem CleanBigonBoundary.exists_smooth_inner_extension_in_open {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) (U : TopologicalSpace.Opens M)
    (hU : (S ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              ∃ W : Set (ℝ × ℝ),
                IsOpen W ∧
                  frontier (WhitneyPairModel.bigon h) ⊆ W ∧
                    Set.EqOn (Subtype.val ∘ F) (d.map ∘ WhitneyPairModel.innerBigonMap h r)
                        W ∧
                      Set.InjOn F W ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                          ∀ p ∈ W, (F p : M) ∉ S ∪ T := by
  classical
  obtain ⟨r, hr, hcollar, V, hV, hfrontV, hsmooth, hinj, hderiv, -, havoid⟩ :=
    d.exists_inner_clean_neighborhood
  have hzero : (0 : ℝ × ℝ) ∈ frontier (WhitneyPairModel.bigon h) := by
    rw [WhitneyPairModel.mem_frontier_bigon_iff]
    refine ⟨?_, Or.inl rfl⟩
    change 0 ≤ (0 : ℝ) ∧ h * 0 ^ 2 + 0 ≤ h
    simpa only [zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero, add_zero] using
      And.intro le_rfl d.height_pos.le
  let c : U := ⟨d.map (WhitneyPairModel.innerBigonMap h r 0), hU (havoid 0 (hfrontV hzero))⟩
  let f : (ℝ × ℝ) → U := fun p =>
    if hp : p ∈ V then ⟨d.map (WhitneyPairModel.innerBigonMap h r p), hU (havoid p hp)⟩
    else c
  have hval (p : ℝ × ℝ) (hp : p ∈ V) :
    (f p : M) = d.map (WhitneyPairModel.innerBigonMap h r p) := by
    dsimp [f]
    rw [dif_pos hp]
  have hfval : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ f) V :=
    hsmooth.congr (fun p hp => hval p hp)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f V := by
    intro p hp
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U f V p).mp (hfval p hp)
  obtain ⟨F, hF, W, hW, hfrontW, hWV, hEq⟩ :=
    exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies hnull d.height_pos
      hV hf hfrontV
  have hEqval : Set.EqOn (Subtype.val ∘ F) (d.map ∘ WhitneyPairModel.innerBigonMap h r) W :=
    by
    intro p hp
    exact (congrArg Subtype.val (hEq hp)).trans (hval p (hWV hp))
  have hinjF : Set.InjOn F W := by
    intro p hp q hq hpq
    apply hinj (hWV hp) (hWV hq)
    exact (hEqval hp).symm.trans ((congrArg Subtype.val hpq).trans (hEqval hq))
  refine ⟨r, hr, hcollar, F, hF, W, hW, hfrontW, hEqval, hinjF, ?_, ?_⟩
  · intro p hp
    have heq : (Subtype.val ∘ F) =ᶠ[𝓝 p] (d.map ∘ WhitneyPairModel.innerBigonMap h r) :=
      Filter.mem_of_superset (hW.mem_nhds hp) (fun _ hq => hEqval hq)
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p) := by
      rw [heq.mfderiv_eq]
      exact hderiv p (hWV hp)
    have hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))] at hi
    intro v w hvw
    apply hi
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) (F p)) hvw
  · intro p hp
    change (Subtype.val ∘ F) p ∉ S ∪ T
    rw [hEqval hp]
    exact havoid p (hWV hp)

/-- Under a dimension hypothesis making general position available, the extension of the previous
statement can be taken to be an embedding of the whole bigon, avoiding the first sheet. -/
theorem CleanBigonBoundary.exists_embedded_inner_extension_in_open {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M] {D Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y]
    [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M))
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g) {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h)
    (U : TopologicalSpace.Opens M) (hU : (Set.range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => F p) ∧
                (∀ p ∈ WhitneyPairModel.bigon h,
                    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                  (∀ p ∈ WhitneyPairModel.bigon h, (F p : M) ∉ Set.range g) ∧
                    ∃ W : Set (ℝ × ℝ),
                      IsOpen W ∧
                        frontier (WhitneyPairModel.bigon h) ⊆ W ∧
                          Set.EqOn (Subtype.val ∘ F)
                            (d.map ∘ WhitneyPairModel.innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, V, hV, hfrontV, hEq, hinj, hderiv, havoid⟩ :=
    d.exists_smooth_inner_extension_in_open U hU hnull
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hcompact hV hfrontV
  have hinjC : Set.InjOn F (WhitneyPairModel.bigon h ∩ C) :=
    hinj.mono (Set.inter_subset_right.trans hCV)
  have hiC :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ C,
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p) :=
    fun p hp => hderiv p (hCV hp.2)
  have hclean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ C, p ∉ (∅ : Set (ℝ × ℝ)) → (F p : M) ∉ Set.range g := by
    intro p hp _ hmem
    exact havoid p (hCV hp.2) (Or.inl hmem)
  obtain ⟨G, hG, hhom, hemb, hiG, havoidG⟩ :=
    ManifoldImmersion.exists_relative_embedded_avoidance_in_open U F g hF hg
      (by simp [Module.finrank_prod]) hdim (by simpa [Module.finrank_prod] using hobstacle)
      (WhitneyPairModel.isCompact_bigon d.height_pos) hC (Set.empty_subset _) hinjC hiC
      hclean
  refine ⟨r, hr, hcollar, G, hG, hemb, hiG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp
    exact havoidG p ⟨hp, Set.notMem_empty p⟩
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC))

/-- Refinement of the previous statement whose embedded extension additionally avoids the image of
the collar on the interior of the bigon, which is what makes the boundary and the filling glue. -/
theorem CleanBigonBoundary.exists_collar_disjoint_inner_extension_in_open {E M D Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y] [ChartedSpace D Y]
    [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h)
    (U : TopologicalSpace.Opens M) (hU : (Set.range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => F p) ∧
                (∀ p ∈ WhitneyPairModel.bigon h,
                    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                  (∀ p ∈ WhitneyPairModel.bigon h, (F p : M) ∉ Set.range g) ∧
                    (∀ p ∈ interior (WhitneyPairModel.bigon h),
                        (F p : M) ∉ d.map '' WhitneyPairModel.innerBigonCollar h r) ∧
                      ∃ W : Set (ℝ × ℝ),
                        IsOpen W ∧
                          frontier (WhitneyPairModel.bigon h) ⊆ W ∧
                            Set.EqOn (Subtype.val ∘ F)
                              (d.map ∘ WhitneyPairModel.innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_embedded_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let Q : TopologicalSpace.Opens (ℝ × ℝ) := ⟨d.domain, d.open_domain⟩
  let q : C(Q, M) :=
    ⟨fun p => d.map p, continuousOn_iff_continuous_domRestrict.mp d.smooth.continuousOn⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ q := by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact d.smooth.contMDiffAt (d.open_domain.mem_nhds p.property)
  let A : Set Q := Subtype.val ⁻¹' WhitneyPairModel.innerBigonCollar h r
  have himage : q '' A = d.map '' WhitneyPairModel.innerBigonCollar h r := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hcollar hp⟩, hp, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact
      ((WhitneyPairModel.isCompact_innerBigonCollar d.height_pos
              hr.1.ne').image_of_continuousOn
          (d.smooth.continuousOn.mono hcollar)).isClosed
  have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (WhitneyPairModel.innerBigonMap h r) :=
    (WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne').contMDiff
  let V' : Set (ℝ × ℝ) := V ∩ WhitneyPairModel.innerBigonMap h r ⁻¹' d.domain
  have hV' : IsOpen V' := hV.inter (d.open_domain.preimage hs.continuous)
  have hfrontV' : frontier (WhitneyPairModel.bigon h) ⊆ V' := by
    intro p hp
    refine ⟨hfrontV hp, hcollar ?_⟩
    exact
      (WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr
            ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1).mpr
        hp
  have hfrontCompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV' hfrontV'
  have hinj : Set.InjOn F (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  have hclean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ C,
      p ∉ frontier (WhitneyPairModel.bigon h) → (F p : M) ∉ q '' A := by
    intro p hp hpB hmem
    rw [himage] at hmem
    obtain ⟨z, hz, heq⟩ := hmem
    have hzp : z = WhitneyPairModel.innerBigonMap h r p :=
      d.injective (hcollar hz) (hCV hp.2).2 (heq.trans (hEq (hCV hp.2).1))
    exact
      hpB
        ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hp.1).mp (hzp ▸ hz))
  let O : Set U := (Subtype.val : U → M) ⁻¹' (Set.range g)ᶜ
  have hO : IsOpen O :=
    (isCompact_range g.continuous).isClosed.isOpen_compl.preimage continuous_subtype_val
  have hmaps : Set.MapsTo F (WhitneyPairModel.bigon h) O := fun p hp => havoid p hp
  have hdim' : 2 * Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hobstacle' : Module.finrank ℝ (ℝ × ℝ) + Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨G, hG, hhom, hembG, hiG, hmapsG, havoidG⟩ :=
    ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open U F q A
      hF hq hclosed hdim' hobstacle' (WhitneyPairModel.isCompact_bigon d.height_pos) hC
      hfrontC hinj hi hclean hO hmaps
  refine ⟨r, hr, hcollar, G, hG, hembG, hiG, hmapsG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp hmem
    have hpB : p ∉ frontier (WhitneyPairModel.bigon h) := by
      intro hfront
      rw [frontier] at hfront
      exact hfront.2 hp
    exact havoidG p ⟨interior_subset hp, hpB⟩ (by rwa [himage])
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC).1)

/-- Gluing: an embedded filling of the bigon which agrees with the contracted boundary near the
boundary and avoids the collar can be repaired into an embedded filling that agrees with the
boundary map itself near the boundary and avoids both sheets in the interior. -/
theorem exists_filled_clean_bigon_of_collar_disjoint_inner {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hcollar : WhitneyPairModel.innerBigonCollar h r ⊆ d.domain) (F : C(ℝ × ℝ, M))
    (hF : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F) (hinjF : Set.InjOn F (WhitneyPairModel.bigon h))
    (hiF : ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p))
    (havoidF : ∀ p ∈ WhitneyPairModel.bigon h, F p ∉ S ∪ T)
    (hcollarF :
      ∀ p ∈ interior (WhitneyPairModel.bigon h),
        F p ∉ d.map '' WhitneyPairModel.innerBigonCollar h r)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W)
    (hEq : Set.EqOn F (d.map ∘ WhitneyPairModel.innerBigonMap h r) W) :
    ∃ f : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
        Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) ∧
          (∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
            (∀ p ∈ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
              ∃ V : Set (ℝ × ℝ),
                IsOpen V ∧ frontier (WhitneyPairModel.bigon h) ⊆ V ∧ Set.EqOn f d.map V := by
  let c := WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne'
  let core : Set (ℝ × ℝ) := c '' WhitneyPairModel.bigon h
  let P : Set (ℝ × ℝ) := c '' (interior (WhitneyPairModel.bigon h) ∪ W)
  let Q : Set (ℝ × ℝ) := d.domain \ c '' (WhitneyPairModel.bigon h \ W)
  let G : (ℝ × ℝ) → M := F ∘ c.symm
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G := hF.comp c.symm.contMDiff
  have hP : IsOpen P := c.toHomeomorph.isOpenMap _ (isOpen_interior.union hW)
  have hQ : IsOpen Q :=
    d.open_domain.inter
      (((WhitneyPairModel.isCompact_bigon d.height_pos).inter_right hW.isClosed_compl).image
          c.continuous).isClosed.isOpen_compl
  have hfront (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h)
    (hi : p ∉ interior (WhitneyPairModel.bigon h)) : p ∈ frontier (WhitneyPairModel.bigon h) := by
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp, hi⟩
  have hcoreP : core ⊆ P := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    by_cases hi : p ∈ interior (WhitneyPairModel.bigon h)
    · exact Or.inl hi
    · exact Or.inr (hfrontW (hfront p hp hi))
  have hcollarQ : WhitneyPairModel.innerBigonCollar h r ⊆ Q := by
    intro p hp
    refine ⟨hcollar hp, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact
      hz.2 (hfrontW ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hz.1).mp hp))
  have hnotCore (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) (hn : p ∉ core) :
    p ∈ WhitneyPairModel.innerBigonCollar h r :=
    ⟨hp, fun hi => hn (Set.image_mono interior_subset hi)⟩
  have hcover : WhitneyPairModel.bigon h ⊆ P ∪ Q := by
    intro p hp
    by_cases hc : p ∈ core
    · exact Or.inl (hcoreP hc)
    · exact Or.inr (hcollarQ (hnotCore p hp hc))
  have hfrontQ : frontier (WhitneyPairModel.bigon h) ⊆ Q := by
    intro p hp
    apply hcollarQ
    refine ⟨((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hi : p ∈ interior (WhitneyPairModel.bigon h) :=
      heq ▸ WhitneyPairModel.innerBigonMap_mem_interior d.height_pos hr (interior_subset hz)
    rw [frontier] at hp
    exact hp.2 hi
  have hmatch : Set.EqOn G d.map (P ∩ Q) := by
    rintro p ⟨hp, hq⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hzW : z ∈ W := by
      rcases hz with hz | hz
      · by_contra hn
        exact hq.2 ⟨z, ⟨interior_subset hz, hn⟩, rfl⟩
      · exact hz
    change F (c.symm (c z)) = d.map (c z)
    rw [c.symm_apply_apply]
    exact hEq hzW
  obtain ⟨j, hj, hjG, hjd⟩ :=
    exists_smooth_open_gluing hP hQ hG.contMDiffOn (d.smooth.mono Set.inter_subset_left) hmatch
  have hjInner (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) : j (c p) = F p :=
    (hjG (hcoreP ⟨p, hp, rfl⟩)).trans (congrArg F (c.symm_apply_apply p))
  have hjCollar (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.innerBigonCollar h r) : j p = d.map p :=
    hjd (hcollarQ hp)
  have hcross (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) (z : ℝ × ℝ)
    (hz : z ∈ WhitneyPairModel.innerBigonCollar h r) (heq : F p = d.map z) : c p = z := by
    by_cases hi : p ∈ interior (WhitneyPairModel.bigon h)
    · exact False.elim (hcollarF p hi ⟨z, hz, heq.symm⟩)
    · have hpf := hfront p hp hi
      apply
        d.injective
          (hcollar ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hp).mpr hpf))
          (hcollar hz)
      exact (hEq (hfrontW hpf)).symm.trans heq
  have hinj : Set.InjOn j (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    by_cases hpCore : p ∈ core
    · obtain ⟨p', hp', rfl⟩ := hpCore
      rw [hjInner p' hp'] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact congrArg c (hinjF hp' hz' heq)
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact hcross p' hp' z hzC heq
    · have hpC := hnotCore p hp hpCore
      rw [hjCollar p hpC] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact (hcross z' hz' p hpC heq.symm).symm
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact d.injective (hcollar hpC) (hcollar hzC) heq
  have hi :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) j p) := by
    intro p hp
    by_cases hpCore : p ∈ core
    · have heq : j =ᶠ[𝓝 p] G :=
        Filter.mem_of_superset (hP.mem_nhds (hcoreP hpCore)) (fun _ hx => hjG hx)
      rw [heq.mfderiv_eq]
      change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (F ∘ c.symm) p)
      rw [mfderiv_comp p (hF.mdifferentiableAt (by simp))
          (c.symm.contMDiff.mdifferentiableAt (by simp))]
      have hpin : c.symm p ∈ WhitneyPairModel.bigon h := by
        obtain ⟨z, hz, rfl⟩ := hpCore
        rwa [c.symm_apply_apply]
      exact
        (hiF _ hpin).comp
          (PartialChart.bijective_mfderiv c.symm.toPartialDiffeomorph (Set.mem_univ p)).injective
    · have hpC := hnotCore p hp hpCore
      have heq : j =ᶠ[𝓝 p] d.map :=
        Filter.mem_of_superset (hQ.mem_nhds (hcollarQ hpC)) (fun _ hx => hjd hx)
      rw [heq.mfderiv_eq]
      exact d.derivative_injective p (hcollar hpC)
  have havoid : ∀ p ∈ interior (WhitneyPairModel.bigon h), j p ∉ S ∪ T := by
    intro p hp
    by_cases hpCore : p ∈ core
    · obtain ⟨z, hz, rfl⟩ := hpCore
      rw [hjInner z hz]
      exact havoidF z hz
    · have hpC := hnotCore p (interior_subset hp) hpCore
      rw [hjCollar p hpC]
      exact d.interior_avoids p ⟨hcollar hpC, hp⟩
  obtain ⟨f, hf, V, hV, hKV, -, hfj⟩ :=
    exists_smooth_extension_near_starConvex (WhitneyPairModel.isCompact_bigon d.height_pos)
      (WhitneyPairModel.zero_mem_bigon d.height_pos.le)
      (WhitneyPairModel.starConvex_bigon d.height_pos.le) (hP.union hQ) hcover hj
  have hinjf : Set.InjOn f (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    apply hinj hp hz
    exact (hfj (hKV hp)).symm.trans (heq.trans (hfj (hKV hz)))
  have hembf : Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) := by
    let : CompactSpace (WhitneyPairModel.bigon h) :=
      isCompact_iff_compactSpace.mp (WhitneyPairModel.isCompact_bigon d.height_pos)
    apply (hf.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p z heq
    exact Subtype.ext (hinjf p.property z.property heq)
  refine ⟨⟨f, hf.continuous⟩, hf, hembf, ?_, ?_, V ∩ Q, hV.inter hQ, ?_, ?_⟩
  · intro p hp
    have heq : f =ᶠ[𝓝 p] j := Filter.mem_of_superset (hV.mem_nhds (hKV hp)) (fun _ hx => hfj hx)
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)
    rw [heq.mfderiv_eq]
    exact hi p hp
  · intro p hp
    change f p ∉ S ∪ T
    rw [hfj (hKV (interior_subset hp))]
    exact havoid p hp
  · intro p hp
    exact ⟨hKV ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1, hfrontQ hp⟩
  · intro p hp
    exact (hfj hp.1).trans (hjd hp.2)

/-- A clean bigon boundary in a manifold of dimension at least five, with a sheet of small enough
dimension and a simply connected complement, bounds an embedded Whitney disc: the bigon is
filled by an embedding avoiding the two sheets in its interior. -/
theorem CleanBigonBoundary.exists_filled_bigon_of_complement_contractions {E M D Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y] [ChartedSpace D Y]
    [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h) (hT : IsClosed T)
    (hnull :
      ∀ f : C(Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens M)),
        ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ f : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
        Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) ∧
          (∀ p ∈ WhitneyPairModel.bigon h,
              Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
            (∀ p ∈ interior (WhitneyPairModel.bigon h), f p ∉ Set.range g ∪ T) ∧
              ∃ V : Set (ℝ × ℝ),
                IsOpen V ∧ frontier (WhitneyPairModel.bigon h) ⊆ V ∧ Set.EqOn f d.map V := by
  let U : TopologicalSpace.Opens M := ⟨Tᶜ, hT.isOpen_compl⟩
  have hU : (Set.range g ∪ T)ᶜ ⊆ U := fun _ hp ht => hp (Or.inr ht)
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, havoidCollar, W, hW, hfrontW, hEq⟩ :=
    d.exists_collar_disjoint_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let F' : C(ℝ × ℝ, M) := ⟨Subtype.val ∘ F, continuous_subtype_val.comp F.continuous⟩
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hF' : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F' := hv.comp hF
  have hinjF' : Set.InjOn F' (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    have hFval : F p = F z := Subtype.ext heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) hFval)
  have hiF' :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F' p) :=
    by
    intro p hp
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p)
    rw [mfderiv_comp p (hv.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
    exact (TopologicalSpace.Opens.injective_mfderiv_subtype_val U (F p)).comp (hi p hp)
  have havoidF' : ∀ p ∈ WhitneyPairModel.bigon h, F' p ∉ Set.range g ∪ T := by
    intro p hp hmem
    rcases hmem with hmem | hmem
    · exact havoid p hp hmem
    · exact (F p).property hmem
  exact
    exists_filled_clean_bigon_of_collar_disjoint_inner d hr hcollar F' hF' hinjF' hiF'
      havoidF' havoidCollar hW hfrontW hEq

/-- In the same situation, the filled bigon carries a tubular neighbourhood: a tubular bigon of
codimension `n` exists. -/
theorem CleanBigonBoundary.nonempty_tubularBigon_of_complement_contractions
    {E M D Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y]
    [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M))
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g) {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h) (hT : IsClosed T)
    (hnull :
      ∀ f : C(Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens M)),
        ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E)
    (n : ℕ) (hcodim : 2 + n = Module.finrank ℝ E) :
    Nonempty (TubularBigon (E := E) (Set.range g) T a b k l h n) := by
  obtain ⟨f, hf, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_filled_bigon_of_complement_contractions g hg hT hnull hdim hobstacle
  have hinj : Set.InjOn f (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  obtain ⟨ε, hε, Φ, hsource, hzero, -⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      (WhitneyPairModel.isCompact_bigon d.height_pos)
      (WhitneyPairModel.zero_mem_bigon d.height_pos.le)
      (WhitneyPairModel.starConvex_bigon d.height_pos.le) hinj hi n
      (by simpa only [Module.finrank_prod, Module.finrank_self] using hcodim) isOpen_univ
      (Set.mapsTo_univ _ _)
  have hgerm : ∀ p ∈ frontier (WhitneyPairModel.bigon h), (f : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map :=
    fun _ hp => Filter.mem_of_superset (hV.mem_nhds (hfrontV hp)) (fun _ hx => hEq hx)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
    fun t ht =>
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time d.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
    fun t ht =>
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time d.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact
    ⟨{  height_pos := d.height_pos
        map := f
        smooth := hf
        closed_embedding := hemb
        derivative_injective := hi
        interior_avoids := havoid
        lower := fun t ht => (hEq (hfrontV (hlow t ht))).trans (d.lower t ht)
        upper := fun t ht => (hEq (hfrontV (hupp t ht))).trans (d.upper t ht)
        lower_germ := fun t ht => (hgerm _ (hlow t ht)).trans (d.lower_germ t ht)
        upper_germ := fun t ht => (hgerm _ (hupp t ht)).trans (d.upper_germ t ht)
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := hzero }⟩

end
