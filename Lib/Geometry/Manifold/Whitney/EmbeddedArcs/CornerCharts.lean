/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips

/-!
# Clean corner charts and clean charts along an arc

At a transverse intersection point of two tubular arcs there is a clean corner chart, a local
parametrisation in which the two arcs are the two coordinate axes
(`exists_clean_corner_of_tubular_arcs`, packaged as `nonempty_cleanCornerPatch_of_tubular_arcs`).
Along an embedded arc in an embedded sheet there is an ambient strip chart that is clean for the
sheet: the sheet is the zero set of the normal coordinate and the centre line is the arc
(`exists_clean_ambient_chart_along_embedded_arc`).

These are tubular-neighbourhood (slice) charts adapted to the arcs of the Whitney trick, cf. Milnor,
*Lectures on the h-cobordism theorem*, §6.

## Tags

slice chart, transversality, tubular neighbourhood
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- At a transverse intersection point of two tubular arcs there is a clean corner chart: a local
parametrisation of a neighbourhood of the intersection in which the two arcs are the two
coordinate axes. -/
theorem exists_clean_corner_of_tubular_arcs {E M D Z N P A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [TopologicalSpace N] [ChartedSpace D N] [TopologicalSpace P] [ChartedSpace Z P] {F : N → M}
    {G : P → M} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) {f : ℝ → N} {g : ℝ → P}
    (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t) {t₀ : ℝ}
    (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source) (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (f t₀) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (f t₀) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (f (t₀ + s * σ))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (g (t₀ + t * τ))) := by
  let c' := (NativeParametrization.translation (t₀, (0 : A))).toPartialDiffeomorph.trans c
  let d' := (NativeParametrization.translation (t₀, (0 : B))).toPartialDiffeomorph.trans d
  have hc0 : (0 : ℝ × A) ∈ c'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + (t₀, (0 : A)) ∈ c.source
    rw [zero_add]
    exact htc
  have hd0 : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + (t₀, (0 : B)) ∈ d.source
    rw [zero_add]
    exact htd
  have hcx : c' 0 = f t₀ := by
    change c (0 + (t₀, (0 : A))) = f t₀
    rw [zero_add, hc]
  have hdy : d' 0 = g t₀ := by
    change d (0 + (t₀, (0 : B))) = g t₀
    rw [zero_add, hd]
  have hxy' : G (d' 0) = F (c' 0) := by rw [hcx, hdy]; exact hxy
  have ht' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c' 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c' 0) ∈ O := by rw [hcx]; exact hxO
  have hu : (σ, (0 : A)) ≠ 0 := fun he => hσ (congrArg Prod.fst he)
  have hv : (τ, (0 : B)) ≠ 0 := fun he => hτ (congrArg Prod.fst he)
  obtain ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter, hi, hclean, hlo, hhi⟩ :=
    exists_native_clean_corner_of_parametrizations hF hG hembF hembG c' d' hc0 hd0 hxy' hdim ht'
      hu hv hO hxO'
  refine ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter.trans (congrArg F hcx), hi, hclean, ?_, ?_⟩
  · intro s hs
    rw [hlo s hs]
    apply congrArg F
    change c (s • (σ, (0 : A)) + (t₀, 0)) = f (t₀ + s * σ)
    have he : s • (σ, (0 : A)) + (t₀, 0) = (t₀ + s * σ, 0) := by simp [smul_eq_mul, add_comm]
    rw [he, hc]
  · intro t ht
    rw [hhi t ht]
    apply congrArg G
    change d (t • (τ, (0 : B)) + (t₀, 0)) = g (t₀ + t * τ)
    have he : t • (τ, (0 : B)) + (t₀, 0) = (t₀ + t * τ, 0) := by simp [smul_eq_mul, add_comm]
    rw [he, hd]

/-- Packaged form of the previous statement: the clean corner patch at a transverse intersection of
two tubular arcs is nonempty. -/
theorem nonempty_cleanCornerPatch_of_tubular_arcs {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) {f : ℝ → N} {g : ℝ → P}
    (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t) {t₀ : ℝ}
    (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source) (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    Nonempty
      (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun s => F (f (t₀ + s * σ)))
        (fun t => G (g (t₀ + t * τ)))) := by
  obtain ⟨W, hW, h0W, k, hk, hinj, _, _, hi, hsheets, hlo, hhi⟩ :=
    exists_clean_corner_of_tubular_arcs hF hG hembF hembG c d hc hd htc htd hxy hdim ht hσ hτ
      isOpen_univ (Set.mem_univ _)
  exact
    ⟨{ domain := W, open_domain := hW, contains_zero := h0W, map := k, smooth := hk,
        injective := hinj, derivative_injective := hi, sheets := hsheets, axis_first := hlo,
        axis_second := hhi }⟩

/-- Along an embedded arc in an embedded sheet there is an ambient strip chart which is clean for
the sheet: the sheet is the zero set of the normal coordinate, and the centre line is the arc. -/
theorem exists_clean_ambient_chart_along_embedded_arc {E M G N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N] {F : N → M}
    {f : ℝ → N} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) (n m : ℕ)
    (hsheet : 1 + n = Module.finrank ℝ G) (hcodim : Module.finrank ℝ G + m = Module.finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ Φ :
      PartialDiffeomorph
        𝓘(ℝ, StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) 𝓘(ℝ, E)
        (StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) M ∞,
      Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) Φ.source ∧
        Φ.target ⊆ O ∧
          (∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = F (f t)) ∧
            (∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) := by
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨a, ha, c, hprod, hzero, _⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      CompactIccSpace.isCompact_Icc (by simp) hstar hinjf hif n
      (by simpa only [Module.finrank_self] using hsheet) isOpen_univ (fun _ _ => Set.mem_univ _)
  let K := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have h0K : (0 : ℝ × EuclideanSpace ℝ (Fin n)) ∈ K := by simp [K]
  have hstarK : StarConvex ℝ (0 : ℝ × EuclideanSpace ℝ (Fin n)) K :=
    hstar.prod (starConvex_singleton _)
  have hKc : K ⊆ c.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, Metric.mem_closedBall_self ha.le⟩
  have hFO : Set.MapsTo (F ∘ c) K O := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change F (c (t, 0)) ∈ O
    rw [hzero]
    exact hfO ht
  have hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) + m = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin,
      hsheet] using hcodim
  obtain ⟨b, hb, Φ, hΦprod, _, htarget, hΦzero, hclean⟩ :=
    exists_clean_embedded_sheet_neighborhood hF hembF c hK h0K hstarK hKc (fun x _ => hiF (c x)) m
      hdim hO hFO
  refine ⟨Φ, ?_, htarget, ?_, hclean⟩
  · intro t ht
    exact hΦprod ⟨⟨ht, rfl⟩, Metric.mem_closedBall_self hb.le⟩
  · intro t ht
    exact (hΦzero (t, 0) ht).trans (congrArg F (hzero t))

end
