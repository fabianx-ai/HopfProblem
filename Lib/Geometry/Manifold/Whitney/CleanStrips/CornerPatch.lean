/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.CleanStrips.CrossingChart

/-!
# Clean corner patches at a transverse crossing

At a transverse intersection point of two embedded submanifolds of complementary dimension,
choosing a nonzero direction `u` in one and `v` in the other and reading the plane
`(s, t) ↦ (s • u, t • v)` in the clean crossing chart gives an immersed, injective
two-dimensional slice through the crossing whose two axes run along the two submanifolds and
which meets each of them only in its axis (`exists_native_clean_corner_of_parametrizations`).
`CleanCornerPatch S T a b` packages such a slice for two sheets `S`, `T` and two arcs `a`, `b`;
`CleanCornerPatch.swap` exchanges the roles of the two sheets.

These are the corners of the Whitney disk (Milnor, *Lectures on the h-cobordism theorem*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- The linear corner map `(s, t) ↦ (s • u, t • v)` of the plane into `D × Z`, spanning the two
coordinate directions by the given vectors.
-/
def TransverseCoordinates.cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) :
    (ℝ × ℝ) →L[ℝ] (D × Z) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)

/-- The value of the linear corner map. -/
theorem TransverseCoordinates.cornerLinear_apply {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) (p : ℝ × ℝ) :
    cornerLinear u v p = (p.1 • u, p.2 • v) :=
  rfl

/-- The linear corner map is injective when both spanning vectors are nonzero. -/
theorem TransverseCoordinates.injective_cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Function.Injective (cornerLinear u v) := by
  intro p q hpq
  exact
    Prod.ext ((smul_left_injective ℝ hu) (congrArg Prod.fst hpq))
      ((smul_left_injective ℝ hv) (congrArg Prod.snd hpq))

/-- The corner chart of a crossing: the linear corner map read in the chart `Φ`, a two-dimensional
slice of the ambient manifold through the crossing containing one direction of each sheet.
-/
def TransverseCoordinates.cornerMap {D Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) : (ℝ × ℝ) → M :=
  Φ ∘ cornerLinear u v

/-- The corner chart is smooth where defined. -/
theorem TransverseCoordinates.contMDiffOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) :=
  Φ.contMDiffOn_toFun.comp (cornerLinear u v).contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

/-- The corner chart is injective where defined, for nonzero spanning vectors. -/
theorem TransverseCoordinates.injOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Set.InjOn (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) := by
  intro p hp q hq heq
  exact injective_cornerLinear hu hv (Φ.toPartialEquiv.injOn hp hq heq)

/-- The corner chart is an immersion where defined, for nonzero spanning vectors. -/
theorem TransverseCoordinates.injective_mfderiv_cornerMap {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) {p : ℝ × ℝ} (hp : p ∈ cornerLinear u v ⁻¹' Φ.source) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (cornerMap Φ u v) p) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, D × Z) ∞ (cornerLinear u v) :=
    (cornerLinear u v).contDiff.contMDiff
  rw [cornerMap,
    mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp) (hL.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (cornerLinear u v).fderiv]
  exact (PartialChart.bijective_mfderiv Φ hp).1.comp (injective_cornerLinear hu hv)

/-- Clean corner at a transverse crossing: near a transverse intersection point of two embedded
submanifolds of complementary dimension there is a two-dimensional immersed injective slice `k`
through the crossing whose two axes parametrise the two sheets in the prescribed directions `u`
and `v`, and in which membership of each sheet is the vanishing of the complementary coordinate.
-/
theorem exists_native_clean_corner_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {u : A} {v : B} (hu : u ≠ 0) (hv : v ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (c 0) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (c (s • u))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (d (t • v))) := by
  obtain ⟨a, ha, Φ, hprod, _, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy hdim ht hO
      hxO
  let L := TransverseCoordinates.cornerLinear u v
  let W := L ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change L 0 ∈ Φ.source
    rw [map_zero]
    exact hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  refine
    ⟨W, Φ.open_source.preimage L.continuous, h0W, k,
      TransverseCoordinates.contMDiffOn_cornerMap Φ u v,
      TransverseCoordinates.injOn_cornerMap Φ hu hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact htarget (Φ.map_source' hp)
  · change Φ (L 0) = F (c 0)
    rw [map_zero]
    exact hcenter
  · intro p hp
    exact TransverseCoordinates.injective_mfderiv_cornerMap Φ hu hv hp
  · intro p hp
    have him := himages (L p) hp
    simpa only [L, k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu, hv, or_false] using him
  · intro s hs
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L (s, 0) ∈ Φ.source at hs
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have haxis : (0, t • v) ∈ Φ.source := by
      change L (0, t) ∈ Φ.source at ht
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using ht
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis

/-- A clean corner patch for two sheets `S` and `T` crossing at a point: an immersed injective map
of a plane neighbourhood of the origin into `M` whose two axes parametrise the given arcs `a`
and `b`, and which meets `S` exactly in the first axis and `T` exactly in the second.
-/
structure CleanCornerPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) where
  /-- The domain of the patch in the plane. -/
  domain : Set (ℝ × ℝ)
  /-- The domain is open. -/
  open_domain : IsOpen domain
  /-- The domain contains the origin. -/
  contains_zero : (0 : ℝ × ℝ) ∈ domain
  /-- The patch map. -/
  map : (ℝ × ℝ) → M
  /-- The patch map is smooth on its domain. -/
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  /-- The patch map is injective on its domain. -/
  injective : Set.InjOn map domain
  /-- The patch map is an immersion on its domain. -/
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  /-- A point of the domain is sent into `S` exactly when its second coordinate vanishes, and
  into `T` exactly when its first coordinate vanishes. -/
  sheets : ∀ p ∈ domain, (map p ∈ S ↔ p.2 = 0) ∧ (map p ∈ T ↔ p.1 = 0)
  /-- On the first axis the patch map is the arc `a`. -/
  axis_first : ∀ t, (t, 0) ∈ domain → map (t, 0) = a t
  /-- On the second axis the patch map is the arc `b`. -/
  axis_second : ∀ t, (0, t) ∈ domain → map (0, t) = b t

/-- Exchanging the two sheets of a clean corner patch, by composing the patch with the swap of the
two plane coordinates.
-/
def CleanCornerPatch.swap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    (c : CleanCornerPatch (E := E) S T a b) : CleanCornerPatch (E := E) T S b a := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have he : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (e : (ℝ × ℝ) → ℝ × ℝ) := e.contDiff.contMDiff
  refine
    { domain := e ⁻¹' c.domain
      open_domain := c.open_domain.preimage e.continuous
      contains_zero := ?_
      map := c.map ∘ e
      smooth := c.smooth.comp he.contMDiffOn (fun _ hp => hp)
      injective := ?_
      derivative_injective := ?_
      sheets := fun p hp => ⟨(c.sheets (e p) hp).2, (c.sheets (e p) hp).1⟩
      axis_first := fun t ht => c.axis_second t ht
      axis_second := fun t ht => c.axis_first t ht }
  · change e 0 ∈ c.domain
    rw [map_zero]
    exact c.contains_zero
  · intro p hp q hq hpq
    exact e.injective (c.injective hp hq hpq)
  · intro p hp
    have hc := c.smooth.contMDiffAt (c.open_domain.mem_nhds hp)
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
    exact
      (c.derivative_injective (e p) hp).comp
        (PartialChart.bijective_mfderiv e.toDiffeomorph.toPartialDiffeomorph
            (Set.mem_univ p)).1

end
