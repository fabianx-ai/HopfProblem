/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus

/-!
# Tubular neighbourhoods of embedded star-convex compact sets

Let `f : D → M` be a map from a finite-dimensional normed space `D` to a compact manifold `M`
modelled on `E`, smooth on a neighbourhood of a compact star-convex set `K ∋ 0`, injective and
immersive on `K`, with `dim D + n = dim E`. Then there is a partial diffeomorphism
`Φ : D × ℝⁿ → M` whose source contains `K ×ˢ closedBall 0 ε`, which restricts to `f` on the zero
section and whose target lies in a prescribed open set
(`exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero` for an inner-product
space `D`, `exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero` for
a normed `D`, `exists_local_tubularNeighborhood_of_embedded_starConvex` for `f` smooth on an open
set only). Star-convexity of `K` makes the normal bundle of `f` over `K` trivial:
`NativeEuclideanEmbedding.exists_smooth_normalFrame_near_starConvex` produces a smooth normal frame,
the first step of the construction. When `f` is an embedding on the open set, the chart can be made
*clean*: a point of its source lies over the image exactly when its normal coordinate vanishes
(`exists_clean_tubularNeighborhood_of_embedded_starConvex`, and for an embedded immersed
`F : N → M` read in a chart of `N`, `exists_clean_embedded_sheet_neighborhood`).

## References

* Hirsch, *Differential Topology*, Ch. 4 §5 (the tubular neighbourhood theorem).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- A smooth normal frame along an embedded immersed star-convex compact set: on a neighbourhood of
`K` there is a smooth family of injective maps whose ranges are the normal spaces of `f`.
Star-convexity makes the normal bundle trivial, which is the first step of the tubular
neighbourhood theorem (Hirsch, *Differential Topology*, Ch. 4 §5). -/
theorem NativeEuclideanEmbedding.exists_smooth_normalFrame_near_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) :
    ∃ V : Set D,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension),
            ContDiffOn ℝ ∞ A V ∧
              ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ K, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, A, hA, hAi⟩ :=
    DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : Module.finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : Module.finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg
          (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) => Module.finrank ℝ S)
          hr).trans
      hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine
    ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap, hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hKU hx), Submodule.range_starProjection]

/-- Tubular neighbourhood theorem for an embedded immersed star-convex compact set in an
inner-product source: there is a partial diffeomorphism of `D × ℝⁿ` onto a neighbourhood of `f '' K`
inside a prescribed open set, restricting to `f` on `D × {0}` (Hirsch, *Differential Topology*,
Ch. 4 §5). -/
theorem exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧ (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ :=
    e.exists_smooth_normalFrame_near_starConvex hf hK hz hstar hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ :=
    r.exists_diskTubularNeighborhood hf hK hV hKV hinj hi hA (fun x hx => (hframe x hx).1)
      (fun x hx => (hframe x hx).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W :=
    fun p => PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ p.property.1
  let Ψ :=
    partialDiffeomorphOfInjectiveLocal hW (Φ.toPartialEquiv.injOn.mono Set.inter_subset_left)
      hWloc
  have hzeroΨ : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

/-- The same tubular neighbourhood statement for a general normed source. -/
theorem exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧ (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let D₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ D))
  let e : D₀ ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let f₀ := f ∘ e
  let K₀ := e ⁻¹' K
  have hf₀ : ContMDiff 𝓘(ℝ, D₀) 𝓘(ℝ, E) ∞ f₀ := hf.comp e.contDiff.contMDiff
  have hK₀ : IsCompact K₀ := e.toHomeomorph.isCompact_preimage.mpr hK
  have hz₀ : (0 : D₀) ∈ K₀ := by
    change e 0 ∈ K
    simpa only [map_zero] using hz
  have hstar₀ : StarConvex ℝ (0 : D₀) K₀ := by
    apply StarConvex.linear_preimage e.toLinearMap
    simpa only [ContinuousLinearEquiv.coe_coe, map_zero] using hstar
  have hinj₀ : Set.InjOn f₀ K₀ := fun _ hx _ hy hxy => e.injective (hinj hx hy hxy)
  have hi₀ : ∀ x ∈ K₀, Function.Injective (mfderiv 𝓘(ℝ, D₀) 𝓘(ℝ, E) f₀ x) := by
    intro x hx
    exact
      (ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff e
            (hf.mdifferentiableAt (by simp))).mpr
        (hi (e x) hx)
  have hcodim₀ : Module.finrank ℝ D₀ + n = Module.finrank ℝ E := by
    simpa only [D₀, finrank_euclideanSpace_fin] using hcodim
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf₀ hK₀ hz₀ hstar₀
      hinj₀ hi₀ n hcodim₀ hO (fun _ hx => hfO hx)
  let eprod := e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))
  let c := eprod.toDiffeomorph
  let Ψ := c.toPartialDiffeomorph'.trans Φ
  have hpre (x : D) (hx : x ∈ K) : e.symm x ∈ K₀ := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_⟩
  · rintro ⟨x, v⟩ ⟨hx, hv⟩
    exact ⟨Set.mem_univ _, hsource ⟨hpre x hx, hv⟩⟩
  · intro x
    change Φ (e.symm x, 0) = f x
    rw [hzero (e.symm x)]
    exact congrArg f (e.apply_symm_apply x)
  · intro y hy
    exact htarget hy.1

/-- Tubular neighbourhood for a map that is only defined and smooth on an open set `U` containing
`K`; the chart source is then contained in `U × ℝⁿ`. -/
theorem exists_local_tubularNeighborhood_of_embedded_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ Set.univ ∧ (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧ Φ.target ⊆ O :=
  by
  obtain ⟨g, hg, V, hV, hKV, hVU, heq⟩ :=
    exists_smooth_extension_near_starConvex hK hz hstar hU hKU hf
  have hinjg : Set.InjOn g K := by
    intro x hx y hy hxy
    apply hinj hx hy
    simpa only [heq (hKV hx), heq (hKV hy)] using hxy
  have hig : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x) := by
    intro x hx
    have hnear : g =ᶠ[𝓝 x] f := Filter.Eventually.mono (hV.mem_nhds (hKV hx)) heq
    rw [hnear.mfderiv_eq]
    exact hi x hx
  have hgO : Set.MapsTo g K O := by
    intro x hx
    rw [heq (hKV hx)]
    exact hfO hx
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hg hK hz
      hstar hinjg hig n hcodim hO hgO
  let Ψ :=
    PartialChart.restrictSource Φ
      (hV.preimage (continuous_fst : Continuous (Prod.fst : D × EuclideanSpace ℝ (Fin n) → D)))
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hsource hp, hKV hp.1⟩
  · intro p hp
    exact ⟨hVU hp.2, Set.mem_univ _⟩
  · intro x hx
    change Φ (x, 0) = f x
    exact (hzero x).trans (heq hx.2)
  · intro y hy
    exact htarget hy.1

/-- Clean tubular neighbourhood: the chart of the previous statement can be chosen so that a point
of its source lies over `f '' U` exactly when its normal coordinate vanishes. -/
theorem exists_clean_tubularNeighborhood_of_embedded_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hemb : Topology.IsEmbedding (fun x : U => f x))
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ Set.univ ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ q ∈ Φ.source, Φ q ∈ f '' U ↔ q.2 = 0) := by
  have hinj : Set.InjOn f K := by
    intro x hx y hy hxy
    exact
      congrArg Subtype.val
        (hemb.injective
          (show (fun u : U => f u) ⟨x, hKU hx⟩ = (fun u : U => f u) ⟨y, hKU hy⟩ from hxy))
  obtain ⟨a, ha, Φ, hprod, hsource, hzero, htarget⟩ :=
    exists_local_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar hU hKU hinj hi n hcodim
      hO hfO
  have hbase : IsOpen {x : U | ((x : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
    Φ.open_source.preimage (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨A, hA, hpreA⟩ := hemb.isInducing.isOpen_iff.mp hbase
  have haxis {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : (x, 0) ∈ Φ.source := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun u : U => f u) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact hx'
  have hKA : Set.MapsTo f K A := by
    intro x hx
    have hx' :
      (⟨x, hKU hx⟩ : U) ∈ {u : U | ((u : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
      hprod ⟨hx, Metric.mem_closedBall_self ha.le⟩
    rw [← hpreA] at hx'
    exact hx'
  let Ψ := PartialChart.restrictTarget Φ hA
  have hKzero : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    have hxΦ := hprod ⟨hx, Metric.mem_closedBall_self ha.le⟩
    refine ⟨hxΦ, ?_⟩
    change Φ (x, 0) ∈ A
    rw [hzero x hxΦ]
    exact hKA hx
  obtain ⟨ε, hε, hεprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hKzero
  refine
    ⟨ε, hε, Ψ, hεprod, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1, fun x hx =>
      hzero x hx.1, ?_⟩
  rintro ⟨x, z⟩ hq
  constructor
  · rintro ⟨u, hu, heq⟩
    have huA : f u ∈ A := heq ▸ hq.2
    have huΦ := haxis hu huA
    have hpair : (x, z) = (u, 0) :=
      Φ.toPartialEquiv.injOn hq.1 huΦ (heq.symm.trans (hzero u huΦ).symm)
    exact congrArg Prod.snd hpair
  · intro hz
    change z = 0 at hz
    subst z
    exact ⟨x, (hsource hq.1).1, (hzero x hq.1).symm⟩

/-- Clean tubular neighbourhood of a sheet: for an embedded immersed `F : N → M` read in a chart
`c`, a chart of `M` in which the sheet is exactly the zero set of the normal coordinate. -/
theorem exists_clean_embedded_sheet_neighborhood {E M D G N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] {F : N → M} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hembF : Topology.IsEmbedding F) (c : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, G) D N ∞) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K) (hKc : K ⊆ c.source)
    (hiF : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (c x))) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hFO : Set.MapsTo (F ∘ c) K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ c.source ×ˢ Set.univ ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = F (c x)) ∧
                  (∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) := by
  let f := F ∘ c
  have hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f c.source := hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hembf : Topology.IsEmbedding (fun x : c.source => f x) :=
    hembF.comp c.toOpenPartialHomeomorph.isEmbedding_restrict
  have hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
    intro x hx
    rw [mfderiv_comp x (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) (hKc hx))]
    exact (hiF x hx).comp (PartialChart.bijective_mfderiv c (hKc hx)).1
  obtain ⟨A, hA, hpreA⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  have hfA : Set.MapsTo f K A := by
    intro x hx
    change c x ∈ F ⁻¹' A
    rw [hpreA]
    exact c.map_source' (hKc hx)
  obtain ⟨ε, hε, Φ, hprod, hsource, htarget, hzero, himage⟩ :=
    exists_clean_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar c.open_source hKc hembf
      hi n hcodim (hO.inter hA) (fun x hx => ⟨hFO hx, hfA hx⟩)
  refine ⟨ε, hε, Φ, hprod, hsource, fun _ hy => (htarget hy).1, hzero, ?_⟩
  intro q hq
  have hqA := (htarget (Φ.map_source' hq)).2
  have hrange : Φ q ∈ Set.range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨y, hy⟩
      have hyA : F y ∈ A := hy ▸ hqA
      have hyT : y ∈ c.target := by
        change y ∈ F ⁻¹' A at hyA
        rwa [hpreA] at hyA
      exact ⟨c.invFun y, c.map_target' hyT, (congrArg F (c.right_inv' hyT)).trans hy⟩
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  exact hrange.trans (himage q hq)
