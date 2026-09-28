/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood
public import Lib.Geometry.Manifold.Immersion.Relative.Arc

/-!
# Clean charts along an arc joining two embedded surfaces

The configuration from which the Whitney trick starts: two embedded immersed surfaces
`f : X → M`, `g : Y → M` in a five-manifold `M`, a point `f x ∉ range g`, a point `g y ∉ range f`
and a path from `f x` to `g y`. `MorseCancellation.exists_clean_two_sheet_arc` produces an embedded
immersed arc from `f x` to `g y` which meets `range f` only at its initial point and `range g` only
at its terminal point, together with charts `ℝ × (ℝ² × ℝ²) → M` at the two endpoints in which the
sheets are the coordinate planes `{z.1 = 0, z.2.2 = 0}`, `{z.1 = 1, z.2.1 = 0}` and the arc is the
first axis. The surfaces are not assumed disjoint.

The charts come from `MorseCancellation.exists_clean_sheet_axis_chart`: around any point of an
embedded immersed submanifold of codimension `1 + n` there is a chart `ℝ × (D × ℝⁿ) → M` in which
the submanifold is `{z.1 = 0 ∧ z.2.2 = 0}`, obtained from the clean tubular neighbourhood of
`Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood` and the coordinate shuffle
`MorseCancellation.sheetAxisShuffle`. `MorseCancellation.chart_axis_curve_properties` records that
the axis curve `t ↦ Φ (t, 0)` of a chart is a smooth immersed curve, and
`MorseCancellation.terminalSheetCoordinates` exchanges the two `D` blocks.

## References

* Milnor, *Lectures on the h-cobordism theorem*, §6 (the Whitney trick).
* Hirsch, *Differential Topology*, Ch. 3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- The linear isomorphism `ℝ × (D × B) ≃L[ℝ] D × (ℝ × B)` exchanging the axis coordinate with the
first block. -/
def MorseCancellation.sheetAxisShuffle {D B : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : (ℝ × (D × B)) ≃L[ℝ] (D × (ℝ × B))
    where
  toLinearEquiv :=
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun p => (p.2.1, (p.1, p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  continuous_invFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)

/-- Axis-adapted clean chart: for an embedded immersed `f : X → M` of codimension `1 + n`, every
point of the image has a chart `ℝ × (D × ℝⁿ) → M` in which the image of `f` is exactly `{z | z.1
= 0 ∧ z.2.2 = 0}`. -/
theorem MorseCancellation.exists_clean_sheet_axis_chart {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {E M X : Type*} [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X] [ChartedSpace D X]
    [IsManifold 𝓘(ℝ, D) ∞ X] {f : X → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hemb : Topology.IsEmbedding f) (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hdim : Module.finrank ℝ D + (1 + n) = Module.finrank ℝ E) (x : X) {U : Set M}
    (hU : IsOpen U) (hxU : f x ∈ U) :
    ∃ Φ :
      PartialDiffeomorph 𝓘(ℝ, ℝ × (D × EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, E)
        (ℝ × (D × EuclideanSpace ℝ (Fin n))) M ∞,
      (0 : ℝ × (D × EuclideanSpace ℝ (Fin n))) ∈ Φ.source ∧
        Φ 0 = f x ∧ Φ.target ⊆ U ∧ ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0 := by
  let c := NativeParametrization.centered (D := D) x
  have hc0 : (0 : D) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  obtain ⟨ε, hε, Q, hprod, -, hQU, hzero, hrecognition⟩ :=
    exists_clean_embedded_sheet_neighborhood hf hemb c isCompact_singleton
      (Set.mem_singleton (0 : D)) (starConvex_singleton (0 : D))
      (Set.singleton_subset_iff.mpr hc0) (fun z _ => hi (c z)) (1 + n) hdim hU
      (show Set.MapsTo (f ∘ c) {0} U by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        change f (c 0) ∈ U
        rw [hcx]
        exact hxU)
  let B := EuclideanSpace ℝ (Fin n)
  let N := EuclideanSpace ℝ (Fin (1 + n))
  let L : (ℝ × B) ≃L[ℝ] N :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [B, N, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin])
  let P : (ℝ × (D × B)) ≃L[ℝ] (D × N) :=
    (sheetAxisShuffle (D := D) (B := B)).trans ((ContinuousLinearEquiv.refl ℝ D).prodCongr L)
  let Φ := P.toDiffeomorph.toPartialDiffeomorph'.trans Q
  have hQ0 : (0 : D × N) ∈ Q.source :=
    hprod ⟨Set.mem_singleton 0, Metric.mem_closedBall_self hε.le⟩
  have hΦ0 : (0 : ℝ × (D × B)) ∈ Φ.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change P 0 ∈ Q.source
    rw [map_zero]
    exact hQ0
  refine ⟨Φ, hΦ0, ?_, fun z hz => hQU hz.1, ?_⟩
  · change Q (P 0) = f x
    rw [map_zero]
    exact (hzero 0 hQ0).trans (congrArg f hcx)
  · intro z hz
    change Q (P z) ∈ Set.range f ↔ _
    rw [hrecognition (P z) hz.2]
    change L (z.1, z.2.2) = 0 ↔ z.1 = 0 ∧ z.2.2 = 0
    constructor
    · intro h
      have he : (z.1, z.2.2) = (0, (0 : B)) := L.injective (h.trans L.map_zero.symm)
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact L.map_zero

/-- The axis curve `t ↦ Φ (t, 0)` of a chart is defined, smooth and immersive on a neighbourhood of
any parameter whose axis point lies in the chart's source. -/
theorem MorseCancellation.chart_axis_curve_properties {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) (p : ℝ) (hp : (p, (0 : V)) ∈ Φ.source) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        p ∈ U ∧
          (∀ t ∈ U, (t, (0 : V)) ∈ Φ.source) ∧
            ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (fun t => Φ (t, (0 : V))) U ∧
              Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => Φ (t, (0 : V))) p) := by
  let L := ContinuousLinearMap.inl ℝ ℝ V
  have hL : ContDiff ℝ ∞ L := L.contDiff
  let U : Set ℝ := L ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage L.continuous
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (Φ ∘ L) U :=
    Φ.contMDiffOn_toFun.comp hL.contMDiff.contMDiffOn (fun _ ht => ht)
  refine ⟨U, hU, hp, fun _ ht => ht, hcurve, ?_⟩
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Φ ∘ L) p)
  rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp)
      (hL.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, L.fderiv]
  exact
    (PartialChart.bijective_mfderiv Φ hp).injective.comp (fun _ _ h => congrArg Prod.fst h)

/-- The diffeomorphism of `ℝ × (D × D)` exchanging the two `D` blocks, used to put the second sheet
of a two-sheet configuration in terminal position. -/
def MorseCancellation.terminalSheetCoordinates {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    Diffeomorph 𝓘(ℝ, ℝ × (D × D)) 𝓘(ℝ, ℝ × (D × D)) (ℝ × (D × D)) (ℝ × (D × D)) ∞
    where
  toEquiv :=
    { toFun := fun z => (z.1 - 1, (z.2.2, z.2.1))
      invFun := fun z => (z.1 + 1, (z.2.2, z.2.1))
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  contMDiff_toFun :=
    ((contDiff_fst.sub contDiff_const).prodMk
        (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff
  contMDiff_invFun :=
    ((contDiff_fst.add contDiff_const).prodMk
        (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff

/-- Two embedded immersed surfaces `f : X → M`, `g : Y → M` in a five-manifold, together with a
point `x` whose image `f x` is off `range g`, a point `y` whose image `g y` is off `range f`, and a
path from `f x` to `g y`, admit adapted clean charts at the two endpoints and an embedded immersed
arc joining them which meets `range f` only at its initial point and `range g` only at its terminal
point.  The two surfaces are *not* assumed disjoint: only the two endpoints are required to lie off
the other surface.  This is the configuration the Whitney trick starts from (Hirsch, *Differential
Topology*, Ch. 3; Milnor, *Lectures on the h-cobordism theorem*, §6). -/
theorem MorseCancellation.exists_clean_two_sheet_arc {E M X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : Topology.IsEmbedding f) (hge : Topology.IsEmbedding g)
    (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y)) (hdim : Module.finrank ℝ E = 5)
    (x : X) (y : Y) (hx : f x ∉ Set.range g) (hy : g y ∉ Set.range f) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source ∧
        ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source ∧
          Φ 0 = f x ∧
            Ψ (1, 0) = g y ∧
              Φ.target ⊆ (Set.range g)ᶜ ∧
                Ψ.target ⊆ (Set.range f)ᶜ ∧
                  (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                    (∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                      ∃ a : C(ℝ, M),
                        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
                          (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
                            (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
                              Topology.IsClosedEmbedding (fun t : unitInterval => a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range f ↔ t = 0) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range g ↔ t = 1) := by
  have hclosedf : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hclosedg : IsClosed (Set.range g) := (isCompact_range hg.continuous).isClosed
  have hcodim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + (1 + 2) = Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin, hdim]
  obtain ⟨Φ, hΦ0, hΦx, hΦavoid, hΦrec⟩ :=
    exists_clean_sheet_axis_chart hf hfe hfi 2 hcodim x hclosedg.isOpen_compl hx
  obtain ⟨Q, hQ0, hQy, hQavoid, hQrec⟩ :=
    exists_clean_sheet_axis_chart hg hge hgi 2 hcodim y hclosedf.isOpen_compl hy
  let T := terminalSheetCoordinates (D := (EuclideanSpace ℝ (Fin 2)))
  let Ψ := T.toPartialDiffeomorph'.trans Q
  have hT1 : T ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) = 0 := by
    change ((1 : ℝ) - 1, ((0 : (EuclideanSpace ℝ (Fin 2))), (0 : (EuclideanSpace ℝ (Fin 2))))) = 0
    rw [sub_self]
    rfl
  have hΨ1 :
    ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change T (1, 0) ∈ Q.source
    rw [hT1]
    exact hQ0
  have hΨy : Ψ (1, 0) = g y := by
    change Q (T (1, 0)) = g y
    rw [hT1]
    exact hQy
  have hΨavoid : Ψ.target ⊆ (Set.range f)ᶜ := fun z hz => hQavoid hz.1
  have hΨrec : ∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Q (T z) ∈ Set.range g ↔ _
    rw [hQrec (T z) hz.2]
    change z.1 - 1 = 0 ∧ z.2.1 = 0 ↔ _
    rw [sub_eq_zero]
  let o : C(X ⊕ Y, M) := ⟨Sum.elim f g, hf.continuous.sumElim hg.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := hf.sumElim hg
  have horange : Set.range o = Set.range f ∪ Set.range g := by
    ext z
    constructor
    · rintro ⟨a | b, he⟩
      · exact Or.inl ⟨a, he⟩
      · exact Or.inr ⟨b, he⟩
    · rintro (⟨a, he⟩ | ⟨b, he⟩)
      · exact ⟨Sum.inl a, he⟩
      · exact ⟨Sum.inr b, he⟩
  have hoclosed : IsClosed (Set.range o) := by rw [horange]; exact hclosedf.union hclosedg
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨W, hW, h1W, hWΨ, hb, hib⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hclean0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 0 := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [horange]
    rintro (h | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
  have hclean1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 1 := by
    filter_upwards [hW.mem_nhds h1W] with t ht
    rw [horange]
    rintro (h | h)
    · exact (hΨavoid (Ψ.map_source' (hWΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hWΨ t ht)).mp h).1
  have hxy : f x ≠ g y := fun h => hx ⟨y, h.symm⟩
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact hxy
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib (γ.cast hΦx hΨy) hends
      (by omega) o ho hoclosed (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0
      hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine
    ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, a, ha', hleft, hright, hemb, hi,
      ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl h)
    · intro he
      subst t
      rw [ha0]
      exact Set.mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inr h)
    · intro he
      subst t
      rw [ha1]
      exact Set.mem_range_self y
