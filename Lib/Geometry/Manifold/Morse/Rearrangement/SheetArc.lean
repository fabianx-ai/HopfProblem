/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative
public import Lib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Morse.Rearrangement.TransverseChart
/-!
# Sheet arcs in a five-dimensional level (proof-specific)

Two statements fixed at `Module.finrank ℝ E = 5` with sheets modelled on
`EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)`: the middle level of the six-manifold of
the W4W1 argument, where the descending and ascending spheres of index-3 critical points are
two-spheres. `MorseCancellation.exists_sheet_arc_tube`: an embedded arc with injective
differential admits a tubular chart matching prescribed endpoint charts up to a linear
transverse correction (`linearTransverseChart`). `exists_clean_two_sheet_arc_avoiding`: two
embedded two-sheets `f`, `g` with a path between chosen points admit clean endpoint charts and a
smooth embedded arc between them meeting `range f` only at `0`, `range g` only at `1`, and
avoiding a closed smooth two-dimensional image `range b`.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! 

/-- An embedded arc with injective differential admits a tubular sheet chart. -/
theorem MorseCancellation.exists_sheet_arc_tube {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {a : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a)
    (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart
                      ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr R)
                      Φ₁) ∧
                  Φ.target ⊆ O := by
  have h0K : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1K : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨r, hr, Ξ, hΞprod, hΞaxis, hΞO⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero ha
      CompactIccSpace.isCompact_Icc h0K ((convex_Icc (0 : ℝ) 1).starConvex h0K) hinj hi 4
      (by rw [Module.finrank_self, hdim]) hO haO
  let L :
    ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])
  let P := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L).toDiffeomorph
  let Ψ := P.toPartialDiffeomorph'.trans Ξ
  have hΨaxis (t : ℝ) : Ψ (t, 0) = a t := by
    change Ξ (t, L 0) = a t
    rw [map_zero, hΞaxis]
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change
      (t, (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Set.univ ∧
        (t, L 0) ∈ Ξ.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hΞprod ⟨ht, Metric.mem_closedBall_self hr.le⟩⟩
  have hΨ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Ψ.source :=
    hzero ⟨h0K, rfl⟩
  have hΨ₁ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Ψ.source :=
    hzero ⟨h1K, rfl⟩
  have haxis₀ : (fun t : ℝ => Φ₀ (t, 0)) =ᶠ[𝓝 (0 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hleft] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  have haxis₁ : (fun t : ℝ => Φ₁ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  obtain ⟨R, hsign⟩ :=
    exists_compatible_sheet_endpoint_orientation (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 2)))
      ⟨0, by simp only [finrank_euclideanSpace_fin]; norm_num⟩ Ψ Φ₀ Φ₁ hΨ₀ hΨ₁ hΦ₀ hΦ₁ haxis₀
      haxis₁
  let C := (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr R
  let Φ₂ := linearTransverseChart C Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source C Φ₁ 1).mpr hΦ₁
  have haxis₂ : (fun t : ℝ => Φ₂ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [haxis₁] with t ht
    exact (linearTransverseChart_axis C Φ₁ t).trans ht
  let _ :
    Nontrivial
      (Fin (Module.finrank ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) :=
    Fin.nontrivial_iff_two_le.mpr
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
        norm_num)
  obtain ⟨ε, hε, Φ, hprod, htarget, haxis, hgl, hgr⟩ :=
    AxisCoordinates.exists_native_axis_chart_with_endpoint_germs
      (Module.finBasis ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) Ψ Φ₀ Φ₂
      zero_lt_one CompactIccSpace.isCompact_Icc hzero hΨ₀ hΨ₁ hΦ₀ hΦ₂ haxis₀ haxis₂ hsign
  exact
    ⟨R, ε, hε, Φ, hprod, fun t => (haxis t).trans (hΨaxis t), hgl, hgr, fun z hz =>
      hΞO (htarget hz).1⟩

/-! ### Longitudinal tube motions -/

/-- Two endpoint sheets admit a clean arc avoiding a closed set. -/
theorem MorseCancellation.exists_clean_two_sheet_arc_avoiding {E M X Y Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    {f : X → M} {g : Y → M} {b : Z → M} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g) (hfe : Topology.IsEmbedding f)
    (hge : Topology.IsEmbedding g) (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hx : f x ∉ Set.range g) (hy : g y ∉ Set.range f) (hbx : f x ∉ Set.range b)
    (hby : g y ∉ Set.range b) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source ∧
        ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source ∧
          Φ 0 = f x ∧
            Ψ (1, 0) = g y ∧
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
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range g ↔ t = 1) ∧
                                  Set.MapsTo a (Set.Icc (0 : ℝ) 1) (Set.range b)ᶜ := by
  obtain ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, -⟩ :=
    exists_clean_two_sheet_arc hf hg hfe hge hfi hgi hdim x y hx hy γ
  let o : C((X ⊕ Y) ⊕ Z, M) :=
    ⟨Sum.elim (Sum.elim f g) b, (hf.continuous.sumElim hg.continuous).sumElim hb.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := (hf.sumElim hg).sumElim hb
  have horange : Set.range o = (Set.range f ∪ Set.range g) ∪ Set.range b := by
    ext z
    constructor
    · rintro ⟨(a | c) | d, he⟩
      · exact Or.inl (Or.inl ⟨a, he⟩)
      · exact Or.inl (Or.inr ⟨c, he⟩)
      · exact Or.inr ⟨d, he⟩
    · rintro ((⟨a, he⟩ | ⟨c, he⟩) | ⟨d, he⟩)
      · exact ⟨Sum.inl (Sum.inl a), he⟩
      · exact ⟨Sum.inl (Sum.inr c), he⟩
      · exact ⟨Sum.inr d, he⟩
  have hoclosed : IsClosed (Set.range o) := by
    rw [horange]
    exact
      ((isCompact_range hf.continuous).isClosed.union
            (isCompact_range hg.continuous).isClosed).union
        hbc
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨V, hV, h1V, hVΨ, hc, hic⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hnear0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∉ Set.range b :=
    (ha.contMDiffAt (hU.mem_nhds h0U)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Φ 0 ∉ Set.range b; rw [hΦx]; exact hbx))
  have hnear1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∉ Set.range b :=
    (hc.contMDiffAt (hV.mem_nhds h1V)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Ψ (1, 0) ∉ Set.range b; rw [hΨy]; exact hby))
  have hclean0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 0 := by
    filter_upwards [hU.mem_nhds h0U, hnear0] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
    · exact (hb' h).elim
  have hclean1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 1 := by
    filter_upwards [hV.mem_nhds h1V, hnear1] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact (hΨavoid (Ψ.map_source' (hVΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hVΨ t ht)).mp h).1
    · exact (hb' h).elim
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact fun h => hx ⟨y, h.symm⟩
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hc hU hV h0U h1V hia hic (γ.cast hΦx hΨy) hends
      (by omega) o ho hoclosed (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0
      hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦrec, hΨrec, a, ha', hleft, hright, hemb, hi, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl (Or.inl h))
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
          (horange.symm ▸ Or.inl (Or.inr h))
    · intro he
      subst t
      rw [ha1]
      exact Set.mem_range_self y
  · intro t ht htb
    have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at htb; exact hbx htb
    have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at htb; exact hby htb
    exact
      havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        (horange.symm ▸ Or.inr htb)
