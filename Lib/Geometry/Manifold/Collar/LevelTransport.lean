/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Collar.HeightCollar
public import Lib.Geometry.Manifold.Collar.SmallPerturbation
public import Lib.Geometry.Manifold.Collar.SupportedDiffeomorph

/-!
# Ambient transport of regular levels

Let `f : M → ℝ` be smooth on a compact manifold. If `b` is a regular value, then for small `t`
there is a diffeomorphism of `M`, the identity off a compact subset of a collar of `f⁻¹(b)`,
carrying `f⁻¹(b)` onto `f⁻¹(b + t)` and `{f ≤ b}` onto `{f ≤ b + t}`
(`RegularLevel.exists_nearby_ambient_level_diffeomorphs`): in a height collar it is a bump
translation of the `ℝ` coordinate. By connectedness of `[a, b]`, if `f` has no critical value in
`[a, b]` there is a diffeomorphism of `M` carrying `f⁻¹(a)` onto `f⁻¹(b)` and `{f ≤ a}` onto
`{f ≤ b}` (`RegularLevel.exists_ambient_regularBand_transport`); this is the first fundamental
theorem of Morse theory in its diffeomorphism form (Milnor, *Morse Theory*, Thm 3.1; *Lectures on
the h-cobordism theorem*, Thm 3.4).

## Main definitions and results

* `RegularLevel.AmbientEquivalent` : two levels related by a diffeomorphism of `M` that also
  matches the sublevels; an equivalence relation.
* `RegularLevel.exists_ambientTransport_of_heightCollar`
* `RegularLevel.exists_ambient_regularBand_transport`
* `RegularLevel.exists_levelDiffeomorph_of_ambient` : an ambient diffeomorphism matching two
  regular levels restricts to a diffeomorphism between them.

## References

* [milnor63] J. Milnor, *Morse Theory*, Thm 3.1
* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3

## Tags

regular level, sublevel set, ambient diffeomorphism, Morse theory
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

/-! ### Ambient transport of level sets -/

/-- A large height difference gives the shift inequality. -/
theorem RegularLevel.le_shift_iff_of_abs_sub_ge {u b t ε : ℝ} (ht : |t| < ε)
    (hu : ε ≤ |u - b|) : u ≤ b + t ↔ u ≤ b := by
  by_cases hbelow : u ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hbelow)] at hu
    exact ⟨fun _ => hbelow, fun _ => by linarith [(abs_lt.mp ht).1]⟩
  · have habove : b ≤ u := le_of_not_ge hbelow
    rw [abs_of_nonneg (sub_nonneg.mpr habove)] at hu
    constructor <;> intro hh <;> exfalso <;> linarith [(abs_lt.mp ht).2]

/-- A height collar gives an ambient transport between levels. -/
theorem RegularLevel.exists_ambientTransport_of_heightCollar {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) (ε : ℝ) (hε : 0 < ε) :
    letI := chartedSpace hf hreg
    ∀ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
      ((Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source) →
        (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) →
          (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) →
            (f ⁻¹' Metric.ball b ε ⊆ Ψ.target) →
              ∃ δ : ℝ,
                0 < δ ∧
                  δ ≤ ε ∧
                    ∃ K : Set M,
                      IsCompact K ∧
                        K ⊆ Ψ.target ∧
                          ∀ t : ℝ,
                            |t| < δ →
                              ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                                (∀ y, y ∉ K → D y = y) ∧
                                  (∀ x : { x : M // f x = b }, D x = Ψ (x, t)) ∧
                                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro Ψ hsource hzero hheight hband
  obtain ⟨β, hβ, hsupp, W, -, hW, -, hβW⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {(0 : ℝ)}) (U :=
      Metric.ball (0 : ℝ) ε) isClosed_singleton Metric.isOpen_ball
      (by
        simpa only [Set.singleton_subset_iff] using
          (Metric.mem_ball_self hε : (0 : ℝ) ∈ Metric.ball 0 ε))
  have hβ0 : β 0 = 1 := hβW (hW (Set.mem_singleton 0))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset (isClosed_tsupport β)
      (hsupp.trans Metric.ball_subset_closedBall)
  obtain ⟨η, hη, htranslations⟩ :=
    SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let C : Set ({ x : M // f x = b } × ℝ) := Set.univ ×ˢ tsupport β
  have hC : IsCompact C := isCompact_univ.prod hcompact
  have hCsource : C ⊆ Ψ.source := fun z hz =>
    hsource ⟨hz.1, Metric.ball_subset_closedBall (hsupp hz.2)⟩
  let K : Set M := Ψ '' C
  have hK : IsCompact K :=
    hC.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hKtarget : K ⊆ Ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Ψ.map_source' (hCsource hz)
  refine ⟨Min.min ε η, lt_min hε hη, min_le_left ε η, K, hK, hKtarget, ?_⟩
  intro t ht
  have htε : |t| < ε := lt_of_lt_of_le ht (min_le_left ε η)
  have htη : ‖t‖ < η := by
    simpa only [Real.norm_eq_abs] using lt_of_lt_of_le ht (min_le_right ε η)
  obtain ⟨d, hd, hdfix⟩ := htranslations t htη
  have hd0 : d 0 = t := by
    rw [hd 0, hβ0]
    simp
  have hdfar (s : ℝ) (hs : ε ≤ s) : d s = s := by
    apply hdfix
    intro hsupps
    have hball : |s| < ε := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsupp hsupps
    rw [abs_of_nonneg (hε.le.trans hs)] at hball
    exact (not_lt_of_ge hs) hball
  have hdmono : StrictMono d := by
    rcases d.contMDiff.continuous.strictMono_of_inj d.injective with hm | ha
    · exact hm
    · have hh := ha (show ε < ε + 1 by linarith)
      rw [hdfar ε le_rfl, hdfar (ε + 1) (by linarith)] at hh
      linarith
  let P := (Diffeomorph.refl 𝓘(ℝ, Model E) { x : M // f x = b } ∞).prodCongr d
  have hPfix : ∀ z, z ∉ C → P z = z := by
    intro z hz
    have hzβ : z.2 ∉ tsupport β := fun hh => hz ⟨Set.mem_univ z.1, hh⟩
    exact Prod.ext rfl (hdfix z.2 hzβ)
  let D := SupportedDiffeomorph.extension Ψ P hC hCsource hPfix
  have hpoint (x : { x : M // f x = b }) : D x = Ψ (x, t) := by
    have hx0 : (x, 0) ∈ Ψ.source := hsource ⟨Set.mem_univ x, Metric.mem_closedBall_self hε.le⟩
    have hP0 : P (x, 0) = (x, t) := by exact Prod.ext rfl hd0
    have hh := SupportedDiffeomorph.extension_chart Ψ P hC hCsource hPfix hx0
    change D (Ψ (x, 0)) = Ψ (P (x, 0)) at hh
    rwa [hzero x, hP0] at hh
  refine ⟨D, ?_, hpoint, ?_, ?_⟩
  · intro y hy
    exact SupportedDiffeomorph.extension_eq_of_notMem_image Ψ P hC hCsource hPfix hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z : { x : M // f x = b } := ⟨x, hx⟩
      have hDx : D x = Ψ (z, t) := hpoint z
      change f (D x) = b + t
      rw [hDx]
      exact
        hheight (z, t)
          (hsource
            ⟨Set.mem_univ z, by
              simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using htε.le⟩)
    · intro hy
      have hy' : f y = b + t := hy
      have hyTarget : y ∈ Ψ.target := by
        apply hband
        change Dist.dist (f y) b < ε
        simpa only [hy', Real.dist_eq, add_sub_cancel_left] using htε
      have hback := Ψ.map_target' hyTarget
      have hright : Ψ (Ψ.symm y) = y := Ψ.right_inv' hyTarget
      have htime : (Ψ.symm y).2 = t := by
        have hh := hheight (Ψ.symm y) hback
        rw [hright, hy'] at hh
        linarith
      refine ⟨((Ψ.symm y).1 : M), (Ψ.symm y).1.property, ?_⟩
      have hpair : ((Ψ.symm y).1, t) = Ψ.symm y := Prod.ext rfl htime.symm
      exact (hpoint (Ψ.symm y).1).trans ((congrArg Ψ hpair).trans hright)
  · have hsublevel (y : M) : f (D y) ≤ b + t ↔ f y ≤ b := by
      by_cases hy : y ∈ Ψ.target
      · let z := Ψ.symm y
        have hz : z ∈ Ψ.source := Ψ.map_target' hy
        have hPz : P z ∈ Ψ.source :=
          SupportedDiffeomorph.mapsTo_source Ψ P.toEquiv hCsource hPfix hz
        have hDy : D y = Ψ (P z) := SupportedDiffeomorph.extendMap_of_mem Ψ P hy
        have hfy : f y = b + z.2 := by
          have hh := hheight z hz
          have hzy : Ψ z = y := Ψ.right_inv' hy
          rwa [hzy] at hh
        have hfd : f (D y) = b + d z.2 := by
          rw [hDy]
          exact hheight (P z) hPz
        have horder : d z.2 ≤ t ↔ z.2 ≤ 0 := by
          rw [← hd0]
          exact hdmono.le_iff_le
        rw [hfd, hfy]
        constructor
        · intro hh
          have hz0 := horder.mp (by linarith)
          linarith
        · intro hh
          have hdz := horder.mpr (by linarith)
          linarith
      · have hDy : D y = y :=
          SupportedDiffeomorph.extension_eq_of_notMem_target Ψ P hC hCsource hPfix hy
        rw [hDy]
        have hfar : ε ≤ |f y - b| := by
          apply le_of_not_gt
          intro hh
          apply hy
          apply hband
          change Dist.dist (f y) b < ε
          simpa only [Metric.mem_ball, Real.dist_eq] using hh
        exact le_shift_iff_of_abs_sub_ge htε hfar
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hsublevel x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := D.surjective y
      exact ⟨x, (hsublevel x).mp hy, rfl⟩

/-- Nearby ambient levels are diffeomorphic when nonempty. -/
theorem RegularLevel.exists_nearby_ambient_level_diffeomorphs_of_nonempty {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ K : Set M,
          IsCompact K ∧
            ∀ t : ℝ,
              |t| < δ →
                ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                  (∀ y, y ∉ K → D y = y) ∧
                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight, hband⟩ := exists_heightCollar_with_band hf hreg
  obtain ⟨δ, hδ, -, K, hK, -, htransport⟩ :=
    exists_ambientTransport_of_heightCollar hf hreg ε hε Ψ hsource hzero hheight hband
  refine ⟨δ, hδ, K, hK, ?_⟩
  intro t ht
  obtain ⟨D, hfix, -, hlevel, hsublevel⟩ := htransport t ht
  exact ⟨D, hfix, hlevel, hsublevel⟩

/-- Nearby ambient levels are diffeomorphic. -/
theorem RegularLevel.exists_nearby_ambient_level_diffeomorphs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ K : Set M,
          IsCompact K ∧
            ∀ t : ℝ,
              |t| < δ →
                ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                  (∀ y, y ∉ K → D y = y) ∧
                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  classical
  by_cases hb : Nonempty { x : M // f x = b }
  · let _ := hb
    exact exists_nearby_ambient_level_diffeomorphs_of_nonempty hf hreg
  · have hlevel : ∀ x, f x = b → x ∈ (∅ : Set M) := fun x hx => (hb ⟨⟨x, hx⟩⟩).elim
    obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous isOpen_empty hlevel
    refine ⟨δ, hδ, ∅, isCompact_empty, ?_⟩
    intro t ht
    refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, fun _ _ => rfl, ?_, ?_⟩
    · change id '' {x : M | f x = b} = {x : M | f x = b + t}
      rw [Set.image_id]
      ext x
      constructor
      · intro hx
        exact (hb ⟨⟨x, hx⟩⟩).elim
      · intro hx
        have hball : x ∈ f ⁻¹' Metric.ball b δ := by
          change Dist.dist (f x) b < δ
          simpa only [show f x = b + t from hx, Real.dist_eq, add_sub_cancel_left] using ht
        exact (hband hball).elim
    · change id '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t}
      rw [Set.image_id]
      ext x
      have hfar : δ ≤ |f x - b| := by
        apply le_of_not_gt
        intro hh
        apply hband
        change Dist.dist (f x) b < δ
        simpa only [Real.dist_eq] using hh
      exact (le_shift_iff_of_abs_sub_ge ht hfar).symm

/-! ### Ambient equivalence of levels -/

/-- Two levels are ambiently equivalent if a transport diffeomorphism exists. -/
def RegularLevel.AmbientEquivalent {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a b : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
    D '' {x : M | f x = a} = {x : M | f x = b} ∧ D '' {x : M | f x ≤ a} = {x : M | f x ≤ b}

/-- Ambient equivalence is reflexive. -/
theorem RegularLevel.ambientEquivalent_refl {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a : ℝ) :
    AmbientEquivalent (E := E) f a a := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, ?_, ?_⟩ <;> exact Set.image_id _

/-- Ambient equivalence is symmetric. -/
theorem RegularLevel.ambientEquivalent_symm {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b : ℝ}
    (h : AmbientEquivalent (E := E) f a b) : AmbientEquivalent (E := E) f b a := by
  obtain ⟨D, hlevel, hsublevel⟩ := h
  have hreverse (S T : Set M) (hST : D '' S = T) : D.symm '' T = S := by
    rw [← hST, Set.image_image]
    have heq : (fun x : M => D.symm (D x)) = id := funext D.symm_apply_apply
    rw [heq, Set.image_id]
  exact ⟨D.symm, hreverse _ _ hlevel, hreverse _ _ hsublevel⟩

/-- Ambient equivalence is transitive. -/
theorem RegularLevel.ambientEquivalent_trans {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b c : ℝ}
    (hab : AmbientEquivalent (E := E) f a b) (hbc : AmbientEquivalent (E := E) f b c) :
    AmbientEquivalent (E := E) f a c := by
  obtain ⟨e, he, he'⟩ := hab
  obtain ⟨d, hd, hd'⟩ := hbc
  refine ⟨e.trans d, ?_, ?_⟩
  · change (fun x => d (e x)) '' {x : M | f x = a} = {x : M | f x = c}
    rw [← Set.image_image, he, hd]
  · change (fun x => d (e x)) '' {x : M | f x ≤ a} = {x : M | f x ≤ c}
    rw [← Set.image_image, he', hd']

/-- An ambient transport across a regular band exists. -/
theorem RegularLevel.exists_ambient_regularBand_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧ D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} := by
  classical
  let B := Set.Icc a b
  let left : B := ⟨a, ⟨le_rfl, hab⟩⟩
  let right : B := ⟨b, ⟨hab, le_rfl⟩⟩
  let reg (t : B) : ∀ x, f x = (t : ℝ) → x ∉ ManifoldMorse.criticalPoints E f := fun x hx =>
    hband x (hx ▸ t.property)
  let P : B → Prop := fun t => AmbientEquivalent (E := E) f a (t : ℝ)
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro t
    obtain ⟨δ, hδ, K, -, htransport⟩ := exists_nearby_ambient_level_diffeomorphs hf (reg t)
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hdist : |(s : ℝ) - (t : ℝ)| < δ := by
      change Dist.dist (s : ℝ) (t : ℝ) < δ at hs
      simpa only [Real.dist_eq] using hs
    obtain ⟨D, -, hlevel, hsublevel⟩ := htransport ((s : ℝ) - (t : ℝ)) hdist
    have hts : AmbientEquivalent (E := E) f (t : ℝ) (s : ℝ) := by
      have heq : (t : ℝ) + ((s : ℝ) - (t : ℝ)) = (s : ℝ) := by ring
      refine ⟨D, ?_, ?_⟩
      · simpa only [heq] using hlevel
      · simpa only [heq] using hsublevel
    apply propext
    constructor
    · intro hs
      exact ambientEquivalent_trans hs (ambientEquivalent_symm hts)
    · intro ht
      exact ambientEquivalent_trans ht hts
  let _ : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hconstant : P left = P right := hlocal.apply_eq_of_preconnectedSpace left right
  have hleft : P left := ambientEquivalent_refl f a
  have hright : P right := hconstant ▸ hleft
  exact hright

/-- Ambiently equivalent levels are diffeomorphic. -/
theorem RegularLevel.exists_levelDiffeomorph_of_ambient {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hlevel : D '' {x : M | f x = a} = {x : M | f x = b}) :
    letI := chartedSpace hf ha
    letI := chartedSpace hf hb
    ∃ e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) { x : M // f x = a } { x : M // f x = b } ∞,
      ∀ x, (e x : M) = D x := by
  let _ := chartedSpace hf ha
  let _ := chartedSpace hf hb
  have hiff (x : M) : f x = a ↔ f (D x) = b := by
    constructor
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := ⟨x, hx, rfl⟩
      rwa [hlevel] at hh
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := by rw [hlevel]; exact hx
      obtain ⟨z, hz, hzx⟩ := hh
      exact D.injective hzx ▸ hz
  let e := D.toHomeomorph.subtype (p := fun x => f x = a) (q := fun x => f x = b) hiff
  have he : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e :=
    (contMDiff_iff_inclusion hf hb 𝓘(ℝ, Model E) e).mpr
      (D.contMDiff.comp (RegularLevel.contMDiff_inclusion hf ha))
  have hei : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e.symm :=
    (contMDiff_iff_inclusion hf ha 𝓘(ℝ, Model E) e.symm).mpr
      (D.symm.contMDiff.comp (RegularLevel.contMDiff_inclusion hf hb))
  let F : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) { x : M // f x = a } { x : M // f x = b } ∞ :=
    { e.toEquiv with
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  exact ⟨F, fun _ => rfl⟩
