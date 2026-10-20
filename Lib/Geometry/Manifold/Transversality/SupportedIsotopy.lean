/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Diffeomorph
/-!
# Compactly supported isotopies

Constructions of isotopies of diffeomorphisms that are the identity outside a compact set:
transport of a relative isotopy through a partial diffeomorphism (isotopy extension through a
chart), fibrewise bump translations of a product, the realisation of a smooth germ by a small
compactly supported map, the isotopy realising a linear shear near the origin, and the inverse of a
diffeomorphism isotopic to the identity.

## Main results

* `SupportedDiffeomorph.SupportedRelativeIsotopy.extension`,
  `SupportedDiffeomorph.exists_supported_isotopy_extension`
* `SupportedDiffeomorph.exists_radius_normalBumpFamily`
* `exists_small_supported_germ`
* `SupportedDiffeomorph.exists_supported_shear_isotopy`
* `SupportedDiffeomorph.IsotopicToIdentity.symm`

## References

* cf. [M. Hirsch, *Differential Topology*][hirsch76], Ch. 8 §1 (isotopy extension).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- An isotopy supported in `K` preserves every set containing `K`. -/
theorem SupportedDiffeomorph.SupportedRelativeIsotopy.mapsTo_superset {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S) {U : Set X} (hKU : K ⊆ U)
    (t : ℝ) : Set.MapsTo (fun x => A.family (t, x)) U U := by
  obtain ⟨d, hd⟩ := A.slices t
  have hfix : ∀ x ∉ U, d x = x := by
    intro x hx
    exact (hd x).trans (A.fixedOutside t x (fun h => hx (hKU h)))
  intro x hx
  change A.family (t, x) ∈ U
  rw [← hd]
  exact SupportedDiffeomorph.mapsTo_of_fixed_outside d.toEquiv hfix hx

/-- The transport of a compactly supported relative isotopy through a partial diffeomorphism:
extending by the identity outside the image of the support gives a relative isotopy of the
target.
-/
def SupportedDiffeomorph.SupportedRelativeIsotopy.extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S)
    (Φ : PartialDiffeomorph I J X Y ∞) (hK : IsCompact K) (hKsource : K ⊆ Φ.source) {T : Set Y}
    (hfixed : ∀ x ∈ Φ.source, Φ x ∈ T → x ∈ S) :
    SupportedDiffeomorph.SupportedRelativeIsotopy
      (SupportedDiffeomorph.extension Φ e hK hKsource A.endpoint_fixed_outside) (Φ '' K) T
    where
  family := fun p => SupportedDiffeomorph.extendMap Φ (fun x => A.family (p.1, x)) p.2
  smooth :=
    SupportedDiffeomorph.contMDiff_extendFamily Φ A.smooth hK hKsource A.fixedOutside
      (A.mapsTo_superset hKsource)
  zero := by
    intro y
    have heq : (fun x => A.family (0, x)) = id := funext A.zero
    rw [heq]
    exact SupportedDiffeomorph.extendMap_id Φ y
  one := by
    intro y
    exact congrArg (fun f : X → X => SupportedDiffeomorph.extendMap Φ f y) (funext A.one)
  slices := by
    intro t
    obtain ⟨d, hd⟩ := A.slices t
    have hfix : ∀ x ∉ K, d x = x := fun x hx => (hd x).trans (A.fixedOutside t x hx)
    exact
      ⟨SupportedDiffeomorph.extension Φ d hK hKsource hfix, fun y =>
        congrArg (fun f : X → X => SupportedDiffeomorph.extendMap Φ f y) (funext hd)⟩
  fixedOutside := fun t y hy =>
    SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (A.fixedOutside t) hy
  fixedOn := by
    intro t y hy
    by_cases hyt : y ∈ Φ.target
    · rw [SupportedDiffeomorph.extendMap_of_mem Φ _ hyt]
      have hsource : Φ.symm y ∈ Φ.source := Φ.map_target' hyt
      have hi : Φ (Φ.symm y) = y := Φ.right_inv' hyt
      have hs : Φ.symm y ∈ S := hfixed (Φ.symm y) hsource (hi.symm ▸ hy)
      rw [A.fixedOn t (Φ.symm y) hs]
      exact hi
    · exact SupportedDiffeomorph.extendMap_of_notMem Φ _ hyt

/-- The isotopy of `M × P` which, in the chart `Φ`, translates the `M` coordinate by `-β(x) • b(u)`
at time `smoothTransition t` and leaves the `P` coordinate fixed; a fibrewise bump translation
of a chart.
-/
def SupportedDiffeomorph.normalBumpFamily {E F H M P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (p : ℝ × (M × P)) : M × P :=
  (bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1), p.2.2)

/-- The bump translation leaves the second factor fixed. -/
theorem SupportedDiffeomorph.normalBumpFamily_normal {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (t : ℝ) (z : M × P) :
    (normalBumpFamily Φ β b (t, z)).2 = z.2 :=
  rfl

/-- The bump translation is the identity at time zero. -/
theorem SupportedDiffeomorph.normalBumpFamily_zero {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (z : M × P) :
    normalBumpFamily Φ β b (0, z) = z := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 0 • b z.2), z.1) = z.1
    rw [Real.smoothTransition.zero, zero_smul, neg_zero, bumpFamily_zero]
  · rfl

/-- The bump translation fixes every fibre over a parameter where the translating field vanishes. -/
theorem SupportedDiffeomorph.normalBumpFamily_fixed_fiber {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {u : P} (hu : b u = 0)
    (t : ℝ) (x : M) : normalBumpFamily Φ β b (t, (x, u)) = (x, u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition t • b u), x) = x
    rw [hu, smul_zero, neg_zero, bumpFamily_zero]
  · rfl

/-- The bump translation is the identity outside the product of the two supports; it is compactly
supported.
-/
theorem SupportedDiffeomorph.normalBumpFamily_fixed_outside {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup P] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E)
    (t : ℝ) (z : M × P) (hz : z ∉ (Φ '' tsupport β) ×ˢ tsupport b) :
    normalBumpFamily Φ β b (t, z) = z := by
  by_cases hu : z.2 ∈ tsupport b
  · have hx : z.1 ∉ Φ '' tsupport β := fun hx => hz ⟨hx, hu⟩
    exact Prod.ext (bumpFamily_fixed_outside Φ β _ hx) rfl
  · have hb : b z.2 = 0 := by
      by_contra hb
      exact hu (subset_tsupport b hb)
    exact normalBumpFamily_fixed_fiber Φ β b hb t z.1

/-- At time one the bump translation reads in the chart as the translation `x ↦ x - β x • b u`. -/
theorem SupportedDiffeomorph.normalBumpFamily_chart {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {x : E} (hx : x ∈ Φ.source)
    (u : P) : normalBumpFamily Φ β b (1, (Φ x, u)) = (Φ (x - β x • b u), u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 1 • b u), Φ x) = _
    rw [Real.smoothTransition.one, one_smul, bumpFamily_chart Φ β _ hx, smul_neg, ←
      sub_eq_add_neg]
  · rfl

/-- For a compactly supported bump function in a chart there is a radius `ε` such that every
translating field of norm less than `ε` yields a bump translation which is smooth, a
diffeomorphism at each time, and compactly supported.
-/
theorem SupportedDiffeomorph.exists_radius_normalBumpFamily {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] [J.Boundaryless]
    [IsManifold J ∞ M] [T2Space M] {β : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ b : P → E,
          ContDiff ℝ ∞ b →
            HasCompactSupport b →
              (∀ u, ‖b u‖ < ε) →
                ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
                    (normalBumpFamily Φ β b) ∧
                  (∀ t,
                      ∃ D : Diffeomorph (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) (M × P) (M × P) ∞,
                        ∀ z, D z = normalBumpFamily Φ β b (t, z)) ∧
                    IsCompact ((Φ '' tsupport β) ×ˢ tsupport b) := by
  obtain ⟨ε, hε, hdiff, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro b hb hbcompact hbound
  have hsmall (t : ℝ) (u : P) : ‖-(Real.smoothTransition t • b u)‖ < ε := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact
      (mul_le_of_le_one_left (norm_nonneg (b u)) (Real.smoothTransition.le_one t)).trans_lt
        (hbound u)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hvec :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => Real.smoothTransition p.1 • b p.2.2) :=
    (hθ.comp contMDiff_fst).smul (hb.contMDiff.comp (contMDiff_snd.comp contMDiff_snd))
  have hneg :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => -(Real.smoothTransition p.1 • b p.2.2)) :=
    (show ContDiff ℝ ∞ (fun x : E => -x) from contDiff_neg).contMDiff.comp hvec
  have hparam :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (𝓘(ℝ, E).prod J) ∞
      (fun p : ℝ × (M × P) => (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) :=
    hneg.prodMk (contMDiff_fst.comp contMDiff_snd)
  have hfirst :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) J ∞
      (fun p : ℝ × (M × P) => bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) := by
    intro p
    exact (hsmooth _ (hsmall p.1 p.2.2)).comp p hparam.contMDiffAt
  refine ⟨hfirst.prodMk (contMDiff_snd.comp contMDiff_snd), ?_, ?_⟩
  · intro t
    have ht :
      ContMDiff (J.prod 𝓘(ℝ, P)) J ∞
        (fun z : M × P => bumpFamily Φ β (-(Real.smoothTransition t • b z.2), z.1)) :=
      hfirst.comp (contMDiff_const.prodMk contMDiff_id)
    have hslices :
      ∀ u : P,
        ∃ D : Diffeomorph J J M M ∞,
          ∀ x, D x = bumpFamily Φ β (-(Real.smoothTransition t • b u), x) :=
      fun u => hdiff _ (hsmall t u)
    have hlocal :
      IsLocalDiffeomorph (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) ∞
        (FiberwiseDiffeomorph.retainParameter fun z : M × P =>
          bumpFamily Φ β (-(Real.smoothTransition t • b z.2), z.1)) := by
      intro p
      exact
        isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ p)
          (FiberwiseDiffeomorph.contMDiff_retainParameter ht).contMDiffOn
          (FiberwiseDiffeomorph.isInvertible_mfderiv_retainParameter ht hslices p)
    refine ⟨IsLocalDiffeomorph.diffeomorph' hlocal ?_, fun _ => rfl⟩
    apply FiberwiseDiffeomorph.bijective_retainParameter
    intro s
    obtain ⟨d, hd⟩ := hslices s
    rw [show (fun x => bumpFamily Φ β (-(Real.smoothTransition t • b s), x)) = d from
      funext fun x => (hd x).symm]
    exact d.bijective
  · exact
      (hcompact.isCompact.image_of_continuousOn
            (Φ.contMDiffOn_toFun.continuousOn.mono hsupport)).prod
        hbcompact.isCompact

/-- A smooth map vanishing at the origin agrees near the origin with a compactly supported smooth
map of arbitrarily small norm, supported in a prescribed neighbourhood.
-/
theorem exists_small_supported_germ {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] {L : P → E} {U : Set P}
    (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hL : ContDiffOn ℝ ∞ L U) (hLzero : L 0 = 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ b : P → E,
      ContDiff ℝ ∞ b ∧
        HasCompactSupport b ∧ tsupport b ⊆ U ∧ (∀ u, ‖b u‖ < ε) ∧ b =ᶠ[𝓝 (0 : P)] L ∧ b 0 = 0 := by
  let V : Set P := U ∩ L ⁻¹' Metric.ball (0 : E) ε
  have hV : IsOpen V := hL.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hzeroV : (0 : P) ∈ V := ⟨hzero, by simpa [hLzero] using hε⟩
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff isCompact_singleton hV (Set.singleton_subset_iff.mpr hzeroV)
  let b : P → E := fun u => β u • L u
  have hfix (u : P) (hu : u ∉ tsupport β) : β u = 0 := by
    by_contra hne
    exact hu (subset_tsupport β hne)
  have hsmooth : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : u ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hu))
    · have hnot : u ∉ tsupport β := fun h => hu (hβsupport h).1
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) u := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hnot] with v hv
      change β v • L v = 0
      rw [hfix v hv, zero_smul]
  have hsupport : tsupport b ⊆ tsupport β := by
    apply closure_mono
    intro u hu hβu
    apply hu
    change β u • L u = 0
    rw [hβu, zero_smul]
  have hcompact : HasCompactSupport b :=
    HasCompactSupport.intro hβcompact.isCompact
      (fun u hu => by change β u • L u = 0; rw [hfix u hu, zero_smul])
  have hsmall (u : P) : ‖b u‖ < ε := by
    by_cases hu : u ∈ tsupport β
    · have hLu : ‖L u‖ < ε := mem_ball_zero_iff.mp (hβsupport hu).2
      change ‖β u • L u‖ < ε
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβrange u).1]
      exact (mul_le_of_le_one_left (norm_nonneg (L u)) (hβrange u).2).trans_lt hLu
    · change ‖β u • L u‖ < ε
      rw [hfix u hu, zero_smul, norm_zero]
      exact hε
  have hgerm : b =ᶠ[𝓝 (0 : P)] L := by
    filter_upwards [hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : P)))] with u hu
    change β u • L u = L u
    rw [hu, one_smul]
  exact
    ⟨b, hsmooth, hcompact, hsupport.trans (hβsupport.trans Set.inter_subset_left), hsmall, hgerm,
      hgerm.eq_of_nhds.trans hLzero⟩

/-- Every linear shear `(x, y) ↦ (x + L y, y)` is, near the origin, the time-one map of a compactly
supported isotopy which preserves the second coordinate and fixes the subspace `y = 0`.
-/
theorem SupportedDiffeomorph.exists_supported_shear_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (hzero : (0 : E × F) ∈ U) :
    ∃ (A : ℝ × (E × F) → E × F) (K : Set (E × F)),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A ∧
            (∀ p, A (0, p) = p) ∧
              (∀ t,
                  ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞,
                    ∀ p, D p = A (t, p)) ∧
                (∀ t p, p ∉ K → A (t, p) = p) ∧
                  (∀ t p, (A (t, p)).2 = p.2) ∧
                    (∀ t x, A (t, (x, (0 : F))) = (x, 0)) ∧
                      (fun p => A (1, p)) =ᶠ[𝓝 (0 : E × F)] (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, -⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : E)}) isCompact_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hρ))
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph'
  obtain ⟨ε, hε, hfamily⟩ :=
    exists_radius_normalBumpFamily (P := F) Φ hβ hβcompact
      (show tsupport β ⊆ Φ.source from Set.subset_univ _)
  obtain ⟨b, hb, hbcompact, hbsupport, hbsmall, hbeq, hbzero⟩ :=
    exists_small_supported_germ Metric.isOpen_ball (Metric.mem_ball_self hρ)
      (show ContDiffOn ℝ ∞ (fun y : F => -(L y)) (Metric.ball 0 ρ) from L.contDiff.neg.contDiffOn)
      (show -(L (0 : F)) = 0 by simp) hε
  obtain ⟨hAprod, hdiffprod, hK⟩ := hfamily b hb hbcompact hbsmall
  let A := normalBumpFamily Φ β b
  let K : Set (E × F) := (Φ '' tsupport β) ×ˢ tsupport b
  let V := PartialChart.vectorProduct E F
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A :=
    V.symm.contMDiff.comp (hAprod.comp (contMDiff_fst.prodMk (V.contMDiff.comp contMDiff_snd)))
  have hdiff (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞, ∀ p, D p = A (t, p) := by
    obtain ⟨D, hD⟩ := hdiffprod t
    exact ⟨(V.trans D).trans V.symm, hD⟩
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨⟨w, hw, rfl⟩, hy⟩
    apply hρU
    change (w, y) ∈ Metric.ball (0 : E × F) ρ
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨mem_ball_zero_iff.mp (hβsupport hw), mem_ball_zero_iff.mp (hbsupport hy)⟩
  have hplateau : ∀ᶠ x in 𝓝 (0 : E), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : E)))
  have hfirst : ∀ᶠ p in 𝓝 (0 : E × F), β p.1 = 1 := (continuous_fst.tendsto (0 : E × F)) hplateau
  have hsecond : ∀ᶠ p in 𝓝 (0 : E × F), b p.2 = -(L p.2) :=
    (continuous_snd.tendsto (0 : E × F)) hbeq
  refine
    ⟨A, K, hK, hKU, hA, normalBumpFamily_zero Φ β b, hdiff, normalBumpFamily_fixed_outside Φ β b,
      normalBumpFamily_normal Φ β b, fun t x => normalBumpFamily_fixed_fiber Φ β b hbzero t x, ?_⟩
  filter_upwards [hfirst, hsecond] with p hp₁ hp₂
  have hh := normalBumpFamily_chart Φ β b (show p.1 ∈ Φ.source from Set.mem_univ _) p.2
  change A (1, p) = (p.1 - β p.1 • b p.2, p.2) at hh
  rwa [hp₁, one_smul, hp₂, sub_neg_eq_add] at hh


/-- Isotopy extension through a chart: a compactly supported isotopy on the source of a partial
diffeomorphism extends to a compactly supported isotopy of the target intertwined with it by the
chart.
-/
theorem SupportedDiffeomorph.exists_supported_isotopy_extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    (hA₀ : ∀ x, A (0, x) = x) (hdiff : ∀ t, ∃ D : Diffeomorph I I X X ∞, ∀ x, D x = A (t, x))
    {K : Set X} (hK : IsCompact K) (hKsource : K ⊆ Φ.source)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) :
    ∃ (B : ℝ × Y → Y) (L : Set Y),
      IsCompact L ∧
        L ⊆ Φ.target ∧
          ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B ∧
            (∀ y, B (0, y) = y) ∧
              (∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, D y = B (t, y)) ∧
                (∀ t y, y ∉ L → B (t, y) = y) ∧
                  (∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source) ∧
                    ∀ t x, x ∈ Φ.source → B (t, Φ x) = Φ (A (t, x)) := by
  have hsource : ∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    have heq : (fun x => A (t, x)) = D := funext (fun x => (hD x).symm)
    rw [heq]
    exact mapsTo_source Φ D.toEquiv hKsource hDfix
  let B : ℝ × Y → Y := fun q => extendMap Φ (fun x => A (q.1, x)) q.2
  refine
    ⟨B, Φ '' K, hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKsource), ?_,
      contMDiff_extendFamily Φ hA hK hKsource hfix hsource, ?_, ?_, ?_, hsource, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hKsource hx)
  · intro y
    have heq : (fun x => A (0, x)) = id := funext hA₀
    change extendMap Φ (fun x => A (0, x)) y = y
    rw [heq]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    refine ⟨extension Φ D hK hKsource hDfix, ?_⟩
    intro y
    exact congrArg (fun f : X → X => extendMap Φ f y) (funext hD)
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro t x hx
    exact extendMap_chart Φ (fun z => A (t, z)) hx


/-- The inverse of a diffeomorphism isotopic to the identity is isotopic to the identity. -/
theorem SupportedDiffeomorph.IsotopicToIdentity.symm {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : SupportedDiffeomorph.IsotopicToIdentity e) :
    SupportedDiffeomorph.IsotopicToIdentity e.symm := by
  obtain ⟨A, hA, hA₀, hA₁, hdiff⟩ := he
  let B : ℝ × M → M := fun p => e.symm (A (1 - p.1, p.2))
  have hrev : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t) :=
    (contDiff_const.sub contDiff_id).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B :=
    e.symm.contMDiff.comp (hA.comp ((hrev.comp contMDiff_fst).prodMk contMDiff_snd))
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro x
    change e.symm (A (1 - 0, x)) = x
    rw [sub_zero, hA₁, e.symm_apply_apply]
  · intro x
    change e.symm (A (1 - 1, x)) = e.symm x
    rw [sub_self, hA₀]
  · intro t
    obtain ⟨d, hd⟩ := hdiff (1 - t)
    refine ⟨d.trans e.symm, ?_⟩
    intro x
    change e.symm (A (1 - t, x)) = e.symm (d x)
    rw [hd]
