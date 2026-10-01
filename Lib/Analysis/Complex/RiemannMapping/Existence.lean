/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.Steps

/-!
# The Riemann mapping theorem

Every simply connected open set `U ⊊ ℂ` admits, for each `x₀ ∈ U`, a bijective holomorphic map
`f : U → 𝔻` onto the unit disc with nonvanishing derivative and `f x₀ = 0`
(`RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`).

The proof is the textbook one (Ahlfors, *Complex Analysis*, Ch. 6 §1.1; Rudin, *Real and Complex
Analysis*, Thm 14.8): bounded holomorphic families are equicontinuous, hence (Arzelà–Ascoli) the
class of normalized injective maps `U → 𝔻` has compact closure in the topology of uniform
convergence on compact subsets; by Hurwitz its closure consists of injective or constant maps, so
`‖f' x₀‖` attains its maximum on the class; a non-surjective member is improved by the Koebe
square-root step (`Complex.exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt`, in
`RiemannMapping/Steps.lean`), so the maximizer is onto. Mathlib provides only the Koebe step.

The file also packages the theorem as a chosen map `RiemannMapping.riemannMap` with its
specification, and proves that a holomorphic map with nonvanishing derivative is a local
analytic diffeomorphism (`RiemannMapping.isLocalDiffeomorphAt_of_deriv_ne_zero`).
-/

open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff Interval NNReal UniformConvergence Uniformity

noncomputable section

/-- A bounded holomorphic family is uniformly equicontinuous on a thickening. -/
theorem RiemannMapping.uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : ι → E → F} {s U : Set E} {r : ℝ} (hr₀ : 0 < r)
    (hU : Metric.thickening r s ⊆ U) (hfd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) : UniformEquicontinuousOn f s := by
  have hsU : s ⊆ U := (Metric.self_subset_thickening hr₀ _).trans hU
  rw [(Metric.uniformity_basis_dist.inf_principal _).uniformEquicontinuousOn_iff
      Metric.uniformity_basis_dist_le]
  intro ε hε
  rcases hf with ⟨C, hC⟩
  rcases exists_pos_mul_lt hε (2 * C / r) with ⟨δ, hδ₀, hδ⟩
  use Min.min δ r, by positivity
  simp only [Set.mem_ofPred, Set.mem_inter_iff, Set.prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [Metric.thickening_eq_biUnion_ball, Set.iUnion₂_subset_iff] at hU
  calc
    Dist.dist (f i x) (f i y) ≤ (2 * C / r) * Dist.dist x y := by
      apply Complex.dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hfd i).mono (hU _ hy)
      · intro z hz
        rw [Metric.mem_closedBall, two_mul]
        exact
          dist_le_norm_add_norm _ _ |>.trans <|
            add_le_add (hC _ _ <| hU y hy hz) (hC _ _ <| hsU hy)
      · exact hdist.2
    _ ≤ _ := by
      grw [hdist.1]
      · exact hδ.le
      · have := (norm_nonneg _).trans (hC i x (hsU hx))
        positivity

/-- A bounded holomorphic family is equicontinuous at a point. -/
theorem RiemannMapping.equicontinuousAt_of_forall_norm_le {ι E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ι → E → F} {U : Set E} {x : E}
    (hU : U ∈ 𝓝 x) (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    EquicontinuousAt f x := by
  rcases Metric.nhds_basis_ball.mem_iff.mp hU with ⟨r, hr₀, hr⟩
  have : Metric.thickening (r / 2) (Metric.ball x (r / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have :=
    uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le (by positivity) this hfd
        hf |>.equicontinuousOn
      x (by simpa)
  rwa [EquicontinuousWithinAt,
    nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ (by positivity))] at this

/-- An exhaustion of the domain by compact subsets. -/
def RiemannMapping.compactSubsets (U : Set ℂ) : Set (Set ℂ) :=
  {K | K ⊆ U ∧ IsCompact K}

/-- The function space of holomorphic maps to the disc. -/
abbrev RiemannMapping.FunctionSpace (U : Set ℂ) :=
  ℂ →ᵤ[compactSubsets U] ℂ

/-- Evaluation at a point of the domain. -/
def RiemannMapping.evaluation {U : Set ℂ} (f : FunctionSpace U) : ℂ → ℂ :=
  UniformOnFun.toFun (compactSubsets U) f

/-- The function-space uniformity is countably generated. -/
theorem RiemannMapping.uniformity_isCountablyGenerated {U : Set ℂ} (hUo : IsOpen U) :
    (𝓤 (FunctionSpace U)).IsCountablyGenerated := by
  have := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  let φ : CompactExhaustion U := Inhabited.default
  apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => (↑) '' φ n)
  · intro n
    exact ⟨Set.image_val_subset, (φ.isCompact n).image continuous_subtype_val⟩
  · exact Set.monotone_image.comp φ.subset
  · rintro K ⟨hKU, hKc⟩
    lift K to Set U using hKU
    rw [← Subtype.isCompact_iff] at hKc
    exact (φ.exists_superset_of_isCompact hKc).imp fun n hn => by gcongr

/-- Locally uniform convergence implies pointwise evaluation convergence. -/
theorem RiemannMapping.evaluation_tendstoLocallyUniformlyOn {U : Set ℂ} (hUo : IsOpen U)
    {f : FunctionSpace U} {s : Set (FunctionSpace U)} :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[s] f) U := by
  have h : Filter.Tendsto id (𝓝[s] f) (𝓝 f) := Filter.tendsto_id'.mpr nhdsWithin_le_nhds
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp h) K ⟨hKU, hK⟩

/-- A bounded holomorphic family has compact closure. -/
theorem RiemannMapping.isCompact_closure_of_bounded_holomorphic {U : Set ℂ} (hUo : IsOpen U)
    {s : Set (FunctionSpace U)} (hsd : ∀ f ∈ s, DifferentiableOn ℂ (evaluation f) U)
    (hsb : ∃ C : ℝ, ∀ f ∈ s, ∀ z ∈ U, ‖evaluation f z‖ ≤ C) : IsCompact (closure s) := by
  obtain ⟨C, hC⟩ := hsb
  apply
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (𝔖 := compactSubsets U) (fun K hK => hK.2)
      (F := evaluation) .id
  · rintro K ⟨hKU, _⟩ z hz
    exact
      (equicontinuousAt_of_forall_norm_le (hUo.mem_nhds (hKU hz))
            (fun f : s => hsd f.val f.property)
            ⟨C, fun f z hz => hC f.val f.property z hz⟩).equicontinuousWithinAt
        K
  · intro K hK x hx
    exact
      ⟨Metric.closedBall 0 C, ProperSpace.isCompact_closedBall _ _, fun f hf => by
        simpa only [mem_closedBall_zero_iff] using hC f hf x (hK.1 hx)⟩

/-- The normalized class of injective disc maps with prescribed derivative data. -/
def RiemannMapping.normalizedClass (U : Set ℂ) (x₀ : ℂ) : Set (FunctionSpace U) :=
  {f |
    Set.MapsTo (evaluation f) U (Metric.ball 0 1) ∧
      Set.InjOn (evaluation f) U ∧
        DifferentiableOn ℂ (evaluation f) U ∧
          (∀ z ∈ U, deriv (evaluation f) z ≠ 0) ∧ evaluation f x₀ = 0}

/-- The normalized class has compact closure. -/
theorem RiemannMapping.normalizedClass_compact_closure {U : Set ℂ} (hUo : IsOpen U) (x₀ : ℂ) :
    IsCompact (closure (normalizedClass U x₀)) := by
  apply isCompact_closure_of_bounded_holomorphic hUo (fun f hf => hf.2.2.1)
  exact ⟨1, fun f hf z hz => (mem_ball_zero_iff.mp (hf.1 hz)).le⟩

/-- The closure of the normalized class. -/
theorem RiemannMapping.closure_normalizedClass {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    closure (normalizedClass U x₀) ⊆
      {f |
        Set.MapsTo (evaluation f) U (Metric.ball 0 1) ∧
          ((∃ C, Set.EqOn (evaluation f) (Function.const ℂ C) U) ∨ Set.InjOn (evaluation f) U) ∧
            DifferentiableOn ℂ (evaluation f) U ∧
              evaluation f x₀ = 0 ∧
                (Set.EqOn (deriv (evaluation f)) 0 U ∨ ∀ z ∈ U, deriv (evaluation f) z ≠ 0)} := by
  let := uniformity_isCountablyGenerated hUo
  intro f hf
  let : (𝓝[normalizedClass U x₀] f).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hf
  have htendsto :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[normalizedClass U x₀] f) U :=
    evaluation_tendstoLocallyUniformlyOn hUo
  have hFd : ∀ᶠ g in 𝓝[normalizedClass U x₀] f, DifferentiableOn ℂ (evaluation g) U :=
    eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1
  have hdf : DifferentiableOn ℂ (evaluation f) U := htendsto.differentiableOn hFd hUo
  have hf_le : ∀ z ∈ U, ‖evaluation f z‖ ≤ 1 := by
    intro z hz
    refine le_of_tendsto (htendsto.tendsto_at hz).norm (eventually_mem_nhdsWithin.mono ?_)
    intro g hg
    exact (mem_ball_zero_iff.mp (hg.1 hz)).le
  have hfx₀ : evaluation f x₀ = 0 := by
    refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
    refine tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun g hg => ?_)
    exact hg.2.2.2.2.symm
  refine ⟨?_, ?_, hdf, hfx₀, ?_⟩
  · by_contra hf_ball
    obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖evaluation f z‖ := by simpa [Set.MapsTo] using hf_ball
    have hm : IsMaxOn (fun z => ‖evaluation f z‖) U z := by
      intro y hy
      exact (hf_le y hy).trans hz
    have he : evaluation f x₀ = evaluation f z :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdf hzU hm hx₀
    norm_num [← he, hfx₀] at hz
  · exact
      Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo hUc
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.1) hFd htendsto
  · apply
      Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn hUo hUc
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.2.1)
        (hFd.mono fun g hg => hg.deriv hUo)
    exact htendsto.deriv hFd hUo

/-- The derivative norm is continuous on the closure. -/
theorem RiemannMapping.norm_deriv_continuousOn_closure {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ContinuousOn (fun f : FunctionSpace U => ‖deriv (evaluation f) x₀‖)
      (closure (normalizedClass U x₀)) := by
  have hc := closure_normalizedClass hUo hUc hx₀
  refine ContinuousOn.mono (ContinuousOn.norm fun f hf => ?_) hc
  refine
    TendstoLocallyUniformlyOn.tendsto_at
      (TendstoLocallyUniformlyOn.deriv (evaluation_tendstoLocallyUniformlyOn hUo) ?_ hUo) hx₀
  exact eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1

/-- Existence of a maximal normalized map: the extremal map maximizing the derivative at the base point, the heart of the Riemann mapping theorem (Ahlfors, Complex Analysis, Ch. 6; Rudin, Real and Complex Analysis, Theorem 14.8). -/
theorem RiemannMapping.exists_maximal_normalizedMap {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hne : (normalizedClass U x₀).Nonempty) :
    ∃ f : FunctionSpace U,
      f ∈ normalizedClass U x₀ ∧
        ∀ g ∈ normalizedClass U x₀, ‖deriv (evaluation g) x₀‖ ≤ ‖deriv (evaluation f) x₀‖ := by
  obtain ⟨f, hf, hmax⟩ :=
    (normalizedClass_compact_closure hUo x₀).exists_isMaxOn hne.closure
      (norm_deriv_continuousOn_closure hUo hUc hx₀)
  have hpos : 0 < ‖deriv (evaluation f) x₀‖ := by
    obtain ⟨g, hg⟩ := hne
    exact (norm_pos_iff.mpr (hg.2.2.2.1 x₀ hx₀)).trans_le (hmax (subset_closure hg))
  obtain ⟨hmap, hinj, hdiff, hzero, hderiv⟩ := closure_normalizedClass hUo hUc hx₀ hf
  have hinj' : Set.InjOn (evaluation f) U := by
    apply hinj.resolve_left
    rintro ⟨C, hC⟩
    rw [(hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq] at hpos
    change 0 < ‖deriv (fun _ : ℂ => C) x₀‖ at hpos
    simp only [deriv_const, norm_zero, lt_self_iff_false] at hpos
  have hderiv' : ∀ z ∈ U, deriv (evaluation f) z ≠ 0 := by
    apply hderiv.resolve_left
    intro hzero'
    have hz : deriv (evaluation f) x₀ = 0 := hzero' hx₀
    simp only [hz, norm_zero, lt_self_iff_false] at hpos
  exact ⟨f, ⟨hmap, hinj', hdiff, hderiv', hzero⟩, fun g hg => hmax (subset_closure hg)⟩

/-- The disc extension of a limit map. -/
def RiemannMapping.discExtension {U : Set ℂ} (f : ℂ → ℂ) (hf : Set.MapsTo f U (Metric.ball 0 1)) :
    ℂ → Complex.UnitDisc := by
  classical
    exact fun z =>
    if hz : z ∈ U then Complex.UnitDisc.mk (f z) (mem_ball_zero_iff.mp (hf hz)) else 0

/-- The disc extension computes the map. -/
@[simp]
theorem RiemannMapping.discExtension_coe {U : Set ℂ} (f : ℂ → ℂ)
    (hf : Set.MapsTo f U (Metric.ball 0 1)) {z : ℂ} (hz : z ∈ U) :
    (discExtension f hf z : ℂ) = f z := by
  simp only [discExtension, dif_pos hz, Complex.UnitDisc.coe_mk]

/-- The disc extension agrees with the map on the domain. -/
theorem RiemannMapping.discExtension_eqOn {U : Set ℂ} (f : ℂ → ℂ)
    (hf : Set.MapsTo f U (Metric.ball 0 1)) :
    Set.EqOn (Complex.UnitDisc.coe ∘ discExtension f hf) f U := fun _ hz =>
  discExtension_coe f hf hz

/-- The normalized class is nonempty. -/
theorem RiemannMapping.normalizedClass_nonempty {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    (normalizedClass U x₀).Nonempty := by
  obtain ⟨f, hf₀, hf_inj, hfd⟩ := Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU hx₀
  refine ⟨UniformOnFun.ofFun (compactSubsets U) (Complex.UnitDisc.coe ∘ f), ?_⟩
  refine ⟨fun z _ => (f z).property, ?_, ?_, hfd, ?_⟩
  · intro z hz w hw he
    exact hf_inj hz hw (Complex.UnitDisc.coe_injective he)
  · intro z hz
    exact (differentiableAt_of_deriv_ne_zero (hfd z hz)).differentiableWithinAt
  · change (f x₀ : ℂ) = 0
    rw [hf₀]
    rfl

/-- THE HEADLINE — the Riemann mapping theorem in normalized form: a simply connected proper domain admits a bijective holomorphic map onto the unit disc with nonvanishing derivative sending the base point to 0 (Rudin, Real and Complex Analysis, Theorem 14.8; Ahlfors, Complex Analysis, Ch. 6). -/
theorem RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧
        Set.BijOn f U (Metric.ball 0 1) ∧ (∀ z ∈ U, deriv f z ≠ 0) ∧ f x₀ = 0 := by
  obtain ⟨f, hf, hmax⟩ :=
    exists_maximal_normalizedMap hUo hUc.isPathConnected.isConnected.isPreconnected hx₀
      (normalizedClass_nonempty hUo hUc hU hx₀)
  obtain ⟨hfmap, hfinj, hfdiff, hfderiv, hfzero⟩ := hf
  refine ⟨evaluation f, hfdiff, ⟨hfmap, hfinj, ?_⟩, hfderiv, hfzero⟩
  by_contra hsurj
  let fDisc := discExtension (evaluation f) hfmap
  have hfeq : Set.EqOn (Complex.UnitDisc.coe ∘ fDisc) (evaluation f) U :=
    discExtension_eqOn (evaluation f) hfmap
  have hfdDisc : DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ fDisc) U :=
    (differentiableOn_congr hfeq).mpr hfdiff
  have hfDisc0 : fDisc x₀ = 0 := by
    apply Complex.UnitDisc.coe_injective
    change (fDisc x₀ : ℂ) = 0
    exact (hfeq hx₀).trans hfzero
  have hfDiscInj : Set.InjOn fDisc U := by
    intro z hz w hw he
    apply hfinj hz hw
    exact (hfeq hz).symm.trans ((congrArg Complex.UnitDisc.coe he).trans (hfeq hw))
  have hfDiscDeriv : ∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ fDisc) z ≠ 0 := by
    intro z hz
    rw [(hfeq.eventuallyEq_of_mem (hUo.mem_nhds hz)).deriv_eq]
    exact hfderiv z hz
  have hfDiscSurj : ¬Set.SurjOn fDisc U Set.univ := by
    intro hs
    apply hsurj
    intro w hw
    obtain ⟨z, hz, he⟩ := hs (Set.mem_univ (Complex.UnitDisc.mk w (mem_ball_zero_iff.mp hw)))
    refine ⟨z, hz, ?_⟩
    exact (hfeq hz).symm.trans (congrArg Complex.UnitDisc.coe he)
  obtain ⟨g, hg₀, hginj, hgdiff, hgderiv, hglt⟩ :=
    Complex.exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt hUo hUc hU hx₀ hfdDisc hfDisc0
      hfDiscInj hfDiscSurj hfDiscDeriv
  let gFun : FunctionSpace U := UniformOnFun.ofFun (compactSubsets U) (Complex.UnitDisc.coe ∘ g)
  have hgmem : gFun ∈ normalizedClass U x₀ := by
    refine ⟨fun z _ => (g z).property, ?_, hgdiff, hgderiv, ?_⟩
    · intro z hz w hw he
      exact hginj hz hw (Complex.UnitDisc.coe_injective he)
    · change (g x₀ : ℂ) = 0
      rw [hg₀]
      rfl
  have hle := hmax gFun hgmem
  have heDeriv : deriv (Complex.UnitDisc.coe ∘ fDisc) x₀ = deriv (evaluation f) x₀ :=
    (hfeq.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq
  rw [heDeriv] at hglt
  exact hle.not_gt hglt

/-- A holomorphic map with nonvanishing derivative is a local diffeomorphism. -/
theorem RiemannMapping.isLocalDiffeomorphAt_of_deriv_ne_zero (U : TopologicalSpace.Opens ℂ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hderiv : ∀ z ∈ U, deriv f z ≠ 0) {z : ℂ}
    (hz : z ∈ U) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f z := by
  have hfω : ContDiffOn ℂ ω f (U : Set ℂ) := hf.contDiffOn U.isOpen
  have hF (w : ℂ) (hw : w ∈ U) : ContDiffAt ℂ ω f w := hfω.contDiffAt (U.isOpen.mem_nhds hw)
  have hD (w : ℂ) (hw : w ∈ U) : HasDerivAt f (deriv f w) w :=
    hf.hasDerivAt (U.isOpen.mem_nhds hw)
  let e : OpenPartialHomeomorph ℂ ℂ :=
    ((hF z hz).toOpenPartialHomeomorph f ((hD z hz).hasFDerivAt_equiv (hderiv z hz))
          (by simp)).restr
      (U : Set ℂ)
  have heU : e.source ⊆ (U : Set ℂ) := by
    intro w hw
    dsimp only [e] at hw
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen] at hw
    exact hw.2
  have hze : z ∈ e.source := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen]
    exact
      ⟨(hF z hz).mem_toOpenPartialHomeomorph_source ((hD z hz).hasFDerivAt_equiv (hderiv z hz))
          (by simp),
        hz⟩
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := ?_
        contMDiffOn_invFun := ?_ }, hze, fun _ _ => rfl⟩
  · change ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f e.source
    exact (hfω.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro w hw
    have hwU := heU (e.map_target hw)
    exact
      (e.contDiffAt_symm hw ((hD _ hwU).hasFDerivAt_equiv (hderiv _ hwU))
          (hF _ hwU)).contDiffWithinAt

/-- The unit disc as a subtype. -/
def RiemannMapping.unitDisc : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The Riemann map of the domain onto the disc. -/
def RiemannMapping.riemannMap (U : TopologicalSpace.Opens ℂ) (hUc : IsSimplyConnected (U : Set ℂ))
    (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) : ℂ → ℂ :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose

/-- The Riemann map is the maximizing normalized map. -/
theorem RiemannMapping.riemannMap_spec (U : TopologicalSpace.Opens ℂ)
    (hUc : IsSimplyConnected (U : Set ℂ)) (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) :
    DifferentiableOn ℂ (riemannMap U hUc hU x₀) (U : Set ℂ) ∧
      Set.BijOn (riemannMap U hUc hU x₀) (U : Set ℂ) (unitDisc : Set ℂ) ∧
        (∀ z ∈ U, deriv (riemannMap U hUc hU x₀) z ≠ 0) ∧ riemannMap U hUc hU x₀ x₀ = 0 :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose_spec
