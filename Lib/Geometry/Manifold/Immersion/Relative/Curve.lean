/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Immersion.Relative.Embedding

/-!
# Relative immersion and embedding theorems for curves

The one-dimensional case of the immersion chain. `WeightedPerturbation.perturb f β a = f + β • a`
perturbs a map `f : E → F` by a cutoff-weighted constant; the parameters `a` creating a kernel
vector of the perturbed derivative at points of a manifold `X` mapped into `E` form the image of
`WeightedPerturbation.badDomain` under the smooth `WeightedPerturbation.badParameter`, so when
`dim X + dim E < dim F` small parameters give a derivative whose kernel is the common kernel of
`fderiv f` and `fderiv β` (`WeightedPerturbation.exists_small_parameter_with_common_kernel`). For a
curve `f : ℝ → F` with `dim F ≥ 3` this gives `CurveImmersion.exists_small_affine_immersion`: small
perturbations `t ↦ f t + t • a` are immersions everywhere. The weight `CurveImmersion.weight β t = t * β t`
turns a cutoff into a curve perturbation with the same support.

The patch step `ManifoldImmersion.exists_curve_immersion_patch_with_property_within_target` and
its iteration give the relative immersion theorem for curves
(`ManifoldImmersion.exists_curve_immersion_on_compact_rel_within_target`, `dim N ≥ 3`), the relative
embedding theorem `ManifoldImmersion.exists_relative_compact_curve_embedding` (a curve which is an
injective immersion on `K ∩ C` is homotopic rel `C` to a closed embedding and immersion on the
compact set `K`), and the versions avoiding a closed image or a finite set
(`ManifoldImmersion.exists_relative_curve_avoidance_of_clean_neighborhood`,
`ManifoldImmersion.exists_relative_curve_avoiding_finite`).

## References

* Hirsch, *Differential Topology*, Ch. 2 §2, in dimension one.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- Perturbation of a map by adding the cutoff-weighted constant `β x • a`. -/
def WeightedPerturbation.perturb {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (β : E → ℝ) (a : F) (x : E) : F :=
  f x + β x • a

/-- The weighted perturbation is smooth. -/
theorem WeightedPerturbation.contDiff_perturb {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) : ContDiff ℝ ∞ (perturb f β a) :=
  hf.add (hβ.smul contDiff_const)

/-- The derivative of the weighted perturbation is `fderiv f x + (fderiv β x).smulRight a`. -/
theorem WeightedPerturbation.fderiv_perturb {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) (x : E) :
    fderiv ℝ (perturb f β a) x = fderiv ℝ f x + (fderiv ℝ β x).smulRight a :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add
      ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv

/-- The points and directions at which the cutoff has nonzero derivative, where the perturbation can
change the kernel. -/
def WeightedPerturbation.badDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} (b : X → E) (β : E → ℝ) : Set (X × E) :=
  {q | fderiv ℝ β (b q.1) q.2 ≠ 0}

/-- The parameter that would create a new kernel vector at a given point and direction. -/
def WeightedPerturbation.badParameter {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} (b : X → E) (f : E → F) (β : E → ℝ)
    (q : X × E) : F :=
  (fderiv ℝ β (b q.1) q.2)⁻¹ • (-(fderiv ℝ f (b q.1) q.2))

/-- The scalar derivative `(x, v) ↦ fderiv β (b x) v` is smooth. -/
theorem WeightedPerturbation.contMDiff_scalarDerivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
    {b : X → E} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (fun q : X × E => fderiv ℝ β (b q.1) q.2) :=
  ((hβ.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd

/-- The bad domain is open. -/
theorem WeightedPerturbation.isOpen_badDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
    {b : X → E} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    IsOpen (badDomain b β) :=
  isOpen_ne_fun (contMDiff_scalarDerivative hb hβ).continuous continuous_const

/-- The bad parameter is smooth on the bad domain. -/
theorem WeightedPerturbation.contMDiffOn_badParameter {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {B H X : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace X] [ChartedSpace H X] {b : X → E} {f : E → F} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (badParameter b f β) (badDomain b β) := by
  have hdf : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun q : X × E => fderiv ℝ f (b q.1) q.2) :=
    ((hf.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd
  intro q hq
  exact
    (((contMDiff_scalarDerivative hb hβ).contMDiffAt.inv₀ hq).smul
        hdf.contMDiffAt.neg).contMDiffWithinAt

/-- For a parameter outside the image of the bad-parameter map, the kernel of the perturbed
derivative is the intersection of the kernels of `fderiv f` and `fderiv β`. -/
theorem WeightedPerturbation.kernel_iff_of_not_bad {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} {b : X → E} {f : E → F}
    {β : E → ℝ} (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) {a : F}
    (hgood : a ∉ badParameter b f β '' badDomain b β) (x : X) (v : E) :
    fderiv ℝ (perturb f β a) (b x) v = 0 ↔ fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  rw [fderiv_perturb hf hβ]
  change fderiv ℝ f (b x) v + fderiv ℝ β (b x) v • a = 0 ↔ _
  constructor
  · intro hker
    have hbzero : fderiv ℝ β (b x) v = 0 := by
      by_contra hn
      apply hgood
      refine ⟨(x, v), hn, ?_⟩
      have heq : fderiv ℝ β (b x) v • a = -(fderiv ℝ f (b x) v) :=
        eq_neg_of_add_eq_zero_right hker
      change (fderiv ℝ β (b x) v)⁻¹ • (-(fderiv ℝ f (b x) v)) = a
      rw [← heq, inv_smul_smul₀ hn]
    exact ⟨by simpa only [hbzero, zero_smul, add_zero] using hker, hbzero⟩
  · rintro ⟨hfzero, hbzero⟩
    simp only [hfzero, hbzero, zero_smul, add_zero]

/-- When `dim X + dim E < dim F`, arbitrarily small parameters give a smooth perturbation whose
derivative has exactly the common kernel of `f` and the cutoff. -/
theorem WeightedPerturbation.exists_small_parameter_with_common_kernel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ B]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    {b : X → E} {f : E → F} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        ContDiff ℝ ∞ (perturb f β a) ∧
          ∀ x v,
            fderiv ℝ (perturb f β a) (b x) v = 0 ↔
              fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  have hd : Module.finrank ℝ (B × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense :=
    GeneralPosition.dense_compl_manifold_image (isOpen_badDomain hb hβ)
      (contMDiffOn_badParameter hb hf hβ) hd
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 hε
  exact
    ⟨a, by simpa only [dist_zero_left] using hnorm, contDiff_perturb hf hβ a,
      kernel_iff_of_not_bad hf hβ hgood⟩

/-- Perturbation of a curve by the linear term `t • a`. -/
def CurveImmersion.perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (a : F) : ℝ → F :=
  WeightedPerturbation.perturb f id a

/-- When `dim F ≥ 3`, arbitrarily small linear perturbations of a smooth curve are immersions
everywhere. -/
theorem CurveImmersion.exists_small_affine_immersion {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧ ContDiff ℝ ∞ (perturb f a) ∧ ∀ t, Function.Injective (fderiv ℝ (perturb f a) t) :=
  by
  have hd : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ F := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨a, ha, hs, hker⟩ :=
    WeightedPerturbation.exists_small_parameter_with_common_kernel (I := 𝓘(ℝ, ℝ)) (b := id)
      (β := id) contMDiff_id hf contDiff_id hd hε
  refine ⟨a, ha, hs, ?_⟩
  intro t u v huv
  have hz : fderiv ℝ (perturb f a) t (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero := ((hker t (u - v)).mp hz).2
  have huv0 : u - v = 0 := by simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hzero
  exact sub_eq_zero.mp huv0

/-- The weight `t ↦ t * β t` used to turn a cutoff into a curve perturbation with the same
support. -/
def CurveImmersion.weight (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  β t * t

/-- The weight of a smooth cutoff is smooth. -/
theorem CurveImmersion.contDiff_weight {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (weight β) :=
  hβ.mul contDiff_id

/-- The weight of a compactly supported cutoff has compact support. -/
theorem CurveImmersion.hasCompactSupport_weight {β : ℝ → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (weight β) :=
  hβ.mul_right (f' := id)

/-- The support of the weight is contained in the support of the cutoff. -/
theorem CurveImmersion.tsupport_weight_subset (β : ℝ → ℝ) :
    tsupport (weight β) ⊆ tsupport β :=
  tsupport_mul_subset_left (f := β) (g := id)

/-- Where the cutoff vanishes the weight vanishes. -/
theorem CurveImmersion.weight_eq_zero {β : ℝ → ℝ} {t : ℝ} (ht : β t = 0) : weight β t = 0 :=
  by simp only [weight, ht, MulZeroClass.zero_mul]

/-- Patch step of the curve immersion theorem: if a property `Q` holds for all small parameters,
some cutoff-supported perturbation of the curve satisfies `Q`, is homotopic to `f` rel the zero
set of the cutoff within the open target, and is an immersion on the plateau. -/
theorem ManifoldImmersion.exists_curve_immersion_patch_with_property_within_target
    {G F H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) {β χ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    (hχone : ∀ t ∈ tsupport β, χ t = 1) (hdim : 3 ≤ Module.finrank ℝ F) (Q : (ℝ → N) → Prop)
    (hQ :
      ∀ᶠ a : F in 𝓝 0,
        Q (ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a))
    {D : Set ℝ} {O : Set N} (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Q g ∧
          HomotopicRelWithin f g {t | β t = 0} D O ∧
            ∀ t ∈ interior {t | β t = 1}, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro t ht
    exact hχsupport (subset_tsupport χ (by change χ t ≠ 0; rw [hχone t ht]; norm_num))
  have hw := CurveImmersion.contDiff_weight hβ
  have hwsupport : tsupport (CurveImmersion.weight β) ⊆ f ⁻¹' c.source :=
    (CurveImmersion.tsupport_weight_subset β).trans hsupport
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ k := fun t =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid c hf hw.contMDiff
      (CurveImmersion.hasCompactSupport_weight hcompact) hwsupport
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQ
  obtain ⟨a, ha, -, hderiv⟩ :=
    CurveImmersion.exists_small_affine_immersion hk hdim (lt_min hε hδ)
  have haε : ‖a‖ < ε := ha.trans_le (min_le_left _ _)
  have hv := hvalid a haε
  have hsmooth := ChartMapPerturbation.contMDiff_perturb c hf hw.contMDiff hwsupport hv
  let g : C(ℝ, N) :=
    ⟨ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a, hsmooth.continuous⟩
  have hcoord (t : ℝ) (ht : β t = 1) : c (g t) = CurveImmersion.perturb k a t := by
    have hts : t ∈ tsupport β := subset_tsupport β (by change β t ≠ 0; rw [ht]; norm_num)
    change c (ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a t) = _
    rw [ChartMapPerturbation.chart_perturb c f (CurveImmersion.weight β) hv
        (hsupport hts)]
    simp only [ChartMapPerturbation.coordinateFamily, CurveImmersion.perturb,
      WeightedPerturbation.perturb, k, ChartMapPerturbation.cutoffCoordinates,
      CurveImmersion.weight, ht, hχone t hts, one_mul, one_smul, id_eq]
  have hQg : Q g :=
    hδkeep
      (show a ∈ Metric.ball 0 δ by
        simpa only [Metric.mem_ball, dist_zero_right] using ha.trans_le (min_le_right ε δ))
  refine ⟨g, hsmooth, hQg, ?_, ?_⟩
  · have hrel :=
      ChartMapPerturbation.homotopicRelWithin_of_source_subset c hf hw.contMDiff hwsupport
        hvalid haε hsource hmaps
    exact
      hrel.mono (fun _ hx => CurveImmersion.weight_eq_zero hx) (Set.Subset.refl D)
        (Set.Subset.refl O)
  · intro t ht
    have hβt : β t = 1 := interior_subset (s := {t | β t = 1}) ht
    have hfs : f t ∈ c.source :=
      hsupport (subset_tsupport β (by change β t ≠ 0; rw [hβt]; norm_num))
    have hgs : g t ∈ c.source :=
      ChartMapPerturbation.perturb_mem_source c f (CurveImmersion.weight β) hv hfs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 t] CurveImmersion.perturb k a := by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact hcoord s (interior_subset (s := {t | β t = 1}) hs)
    change Function.Injective (fderiv ℝ (c ∘ g) t)
    rw [heq.fderiv_eq]
    exact hderiv t

/-- One step of the curve immersion induction: a perturbation supported in one patch makes the curve
an immersion on `K ∪ L`. -/
theorem ManifoldImmersion.exists_curve_immersion_patch_step_within_target {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N)) (i : ι)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K L C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (hLsub : L ⊆ (p i).plateau)
    (hfixed : ∀ t ∈ C, (p i).cutoff t = 0) {D : Set ℝ} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          HomotopicRelWithin f g C D O ∧
            ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let w := CurveImmersion.weight (p i).cutoff
  have hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w :=
    (CurveImmersion.contDiff_weight (p i).smooth.contDiff).contMDiff
  have hinner := (p i).inner_compatible (hcompatible i)
  have hwsupport : tsupport w ⊆ f ⁻¹' (p i).chart.source :=
    (CurveImmersion.tsupport_weight_subset (p i).cutoff).trans hinner
  have hkeep :
    ∀ᶠ a : G in 𝓝 0,
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f w a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hw hwsupport
        (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hw
      (CurveImmersion.hasCompactSupport_weight (p i).compact) hwsupport hK hinj
  let Q : (ℝ → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧ ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)
  have hQ : ∀ᶠ a : G in 𝓝 0, Q (ChartMapPerturbation.perturb (p i).chart f w a) :=
    hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, hrel, hplateau⟩ :=
    exists_curve_immersion_patch_with_property_within_target (p i).chart f hf
      (p i).smooth.contDiff (p i).outer_smooth.contDiff (p i).compact (hcompatible i) (p i).nested
      hdim Q hQ hsource hmaps
  refine ⟨g, hg, hc, ?_, ?_⟩
  · exact hrel.mono hfixed (Set.Subset.refl D) (Set.Subset.refl O)
  · intro t ht
    rcases ht with ht | ht
    · exact hKnew t ht
    · exact hplateau t (hLsub ht)

/-- Iterating the curve patch step over a finite family of patches. -/
theorem ManifoldImmersion.exists_finite_curve_patch_immersion_within_target {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N))
    (L : ι → Set ℝ) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hfixed : ∀ i t, t ∈ C → (p i).cutoff t = 0) {D : Set ℝ} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          HomotopicRelWithin f g C D O ∧
            ∀ t ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRelWithin.refl f C hmaps, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂⟩ :=
      exists_curve_immersion_patch_step_within_target p i g₁ hg₁ hc₁ hdim hKold hinj₁ (hLsub i)
        (hfixed i) (hsource i) hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro t ht
    apply hinj₂ t
    rcases ht with ht | ht
    · exact Or.inl (Or.inl ht)
    · obtain ⟨j, hj, htj⟩ := Set.mem_iUnion₂.mp ht
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr htj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, htj⟩))

/-- Relative immersion theorem for curves: when `dim N ≥ 3`, a smooth curve that is an immersion on
a compact set `K` is homotopic rel a closed set `C` disjoint from `L`, within a prescribed open
target, to a curve that is an immersion on `K ∪ L`. -/
theorem ManifoldImmersion.exists_curve_immersion_on_compact_rel_within_target
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (hC : IsClosed C)
    (hdis : Disjoint L C) {D : Set ℝ} {O : Set N} (hO : IsOpen O) (hLO : Set.MapsTo f L O)
    (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        HomotopicRelWithin f g C D O ∧
          ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
  have hp (t : L) :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC
      (show (t : ℝ) ∉ C from fun ht => Set.disjoint_left.mp hdis t.property ht) hO
      (hLO t.property)
  choose p T hcompatible hT hn hsub hfixed hsource using hp
  have hcover : L ⊆ ⋃ t : L, interior (T t) := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨t, ht⟩)⟩
  obtain ⟨s, hs⟩ :=
    hL.elim_finite_subcover (fun t : L => interior (T t)) (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ :=
    exists_finite_curve_patch_immersion_within_target (fun i : s => p i.1) (fun i : s => T i.1)
      (fun i => hT i.1) (fun i => hsub i.1) f hf (fun i => hcompatible i.1) hdim hK hinj
      (fun i => hfixed i.1) (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro t ht
  apply hderiv t
  rcases ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨i, his, hti⟩ := Set.mem_iUnion₂.mp (hs ht)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hti⟩)

/-- Relative embedding theorem for curves within an open target: when `dim N ≥ 3`, a curve which is
an injective immersion on `K ∩ C` is homotopic rel `C` to a curve that is a closed embedding and
an immersion on the compact set `K`. -/
theorem ManifoldImmersion.exists_relative_compact_curve_embedding_within_target
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f (K \ C) O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        HomotopicRelWithin f g C (K \ C) O ∧
          Topology.IsClosedEmbedding (fun t : K => g t) ∧
            ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let U : Set ℝ := {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun t ht => hderiv t ht
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := Set.disjoint_left.mpr (fun _ ht htC => ht.2 (hCD ⟨ht.1, htC⟩))
  have hLO : Set.MapsTo f L O := fun t ht => hmaps ⟨ht.1, fun htC => ht.2 (hCD ⟨ht.1, htC⟩)⟩
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_curve_immersion_on_compact_rel_within_target f hf hdim hD hL (fun t ht => hDU ht) hC
      hdis hO hLO hmaps
  have hKinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g₁ t) := by
    intro t ht
    apply hinj₁ t
    by_cases htD : t ∈ D
    · exact Or.inl htD
    · exact Or.inr ⟨ht, fun hi => htD (interior_subset hi)⟩
  have hfixed₁ : Set.InjOn g₁ (K ∩ C) := by
    intro t ht s hs hts
    apply hfixed ht hs
    rw [hhom₁.homotopicRel.fst_eq_snd ht.2, hhom₁.homotopicRel.fst_eq_snd hs.2]
    exact hts
  have hd : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion_within_target g₁ hg₁ hd hK hKinj hC hfixed₁ hO
      hhom₁.mapsTo_right
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

/-- The same statement with an ordinary relative homotopy (Hirsch, *Differential Topology*,
Ch. 2 §2, Ch. 3 §2, in dimension one). -/
theorem ManifoldImmersion.exists_relative_compact_curve_embedding {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun t : K => g t) ∧
            ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_relative_compact_curve_embedding_within_target f hf hdim hK hC hfixed hderiv
      isOpen_univ (Set.mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

/-- Relative curve embedding with avoidance: when `dim N ≥ 3` and `1 + dim Y < dim N`, a curve clean
on `K ∩ C` outside `B` is homotopic rel `C` to an embedded immersed curve on `K` avoiding the
image of `g` outside `B`. -/
theorem ManifoldImmersion.exists_relative_curve_avoidance_of_clean_neighborhood
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] {F H' Y : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [LindelofSpace (ℝ × Y)] (f : C(ℝ, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hdim : 3 ≤ Module.finrank ℝ G)
    (hobstacle : 1 + Module.finrank ℝ F < Module.finrank ℝ G) {K C B : Set ℝ} (hK : IsCompact K)
    (hC : IsClosed C) (hBC : B ⊆ interior C) (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ Set.range g) :
    ∃ f' : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun t : K => f' t) ∧
            (∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧
              ∀ t ∈ K \ B, f' t ∉ Set.range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_curve_embedding f hf hdim hK hC hfixed hderiv
  have hinj₁ : Set.InjOn f₁ K := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hclean₁ : ∀ t ∈ K ∩ C, t ∉ B → f₁ t ∉ Set.range g := by
    intro t ht htB
    rw [← hhom₁.fst_eq_snd ht.2]
    exact hclean t ht htB
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ F < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobstacle
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid⟩ :=
    exists_embedded_avoidance_relative_neighborhood f₁ g hf₁ hg hself hobs hK hC hBC hinj₁ hderiv₁
      hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid⟩

/-- Version of the previous statement with a finite obstacle set. -/
theorem ManifoldImmersion.exists_relative_curve_avoiding_finite {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) {K C B : Set ℝ} (hK : IsCompact K)
    (hC : IsClosed C) (hBC : B ⊆ interior C) (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ S) :
    ∃ f' : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun t : K => f' t) ∧
            (∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧ ∀ t ∈ K \ B, f' t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : Set.range g = S := by ext y; simp [g]
  have hobs : 1 + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hclean' : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ Set.range g := by simpa only [hrange] using hclean
  obtain ⟨f', hf', hrel, hemb, hi, havoid⟩ :=
    exists_relative_curve_avoidance_of_clean_neighborhood f g hf hg hdim hobs hK hC hBC hfixed
      hderiv hclean'
  refine ⟨f', hf', hrel, hemb, hi, ?_⟩
  simpa only [hrange] using havoid
