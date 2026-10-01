/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Immersion.Relative.Curve

/-!
# Making a map immersive by small perturbations

General position for the immersion condition, in charts: a smooth map can be moved by a compactly
supported weighted perturbation, keeping an open property, so that it becomes immersive along a
family of base points (`ManifoldImmersion.exists_weighted_immersive_patch_with_property`). Along the
zero set of a weight the perturbation preserves the kernel conditions
(`ChartMapPerturbation.common_kernel_preserved_on_zero_set`); one repair step, its finite iteration
and the compact case (`ManifoldImmersion.exists_compact_boundary_derivative_repair`) make the map
immersive on the image of a compact family by a homotopy relative to the zero set of the weight.

With the endpoint function `t (1 - t)` (`CurveImmersion.endpointFunction`) as weight: a smooth curve
in a manifold of dimension at least two is homotopic relative to its endpoints to a curve with
injective differential at both endpoints
(`ManifoldImmersion.exists_curve_endpoint_derivative_repair`).

Cf. Hirsch, *Differential Topology*, Ch. 2 (density of immersions, approximation relative to a
closed set).

## Tags

immersion, general position, perturbation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- General-position perturbation in a chart: a smooth map can be moved by a compactly supported
weighted perturbation, keeping a prescribed open property, so that it becomes immersive along a
given family of base points. -/
theorem ManifoldImmersion.exists_weighted_immersive_patch_with_property
    {B E G F H H' X N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ B H}
    {J : ModelWithCorners ℝ G H'} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [LindelofSpace (X × E)] [TopologicalSpace N] [ChartedSpace H' N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) {β χ : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {S : Set X}
    (hplateau : ∀ x ∈ S, b x ∈ interior {y | χ y = 1})
    (hcommon : ∀ x ∈ S, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 → fderiv ℝ β (b x) v = 0 → v = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F) (Q : (E → N) → Prop)
    (hQ : ∀ᶠ a : F in 𝓝 0, Q (ChartMapPerturbation.perturb c f β a)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Q g ∧
          f.HomotopicRel g {y | β y = 0} ∧
            ∀ x ∈ S, Function.Injective (mfderiv 𝓘(ℝ, E) J g (b x)) := by
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k := fun _ =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  have hQmem : {a : F | Q (ChartMapPerturbation.perturb c f β a)} ∈ 𝓝 0 := hQ
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨a, ha, -, hkernel⟩ :=
    WeightedPerturbation.exists_small_parameter_with_common_kernel hb hk hβ hdim
      (lt_min hε hδ)
  have haε : ‖a‖ < ε := (lt_min_iff.mp ha).1
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).2
  have hv := hvalid a haε
  have hsmooth := ChartMapPerturbation.contMDiff_perturb c hf hβ.contMDiff hsupport hv
  let g : C(E, N) := ⟨ChartMapPerturbation.perturb c f β a, hsmooth.continuous⟩
  have hQg : Q g :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine
    ⟨g, hsmooth, hQg,
      ⟨ChartMapPerturbation.homotopyRel c hf hβ.contMDiff hsupport hvalid haε⟩, ?_⟩
  intro x hx
  have hxplateau := hplateau x hx
  have hsource (y : E) (hy : χ y = 1) : f y ∈ c.source :=
    hχsupport (subset_tsupport χ (by change χ y ≠ 0; rw [hy]; exact one_ne_zero))
  have hxone : χ (b x) = 1 := interior_subset (s := {y | χ y = 1}) hxplateau
  have hfx := hsource (b x) hxone
  have hgx : g (b x) ∈ c.source := ChartMapPerturbation.perturb_mem_source c f β hv hfx
  have heqold : k =ᶠ[𝓝 (b x)] (c ∘ f) := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    exact
      ChartMapPerturbation.cutoffCoordinates_eq_of_one c f χ
        (interior_subset (s := {y | χ y = 1}) hy)
  have heqnew : (c ∘ g) =ᶠ[𝓝 (b x)] WeightedPerturbation.perturb k β a := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    have hyone : χ y = 1 := interior_subset (s := {y | χ y = 1}) hy
    change c (ChartMapPerturbation.perturb c f β a y) = _
    rw [ChartMapPerturbation.chart_perturb c f β hv (hsource y hyone)]
    simp only [ChartMapPerturbation.coordinateFamily, WeightedPerturbation.perturb, k,
      ChartMapPerturbation.cutoffCoordinates, hyone, one_smul]
  apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgx).mp
  change Function.Injective (fderiv ℝ (c ∘ g) (b x))
  rw [heqnew.fderiv_eq]
  intro v w hvw
  have hzero : fderiv ℝ (WeightedPerturbation.perturb k β a) (b x) (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  obtain ⟨hkzero, hβzero⟩ := (hkernel x (v - w)).mp hzero
  have hnative : mfderiv 𝓘(ℝ, E) J f (b x) (v - w) = 0 := by
    apply (fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hfx (v - w)).mp
    rw [← heqold.fderiv_eq]
    exact hkzero
  exact sub_eq_zero.mp (hcommon x hx (v - w) hnative hβzero)

/-- For a weighted chart perturbation, a tangent vector killed by the derivative of the weight is
killed by the derivative of the perturbed map exactly when it is killed by the derivative of the
original one. -/
theorem ChartMapPerturbation.derivative_eq_zero_iff_of_weight_derivative_eq_zero
    {E G F H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : F} (ha : Valid c f β a) {x v : E} (hweight : fderiv ℝ β x v = 0) :
    mfderiv 𝓘(ℝ, E) J (perturb c f β a) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  by_cases hx : f x ∈ c.source
  · have hsmooth := contMDiff_perturb c hf hβ.contMDiff hsupport ha
    have hgx := perturb_mem_source c f β ha hx
    have hcf : ContDiffAt ℝ ∞ (c ∘ f) x :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp x
          hf.contMDiffAt) |>.contDiffAt
    have hcd :
      HasFDerivAt (fun y => c (f y) + β y • a) (fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a)
        x :=
      (hcf.differentiableAt (by simp)).hasFDerivAt.add
        ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)
    have heq : (c ∘ perturb c f β a) =ᶠ[𝓝 x] (fun y => c (f y) + β y • a) := by
      filter_upwards [(c.open_source.preimage hf.continuous).mem_nhds hx] with y hy
      exact chart_perturb c f β ha hy
    have hderiv :
      fderiv ℝ (c ∘ perturb c f β a) x = fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a :=
      heq.fderiv_eq.trans hcd.fderiv
    rw [←
      ManifoldImmersion.fderiv_chart_eq_zero_iff c (hsmooth.mdifferentiableAt (by simp)) hgx
        v,
      ← ManifoldImmersion.fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hx v,
      hderiv]
    change fderiv ℝ (c ∘ f) x v + fderiv ℝ β x v • a = 0 ↔ fderiv ℝ (c ∘ f) x v = 0
    rw [hweight, zero_smul, add_zero]
  · have hn : x ∉ tsupport β := fun ht => hx (hsupport ht)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hn
    have heq : perturb c f β a =ᶠ[𝓝 x] f := by
      filter_upwards [hzero] with y hy
      exact perturb_eq_of_zero c f β a hy
    rw [heq.mfderiv_eq]
    rfl

/-- If a weight vanishes at `x` together with its derivative in the direction `v`, then so does any
smooth multiple of it. -/
theorem ChartMapPerturbation.fderiv_cutoff_mul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ) {x v : E}
    (hx : ρ x = 0) (hv : fderiv ℝ ρ x v = 0) : fderiv ℝ (fun y => ψ y * ρ y) x v = 0 := by
  rw [fderiv_fun_mul (hψ.differentiable (by simp) x) (hρ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, hx, hv, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, add_zero]

/-- The perturbation with a cut-off weight preserves the condition that the differential of the map
and the derivative of the weight have no common kernel on the zero set of the weight. -/
theorem ChartMapPerturbation.common_kernel_preserved_on_zero_set {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {ψ ρ : E → ℝ} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ)
    (hsupport : tsupport (fun y => ψ y * ρ y) ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f (fun y => ψ y * ρ y) a)
    (hcommon : ∀ x, ρ x = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f x v = 0 → fderiv ℝ ρ x v = 0 → v = 0) :
    ∀ x,
      ρ x = 0 →
        ∀ v,
          mfderiv 𝓘(ℝ, E) J (perturb c f (fun y => ψ y * ρ y) a) x v = 0 →
            fderiv ℝ ρ x v = 0 → v = 0 := by
  intro x hx v hzero hv
  have hweight := fderiv_cutoff_mul_eq_zero hψ hρ hx hv
  have hold :=
    (derivative_eq_zero_iff_of_weight_derivative_eq_zero c hf (hψ.mul hρ) hsupport ha hweight).mp
      hzero
  exact hcommon x hx v hold hv

/-- One step of the repair of the immersion property along the zero set of a weight: the map can be
perturbed inside one patch, relative to that zero set, to become immersive on the given compact
set together with the plateau of the patch. -/
theorem ManifoldImmersion.exists_boundary_derivative_repair_step {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N)) (i : ι)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G) {K L : Set E}
    (hK : IsCompact K) (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hLsub : L ⊆ (p i).plateau) (hLrange : L ⊆ Set.range b)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          f.HomotopicRel g {y | ρ y = 0} ∧
            (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) ∧
              ∀ y ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  let β : E → ℝ := fun y => (p i).cutoff y * ρ y
  have hβ : ContDiff ℝ ∞ β := (p i).smooth.contDiff.mul hρ
  have hcompact : HasCompactSupport β := (p i).compact.mul_right
  have hsupport : tsupport β ⊆ f ⁻¹' (p i).chart.source :=
    tsupport_mul_subset_left.trans ((p i).inner_compatible (hcompatible i))
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f β a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hβ.contMDiff
        hsupport (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hβ.contMDiff
      hcompact hsupport hK hinj
  let Common (g : E → N) : Prop :=
    ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0
  have hretain :
    ∀ᶠ a in 𝓝 (0 : G), Common (ChartMapPerturbation.perturb (p i).chart f β a) := by
    filter_upwards [ChartMapPerturbation.eventually_valid (p i).chart hf hβ.contMDiff
        hcompact hsupport] with
      a ha
    exact
      ChartMapPerturbation.common_kernel_preserved_on_zero_set (p i).chart hf
        (p i).smooth.contDiff hρ hsupport ha hcommon
  let Q : (E → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧ (∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g y)) ∧ Common g
  have hQ : ∀ᶠ a in 𝓝 (0 : G), Q (ChartMapPerturbation.perturb (p i).chart f β a) :=
    hkeep.and (hold.and hretain)
  have houter : (p i).plateau ⊆ interior {y | (p i).outer y = 1} := by
    apply isOpen_interior.subset_interior_iff.mpr
    intro y hy
    apply (p i).nested y
    apply subset_tsupport (p i).cutoff
    change (p i).cutoff y ≠ 0
    rw [interior_subset (s := {y | (p i).cutoff y = 1}) hy]
    exact one_ne_zero
  have hplateau : ∀ x ∈ b ⁻¹' L, b x ∈ interior {y | (p i).outer y = 1} := fun _ hx =>
    houter (hLsub hx)
  have hcommonβ :
    ∀ x ∈ b ⁻¹' L, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 → fderiv ℝ β (b x) v = 0 → v = 0 := by
    intro x hx v hfv hβv
    have heq : β =ᶠ[𝓝 (b x)] ρ := by
      filter_upwards [(p i).plateau_eventually_one (hLsub hx)] with y hy
      simp only [β, hy, one_mul]
    apply hcommon (b x) (hzero x) v hfv
    rw [← heq.fderiv_eq]
    exact hβv
  obtain ⟨g, hg, ⟨hc, hinjg, hcommong⟩, ⟨Hrel⟩, hnew⟩ :=
    exists_weighted_immersive_patch_with_property (p i).chart f hf hb hβ
      (p i).outer_smooth.contDiff hcompact hsupport (hcompatible i) hplateau hcommonβ hdim Q hQ
  refine ⟨g, hg, hc, ?_, hcommong, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := ?_ }⟩
    intro t y hy
    apply Hrel.eq_fst t
    change (p i).cutoff y * ρ y = 0
    rw [hy, MulZeroClass.mul_zero]
  · intro y hy
    rcases hy with hy | hy
    · exact hinjg y hy
    · obtain ⟨x, rfl⟩ := hLrange hy
      exact hnew x hy

/-- Iterating the repair step over a finite set of patches. -/
theorem ManifoldImmersion.exists_finite_boundary_derivative_repair {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N))
    (L : ι → Set E) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f) {b : X → E}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hLrange : ∀ i, L i ⊆ Set.range b) {ρ : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0)
    (s : Finset ι) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          f.HomotopicRel g {y | ρ y = 0} ∧
            (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) ∧
              ∀ y ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, hcommon, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hcommon₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hcommon₂, hinj₂⟩ :=
      exists_boundary_derivative_repair_step p i g₁ hg₁ hc₁ hb hρ hzero hdim hKold hinj₁ (hLsub i)
        (hLrange i) hcommon₁
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hcommon₂, ?_⟩
    intro y hy
    apply hinj₂ y
    rcases hy with hy | hy
    · exact Or.inl (Or.inl hy)
    · obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hyj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, hyj⟩))

/-- The compact case of the repair: a smooth map can be made immersive at every point of the image
of a compact parameter family, by a homotopy relative to the zero set of the weight. -/
theorem ManifoldImmersion.exists_compact_boundary_derivative_repair {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X]
    [LindelofSpace (X × E)] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g {y | ρ y = 0} ∧
          ∀ y ∈ Set.range b, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
  have hboundary : IsCompact (Set.range b) := isCompact_range hb.continuous
  have hp (x : Set.range b) :
    ∃ p : ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ D : Set E, p.Compatible f ∧ IsCompact D ∧ D ∈ 𝓝 x.1 ∧ D ⊆ p.plateau := by
    obtain ⟨p, hcompatible, hplateau⟩ :=
      ManifoldSmoothing.exists_smoothing_patch_at (I := 𝓘(ℝ, E)) (J := J) f x.1
    obtain ⟨D, hDx, hDsub, hD⟩ := local_compact_nhds (isOpen_interior.mem_nhds hplateau)
    exact ⟨p, D, hcompatible, hD, hDx, hDsub⟩
  choose p D hcompatible hD hn hsub using hp
  have hcover : Set.range b ⊆ ⋃ x : Set.range b, interior (D x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ :=
    hboundary.elim_finite_subcover (fun x : Set.range b => interior (D x))
      (fun _ => isOpen_interior) hcover
  let L (i : s) := Set.range b ∩ D i.1
  have hL (i : s) : IsCompact (L i) := hboundary.inter_right (hD i.1).isClosed
  have hLsub (i : s) : L i ⊆ (p i.1).plateau := fun _ hx => hsub i.1 hx.2
  have hLrange (i : s) : L i ⊆ Set.range b := Set.inter_subset_left
  obtain ⟨g, hg, -, hhom, -, hinj⟩ :=
    exists_finite_boundary_derivative_repair (fun i : s => p i.1) L hL hLsub f hf
      (fun i => hcompatible i.1) hb hLrange hρ hzero hdim isCompact_empty
      (fun _ hx => False.elim hx) hcommon Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro y hy
  obtain ⟨i, hi, hyD⟩ := Set.mem_iUnion₂.mp (hs hy)
  apply hinj y
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hy, interior_subset hyD⟩)

/-- The function `t (1 - t)`, which vanishes exactly at the two endpoints of the unit interval. -/
def CurveImmersion.endpointFunction (t : ℝ) : ℝ :=
  t * (1 - t)

/-- The endpoint function is smooth. -/
theorem CurveImmersion.contDiff_endpointFunction : ContDiff ℝ ∞ endpointFunction := by
  unfold endpointFunction
  fun_prop

/-- The endpoint function vanishes exactly at `0` and `1`. -/
theorem CurveImmersion.endpointFunction_eq_zero_iff (t : ℝ) :
    endpointFunction t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [endpointFunction, mul_eq_zero, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

/-- The derivative of the endpoint function is `v ↦ v (1 - 2 t)`. -/
theorem CurveImmersion.fderiv_endpointFunction (t v : ℝ) :
    fderiv ℝ endpointFunction t v = v * (1 - 2 * t) := by
  have hd : HasDerivAt endpointFunction (1 * (1 - t) + t * (0 - 1)) t :=
    (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have heq : 1 * (1 - t) + t * (0 - 1) = 1 - 2 * t := by ring
  rw [heq] at hd
  rw [hd.hasFDerivAt.fderiv]
  rfl

/-- At a zero of the endpoint function the derivative is injective, since `1 - 2t = ±1` there. -/
theorem CurveImmersion.injective_endpointFunction_derivative {t : ℝ}
    (ht : endpointFunction t = 0) {v : ℝ} (hv : fderiv ℝ endpointFunction t v = 0) : v = 0 := by
  rw [fderiv_endpointFunction] at hv
  rcases (endpointFunction_eq_zero_iff t).mp ht with rfl | rfl
  · simpa using hv
  · norm_num at hv
    exact hv

/-- A smooth curve in a manifold of dimension at least two can be homotoped, relative to the two
endpoints, to a curve whose differential is injective at both endpoints. -/
theorem ManifoldImmersion.exists_curve_endpoint_derivative_repair {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        f.HomotopicRel g ({0, 1} : Set ℝ) ∧
          ∀ t ∈ ({0, 1} : Set ℝ), Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let X := ({0, 1} : Set ℝ)
  let : Fintype X := ((Set.finite_singleton (1 : ℝ)).insert 0).fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z X := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ X := IsManifold.of_discreteTopology _
  let b : X → ℝ := Subtype.val
  have hb : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ b := contMDiff_of_discreteTopology
  have hrange : Set.range b = ({0, 1} : Set ℝ) := by ext t; simp [b, X]
  have hzero : ∀ x, CurveImmersion.endpointFunction (b x) = 0 := by
    intro x
    apply (CurveImmersion.endpointFunction_eq_zero_iff _).mpr
    exact x.property
  have hzset : {t | CurveImmersion.endpointFunction t = 0} = ({0, 1} : Set ℝ) := by
    ext t
    simp only [Set.mem_ofPred_eq, CurveImmersion.endpointFunction_eq_zero_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have hd : Module.finrank ℝ Z + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  obtain ⟨g, hg, hrel, hi⟩ :=
    exists_compact_boundary_derivative_repair f hf hb
      CurveImmersion.contDiff_endpointFunction hzero hd
      (fun _ ht _ _ hv => CurveImmersion.injective_endpointFunction_derivative ht hv)
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [hzset] using hrel
  · simpa only [hrange] using hi

end
