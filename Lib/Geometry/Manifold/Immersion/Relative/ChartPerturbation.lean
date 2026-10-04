/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence.ChartPerturbation
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension
public import Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus

/-!
# General position for chart-supported perturbations

For a smooth map `f : X → N`, a chart `c : N → F` of the target and a cutoff `β : X → ℝ` supported in
`f ⁻¹' c.source`, the chart-supported perturbation `ChartMapPerturbation.perturb c f β a` moves `f`
inside the chart by `β x • a`. This module contains the Sard-type count controlling such
perturbations. The parameters `a` for which the perturbed map identifies two points that `f` (or the
cutoff) distinguishes are the image of the open set `ChartMapPerturbation.collisionDomain` under
the smooth map `ChartMapPerturbation.collisionParameter`; that image has Hausdorff dimension at most
`2 dim X`, so when `2 dim X < dim F` arbitrarily small parameters create no new double point
(`ChartMapPerturbation.exists_small_collision_removing_parameter`). Likewise the parameters making
`f x` hit an obstacle `g y`, `g : Y → N`, form the image of `ChartMapPerturbation.obstacleDomain`, of
dimension at most `dim X + dim Y` (`ChartMapPerturbation.exists_small_embedding_avoiding_parameter`
combines both counts). Small perturbations keep `f` an immersion on a compact set
(`ChartMapPerturbation.eventually_perturb_injective_derivative`).

## References

* Whitney, *Differentiable manifolds*, Thm 5 (the counting argument).
* Hirsch, *Differential Topology*, Ch. 2 §2 and Ch. 3 §2 (general position).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- The pairs of distinct points of the source at which a chart-supported perturbation could create
a double point: both are in the chart and the cutoff distinguishes them. -/
def ChartMapPerturbation.collisionDomain {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) : Set (X × X) :=
  {q | f q.1 ∈ c.source ∧ f q.2 ∈ c.source ∧ β q.1 - β q.2 ≠ 0}

/-- The parameter value that would make the two points of a pair collide under the chart-supported
perturbation. -/
def ChartMapPerturbation.collisionParameter {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (q : X × X) : F :=
  (β q.1 - β q.2)⁻¹ • (c (f q.2) - c (f q.1))

/-- The collision domain is open. -/
theorem ChartMapPerturbation.isOpen_collisionDomain {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) : IsOpen (collisionDomain c f β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hf.comp continuous_snd)).inter
      (isOpen_ne_fun ((hβ.comp continuous_fst).sub (hβ.comp continuous_snd)) continuous_const))

/-- The collision parameter is smooth on the collision domain, so its image is a set of measure zero
once the dimensions allow. -/
theorem ChartMapPerturbation.contMDiffOn_collisionParameter {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I) 𝓘(ℝ, F) ∞ (collisionParameter c f β) (collisionDomain c f β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hf.comp contMDiff_snd).contMDiffAt
  have hb : ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) ∞ (fun r : X × X => β r.1 - β r.2) q :=
    (hβ.comp contMDiff_fst).contMDiffAt.sub (hβ.comp contMDiff_snd).contMDiffAt
  exact ((hb.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

/-- If the parameter avoids the image of the collision map, then the perturbed map identifies two
points only when the original map does and the cutoff agrees there. -/
theorem ChartMapPerturbation.collision_imp_old_and_equal_cutoff {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (hvalid : Valid c f β a)
    (hgood : a ∉ collisionParameter c f β '' collisionDomain c f β) {x y : X}
    (heq : perturb c f β a x = perturb c f β a y) : f x = f y ∧ β x = β y := by
  classical
  by_cases hx : f x ∈ c.source
  · have hpy : perturb c f β a y ∈ c.source := heq ▸ perturb_mem_source c f β hvalid hx
    have hy : f y ∈ c.source := by
      by_contra hn
      simp only [perturb, hn, if_false] at hpy
    have hcoord : c (f x) + β x • a = c (f y) + β y • a := by
      have hh := congrArg c heq
      simpa only [chart_perturb c f β hvalid hx, chart_perturb c f β hvalid hy,
        coordinateFamily] using hh
    by_cases hb : β x = β y
    · refine ⟨c.toPartialEquiv.injOn hx hy ?_, hb⟩
      rw [hb] at hcoord
      exact add_right_cancel hcoord
    · have hd : β x - β y ≠ 0 := sub_ne_zero.mpr hb
      have hs : (β x - β y) • a = c (f y) - c (f x) := by
        rw [sub_smul]
        exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hcoord)
      exfalso
      apply hgood
      refine ⟨(x, y), ⟨hx, hy, hd⟩, ?_⟩
      change (β x - β y)⁻¹ • (c (f y) - c (f x)) = a
      rw [← hs, inv_smul_smul₀ hd]
  · have hpx : perturb c f β a x = f x := by simp only [perturb, hx, if_false]
    have hy : f y ∉ c.source := by
      intro hy
      have hpy := perturb_mem_source c f β hvalid hy
      rw [← heq, hpx] at hpy
      exact hx hpy
    have hpy : perturb c f β a y = f y := by simp only [perturb, hy, if_false]
    have hβx : β x = 0 := by
      by_contra hn
      exact hx (hsupport (subset_tsupport β hn))
    have hβy : β y = 0 := by
      by_contra hn
      exact hy (hsupport (subset_tsupport β hn))
    exact ⟨hpx.symm.trans (heq.trans hpy), hβx.trans hβy.symm⟩

/-- Sard-type statement: if `2 dim X < dim F`, arbitrarily small parameters `a` give a smooth
perturbation that creates no new double points. -/
theorem ChartMapPerturbation.exists_small_collision_removing_parameter
    {E G F H K X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [IsManifold I ∞ X] [LindelofSpace (X × X)] (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧
            ∀ x y, perturb c f β a x = perturb c f β a y → f x = f y ∧ β x = β y := by
  have hd : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hdim
  have hdense :=
    GeneralPosition.dense_compl_manifold_image
      (isOpen_collisionDomain c hf.continuous hβ.continuous)
      (contMDiffOn_collisionParameter c hf hβ) hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < Min.min ε δ := by simpa only [dist_zero_left] using har
  have hv := hvalid a (lt_of_lt_of_le ha (min_le_right _ _))
  exact
    ⟨a, lt_of_lt_of_le ha (min_le_left _ _), hv, contMDiff_perturb c hf hβ hsupport hv,
      fun _ _ heq => collision_imp_old_and_equal_cutoff c hsupport hv hgood heq⟩

/-- The pairs `(x, y) ∈ X × Y` at which a chart-supported perturbation of `f` could make `f x` hit
`g y`. -/
def ChartMapPerturbation.obstacleDomain {G F K X Y N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ) : Set (X × Y) :=
  {q | f q.1 ∈ c.source ∧ g q.2 ∈ c.source ∧ β q.1 ≠ 0}

/-- The parameter value that would make `f x` hit the obstacle point `g y`. -/
def ChartMapPerturbation.obstacleParameter {G F K X Y N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ) (q : X × Y) :
    F :=
  (β q.1)⁻¹ • (c (g q.2) - c (f q.1))

/-- The obstacle domain is open. -/
theorem ChartMapPerturbation.isOpen_obstacleDomain {G F K X Y N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N}
    {g : Y → N} {β : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hβ : Continuous β) :
    IsOpen (obstacleDomain c f g β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hg.comp continuous_snd)).inter
      (isOpen_ne_fun (hβ.comp continuous_fst) continuous_const))

/-- The obstacle parameter is smooth on the obstacle domain. -/
theorem ChartMapPerturbation.contMDiffOn_obstacleParameter {E E' G F H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N}
    {β : X → ℝ} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ (obstacleParameter c f g β) (obstacleDomain c f g β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (g r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hg.comp contMDiff_snd).contMDiffAt
  exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

/-- If the parameter avoids the image of the obstacle map, the perturbed map misses the obstacle
wherever the cutoff is nonzero. -/
theorem ChartMapPerturbation.avoids_of_not_obstacle_parameter {G F K X Y N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N}
    {β : X → ℝ} (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (ha : Valid c f β a)
    (hgood : a ∉ obstacleParameter c f g β '' obstacleDomain c f g β) (x : X) (hx : β x ≠ 0)
    (y : Y) : perturb c f β a x ≠ g y := by
  intro heq
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := heq ▸ perturb_mem_source c f β ha hfx
  have hcoord : c (f x) + β x • a = c (g y) := by
    rw [← heq, chart_perturb c f β ha hfx]
    rfl
  apply hgood
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← hcoord, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- General position in a chart: if `2 dim X < dim F` and `dim X + dim Y < dim F`, arbitrarily small
parameters give a smooth perturbation that creates no new double points and avoids the image of
`g` wherever the cutoff is nonzero. -/
theorem ChartMapPerturbation.exists_small_embedding_avoiding_parameter
    {E E' G F H H' K X Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × X)] [LindelofSpace (X × Y)] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧
            (∀ x y, perturb c f β a x = perturb c f β a y → f x = f y) ∧
              ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  have hdself : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hself
  have hdobstacle : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hobstacle
  have hs :=
    GeneralPosition.dimH_image_manifold_le
      (isOpen_collisionDomain c hf.continuous hβ.continuous)
      (contMDiffOn_collisionParameter c hf hβ)
  have ho :=
    GeneralPosition.dimH_image_manifold_le
      (isOpen_obstacleDomain c hf.continuous hg.continuous hβ.continuous)
      (contMDiffOn_obstacleParameter c hf hg hβ)
  have hdense :
    Dense
      ((collisionParameter c f β '' collisionDomain c f β) ∪
          (obstacleParameter c f g β '' obstacleDomain c f g β))ᶜ := by
    apply dense_compl_of_dimH_lt_finrank
    rw [dimH_union]
    exact max_lt (hs.trans_lt (Nat.cast_lt.mpr hdself)) (ho.trans_lt (Nat.cast_lt.mpr hdobstacle))
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < Min.min ε δ := by simpa only [dist_zero_left] using hnorm
  have hv := hvalid a (lt_min_iff.mp ha).2
  refine ⟨a, (lt_min_iff.mp ha).1, hv, contMDiff_perturb c hf hβ hsupport hv, ?_, ?_⟩
  · intro x y hxy
    exact (collision_imp_old_and_equal_cutoff c hsupport hv (fun h => hgood (Or.inl h)) hxy).1
  · exact avoids_of_not_obstacle_parameter c hsupport hv (fun h => hgood (Or.inr h))


/-- Small chart-supported perturbations preserve the immersion property on a compact set. -/
theorem ChartMapPerturbation.eventually_perturb_injective_derivative {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∀ᶠ a : F in 𝓝 0, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β a) x) := by
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  let W : Set (F × E) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily :
    ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, E)) J ∞ (fun q : F × E => perturb c f β q.1 q.2) W := by
    intro q hq
    exact (contMDiffAt_perturb c hf hβ hsupport q (hvalid q.1 hq)).contMDiffWithinAt
  apply ManifoldImmersion.eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    have heq : perturb c f β (0 : F) = f := funext (perturb_zero c f β)
    change Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β (0 : F)) x)
    rw [heq]
    exact hinj x hx
