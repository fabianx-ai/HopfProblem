/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence

/-!
# The immersion locus and local injectivity

Basic facts about smooth maps `f : E → N` from a normed space into a manifold. Being an immersion
at `x` (injectivity of `mfderiv 𝓘(ℝ, E) J f x`) can be tested in a chart of the target
(`ManifoldImmersion.injective_fderiv_chart_iff`, `ManifoldImmersion.fderiv_chart_eq_zero_iff`). The set
of points at which `f` is an immersion is open (`ManifoldImmersion.isOpen_injective_derivative`, also
on an open set and for a smooth family of maps, `isOpen_injective_nativeDerivative`), so being an
immersion on a compact set is an open condition on the parameter of a family
(`ManifoldImmersion.eventually_injective_nativeDerivative`).

The local immersion theorem gives injectivity near a point where the derivative is injective
(`ManifoldImmersion.exists_open_injOn_of_injective_fderiv` and its manifold forms), and an
injective immersion on a compact set is an injective immersion on a neighbourhood of that set
(`ManifoldImmersion.exists_open_embedded_immersive_neighborhood`). The set of pairs of distinct
points of a compact set with the same image, `ManifoldImmersion.doublePoints`, is compact for a
locally injective map, in particular for an immersion
(`ManifoldImmersion.isCompact_doublePoints_of_injective_nativeDerivative`). Precomposition with a linear
isomorphism preserves the immersion condition (`ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff`).

## References

* Hirsch, *Differential Topology*, Ch. 1 (the local immersion theorem).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- Being an immersion at a point can be tested in a chart: the Fréchet derivative of the chart
representative is injective if and only if the manifold derivative is. -/
theorem ManifoldImmersion.injective_fderiv_chart_iff {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x) (hx : f x ∈ c.source) :
    Function.Injective (fderiv ℝ (c ∘ f) x) ↔ Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  have hderiv : fderiv ℝ (c ∘ f) x = (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv (by simp)).injective
  rw [hderiv]
  constructor
  · intro h v w hvw
    exact h (congrArg (mfderiv J 𝓘(ℝ, F) c (f x)) hvw)
  · exact fun h => hc.comp h

/-- A tangent vector is in the kernel of the chart representative's derivative exactly when it is in
the kernel of the manifold derivative. -/
theorem ManifoldImmersion.fderiv_chart_eq_zero_iff {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x) (hx : f x ∈ c.source) (v : E) :
    fderiv ℝ (c ∘ f) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  have hderiv : fderiv ℝ (c ∘ f) x = (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv (by simp)).injective
  rw [hderiv]
  change (mfderiv J 𝓘(ℝ, F) c (f x)) (mfderiv 𝓘(ℝ, E) J f x v) = 0 ↔ _
  constructor
  · intro h
    apply hc
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- For a smooth family of maps, the set of parameters and points at which the map is an immersion
is open. -/
theorem ManifoldImmersion.isOpen_injective_nativeDerivative {P E G H N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : P → E → N} {W : Set (P × E)} (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) :
    IsOpen {q : P × E | q ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqinj⟩
  let c := modelChartPartialDiffeomorph (I := J) (f q.1 q.2)
  let U := W ∩ (Function.uncurry f) ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hqU : q ∈ U := ⟨hq, mem_extChartAt_source (f q.1 q.2)⟩
  have hc : ContDiffOn ℝ ∞ (fun r : P × E => c (f r.1 r.2)) U := by
    intro r hr
    have hmap :
      ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞ (fun s : P × E => (s.1, s.2)) r :=
      contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
    have hfr := (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r hmap
    exact
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r
          hfr) |>.contDiffAt.contDiffWithinAt
  have hd :=
    MorsePerturbation.contDiffOn_spatialDerivative (f := fun a x => c (f a x)) hU hc
  have hgood :
    IsOpen
      (U ∩
        (fun r : P × E => fderiv ℝ (c ∘ f r.1) r.2) ⁻¹' {L : E →L[ℝ] G | Function.Injective L}) :=
    hd.continuousOn.isOpen_inter_preimage hU ContinuousLinearMap.isOpen_injective
  have hiff (r : P × E) (hr : r ∈ U) :
    Function.Injective (fderiv ℝ (c ∘ f r.1) r.2) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J (f r.1) r.2) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) J ∞ (f r.1) r.2 :=
      (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r.2 (f := fun x : E => (r.1, x))
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact injective_fderiv_chart_iff c (hs.mdifferentiableAt (by simp)) hr.2
  have hn := hgood.mem_nhds ⟨hqU, (hiff q hqU).mpr hqinj⟩
  apply Filter.mem_of_superset hn
  intro r hr
  exact ⟨hr.1.1, (hiff r hr.1).mp hr.2⟩

/-- The set of points of an open set at which a smooth map is an immersion is open. -/
theorem ManifoldImmersion.isOpen_injective_derivative_on {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N} {W : Set E}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) :
    IsOpen {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) (Prod.snd ⁻¹' W) :=
    hf.comp contMDiff_snd.contMDiffOn (fun _ hp => hp)
  have hopen :=
    (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f) (hW.preimage continuous_snd)
          hfamily).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  exact hopen

/-- The immersion locus of a smooth map is open. -/
theorem ManifoldImmersion.isOpen_injective_derivative {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) :
    IsOpen {x : E | Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) :=
    hf.comp contMDiff_snd
  have hopen :=
    (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f) isOpen_univ
          hfamily.contMDiffOn).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  change IsOpen {x : E | True ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} at hopen
  simpa only [true_and] using hopen

/-- Being an immersion on a compact set is an open condition on the parameter of a smooth family. -/
theorem ManifoldImmersion.eventually_injective_nativeDerivative {P E G H N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : P → E → N} {W : Set (P × E)} (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) {K : Set E}
    (hK : IsCompact K) {a₀ : P} (hmem : ∀ x ∈ K, (a₀, x) ∈ W)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a₀) x)) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a) x) := by
  have hopen :=
    MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_injective_nativeDerivative hW hf)
  have hn := hopen.mem_nhds (fun x hx => ⟨hmem x hx, hinj x hx⟩)
  filter_upwards [hn] with a ha x hx
  exact (ha x hx).2


/-- Local injectivity from an injective derivative: a smooth map with injective derivative at `x` is
injective on a neighbourhood of `x` (the local immersion theorem, Hirsch, *Differential
Topology*, Ch. 1). -/
theorem ManifoldImmersion.exists_open_injOn_of_injective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ Set.InjOn f V := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hdf := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hderiv : HasFDerivAt (L ∘ f) (ContinuousLinearMap.id ℝ E) x := by
    convert L.hasFDerivAt.comp x hdf.hasFDerivAt using 1
    ext v
    exact (hL v).symm
  have hcomp : ContDiffOn ℝ ∞ (L ∘ f) U := L.contDiff.comp_contDiffOn hf
  have hinv : (fderiv ℝ (L ∘ f) x).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨φ, hxφ, hφU, hφeq⟩ := exists_partialDiffeomorph_of_contDiffOn hU hx hcomp hinv
  refine ⟨φ.source, φ.open_source, hxφ, hφU, ?_⟩
  intro y hy z hz hyz
  apply φ.toPartialEquiv.injOn hy hz
  rw [hφeq]
  exact congrArg L hyz

/-- Manifold form of local injectivity, for a map smooth on an open set. -/
theorem ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : E → N} {W : Set E} (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W)
    {x : E} (hxW : x ∈ W) (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ Set.InjOn f V := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  have hx : f x ∈ c.source := mem_extChartAt_source (f x)
  let U := W ∩ f ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hc : ContDiffOn ℝ ∞ (c ∘ f) U :=
    (c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ h => h.2)).contDiffOn
  have hfx := hf.contMDiffAt (hW.mem_nhds hxW)
  have hi := (injective_fderiv_chart_iff c (hfx.mdifferentiableAt (by simp)) hx).mpr hinj
  obtain ⟨V, hV, hxV, hVU, hinjV⟩ := exists_open_injOn_of_injective_fderiv hU ⟨hxW, hx⟩ hc hi
  exact
    ⟨V, hV, hxV, hVU.trans Set.inter_subset_left, fun _ hy _ hz heq =>
      hinjV hy hz (congrArg c heq)⟩

/-- Manifold form of local injectivity for a globally smooth map. -/
theorem ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {x : E}
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ Set.InjOn f V := by
  obtain ⟨V, hV, hxV, _, hinjV⟩ :=
    exists_open_injOn_of_injective_nativeDerivative_on isOpen_univ hf.contMDiffOn (Set.mem_univ x)
      hinj
  exact ⟨V, hV, hxV, hinjV⟩

/-- An injective immersion on a compact set is injective on a neighbourhood of that set. -/
theorem ManifoldImmersion.exists_open_injOn_near_compact_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ Set.InjOn f V := by
  have hc : ∀ x ∈ K, ContinuousAt f x := fun x hx =>
    hf.continuousOn.continuousAt (hW.mem_nhds (hKW hx))
  have hlocal : ∀ x ∈ K, ∃ V ∈ nhds x, Set.InjOn f V := by
    intro x hx
    obtain ⟨V, hV, hxV, _, hinjV⟩ :=
      exists_open_injOn_of_injective_nativeDerivative_on hW hf (hKW hx) (hi x hx)
    exact ⟨V, hV.mem_nhds hxV, hinjV⟩
  obtain ⟨V, hV, hKV, hinjV⟩ := hinj.exists_isOpen_superset hK hc hlocal
  exact
    ⟨V ∩ W, hV.inter hW, fun _ hx => ⟨hKV hx, hKW hx⟩, Set.inter_subset_right,
      hinjV.mono Set.inter_subset_left⟩

/-- An injective immersion on a compact set is an injective immersion on a neighbourhood of that
set. -/
theorem ManifoldImmersion.exists_open_embedded_immersive_neighborhood {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧ V ⊆ W ∧ Set.InjOn f V ∧ ∀ x ∈ V, Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  let O := {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)}
  have hO : IsOpen O := isOpen_injective_derivative_on hW hf
  have hOW : O ⊆ W := fun _ hx => hx.1
  obtain ⟨V, hV, hKV, hVO, hinjV⟩ :=
    exists_open_injOn_near_compact_on hO (hf.mono hOW) hK (fun x hx => ⟨hKW hx, hi x hx⟩) hinj hi
  exact ⟨V, hV, hKV, hVO.trans hOW, hinjV, fun x hx => (hVO hx).2⟩

/-- Globally smooth form of the previous lemma. -/
theorem ManifoldImmersion.exists_open_injOn_near_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E} (hK : IsCompact K)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Set.InjOn f V := by
  apply hinj.exists_isOpen_superset hK (fun _ _ => hf.continuous.continuousAt)
  intro x hx
  obtain ⟨V, hV, hxV, hinjV⟩ := exists_open_injOn_of_injective_nativeDerivative hf (hi x hx)
  exact ⟨V, hV.mem_nhds hxV, hinjV⟩

/-- The set of pairs of distinct points of `K` with the same image. -/
def ManifoldImmersion.doublePoints {X N : Type*} (f : X → N) (K : Set X) : Set (X × X) :=
  {q | q.1 ∈ K ∧ q.2 ∈ K ∧ q.1 ≠ q.2 ∧ f q.1 = f q.2}

/-- For a locally injective continuous map, the double-point set over a compact set is compact. -/
theorem ManifoldImmersion.isCompact_doublePoints_of_locally_injective {X N : Type*}
    [TopologicalSpace X] [TopologicalSpace N] [T2Space N] {f : X → N} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    IsCompact (doublePoints f K) := by
  classical
  choose U hU hmem hinj using (fun x : K => hlocal x x.property)
  let V : Set (X × X) := ⋃ x : K, (U x) ×ˢ (U x)
  have hV : IsOpen V := isOpen_iUnion (fun x => (hU x).prod (hU x))
  have hclosed : IsClosed {q : X × X | f q.1 = f q.2} :=
    isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)
  have heq : doublePoints f K = ((K ×ˢ K) ∩ {q : X × X | f q.1 = f q.2}) ∩ Vᶜ := by
    ext q
    constructor
    · rintro ⟨hx, hy, hne, hcoll⟩
      refine ⟨⟨⟨hx, hy⟩, hcoll⟩, ?_⟩
      intro hv
      obtain ⟨x, hxU, hyU⟩ := Set.mem_iUnion.mp hv
      exact hne (hinj x hxU hyU hcoll)
    · rintro ⟨⟨⟨hx, hy⟩, hcoll⟩, hv⟩
      refine ⟨hx, hy, ?_, hcoll⟩
      intro hxy
      apply hv
      apply Set.mem_iUnion.mpr
      refine ⟨⟨q.1, hx⟩, hmem ⟨q.1, hx⟩, ?_⟩
      rw [← hxy]
      exact hmem ⟨q.1, hx⟩
  rw [heq]
  exact ((hK.prod hK).inter_right hclosed).inter_right hV.isClosed_compl

/-- For an immersion, the double-point set over a compact set is compact. -/
theorem ManifoldImmersion.isCompact_doublePoints_of_injective_nativeDerivative
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    IsCompact (doublePoints f K) :=
  isCompact_doublePoints_of_locally_injective hf.continuous hK
    (fun _ hx => exists_open_injOn_of_injective_nativeDerivative hf (hinj _ hx))


/-- Precomposition with a linear isomorphism does not change whether a map is an immersion at a
point. -/
theorem ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff {E E' G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (e : E' ≃L[ℝ] E) {f : E → N} {x : E'}
    (hf : MDifferentiableAt 𝓘(ℝ, E) J f (e x)) :
    Function.Injective (mfderiv 𝓘(ℝ, E') J (f ∘ e) x) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J f (e x)) := by
  have he : mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) e x = e.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact e.toContinuousLinearMap.fderiv
  have hesmooth : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ e := e.contDiff.contMDiff
  rw [mfderiv_comp x hf (hesmooth.mdifferentiableAt (by simp)), he]
  constructor
  · intro h v w hvw
    apply e.symm.injective
    apply h
    change (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm v)) = (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm w))
    exact
      (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (v : E))).trans
        (hvw.trans (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (w : E))).symm)
  · exact fun h => h.comp e.injective
