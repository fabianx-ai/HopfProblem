/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Transversality.Basic

/-!
# Homogeneity of manifolds: moving points by supported diffeomorphisms

Let `M` be a boundaryless manifold modelled on a finite-dimensional space and `U ⊆ M` open. Two
points of a preconnected subset of `U`, or the two ends of a path in `U`, are exchanged by a
diffeomorphism of `M` which is the identity outside `U` and isotopic to the identity
(`MorseCancellation.exists_isotopic_pointMoving_of_preconnected`,
`MorseCancellation.exists_isotopic_pointMoving_of_path`; without the isotopy,
`SupportedDiffeomorph.exists_pointMoving_of_preconnected`, `SupportedDiffeomorph.exists_pointMoving_of_path`).
The proof is the clopen-orbit argument: the orbit `MorseCancellation.isotopicPointOrbit J U x` of a
point is open and its complement in `U` is open (`isOpen_isotopicPointOrbit`,
`isOpen_sdiff_isotopicPointOrbit`), starting from the local statement
`MorseCancellation.exists_open_isotopic_pointMoving` read in a chart.

Consequences: two distinct points can be pushed simultaneously into a dense set
(`MorseCancellation.exists_isotopic_two_points_in_dense`); a path in a manifold of dimension at
least `2` between points off a finite set can be replaced by a smooth path avoiding that set
(`exists_smooth_path_avoiding_finite`), so a diffeomorphism fixing the finite set pointwise carries one
end to the other (`exists_pointMoving_fixing_finite`). `exists_smooth_connecting_curve` replaces a
continuous path by a smooth curve `ℝ → N`, reparametrised by `CurveImmersion.smoothTime`.

## References

* Milnor, *Topology from the differentiable viewpoint*, §4, Homogeneity Lemma.
* cf. Hirsch, *Differential Topology*, Ch. 8 (isotopy).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- Homogeneity of a manifold, local form: every point `x` of an open set `U` has a neighbourhood `V
⊆ U` such that any `y ∈ V` is the image of `x` under a diffeomorphism isotopic to the identity
and supported in `U`. -/
theorem MorseCancellation.exists_open_isotopic_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧
          V ⊆ U ∧
            ∀ y ∈ V,
              ∃ d : Diffeomorph J J M M ∞,
                SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := modelChartPartialDiffeomorph (I := J) x
  let Φ := PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := SupportedDiffeomorph.exists_supported_pointMoving Φ hxΦ
  refine
    ⟨Φ '' Metric.ball (c x) ε,
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ⟨A, hA, hzero, hd, hdiff⟩, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

/-- Two distinct points can be pushed simultaneously into any dense set by a diffeomorphism isotopic
to the identity. -/
theorem MorseCancellation.exists_isotopic_two_points_in_dense {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {B : Set M} (hB : Dense B) {x y : M} (hxy : x ≠ y) :
    ∃ d : Diffeomorph J J M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧ d x ∈ B ∧ d y ∈ B := by
  obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation hxy
  obtain ⟨U', hU', hx', hU'U, hmoveU⟩ := exists_open_isotopic_pointMoving (J := J) hU hx
  obtain ⟨V', hV', hy', hV'V, hmoveV⟩ := exists_open_isotopic_pointMoving (J := J) hV hy
  obtain ⟨x', hx'B, hx'U⟩ := hB.exists_mem_open hU' ⟨x, hx'⟩
  obtain ⟨y', hy'B, hy'V⟩ := hB.exists_mem_open hV' ⟨y, hy'⟩
  obtain ⟨d, hd, hdx, hdfix⟩ := hmoveU x' hx'U
  obtain ⟨e, he, hey, hefix⟩ := hmoveV y' hy'V
  have hyU : y ∉ U := fun h => Set.disjoint_left.mp hdisj h hy
  have hxV : x' ∉ V := fun h => Set.disjoint_left.mp hdisj (hU'U hx'U) h
  refine ⟨d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) ∈ B
    rw [hdx, hefix x' hxV]
    exact hx'B
  · change e (d y) ∈ B
    rw [hdfix y hyU, hey]
    exact hy'B

/-- A point and its image under a diffeomorphism isotopic to the identity are joined by a path. -/
theorem MorseCancellation.isotopicToIdentity_joined {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {d : Diffeomorph J J M M ∞} (hd : SupportedDiffeomorph.IsotopicToIdentity d) (x : M) :
    Joined x (d x) := by
  obtain ⟨A, hA, hzero, hone, -⟩ := hd
  exact
    ⟨{  toFun := fun t => A ((t : ℝ), x)
        continuous_toFun := hA.continuous.comp (continuous_subtype_val.prodMk continuous_const)
        source' := hzero x
        target' := hone x }⟩

/-- The set of points reachable from `x` by a diffeomorphism isotopic to the identity and supported
in `U`. -/
def MorseCancellation.isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (J : ModelWithCorners ℝ E H)
    (U : Set M) (x : M) : Set M :=
  {y |
    y ∈ U ∧
      ∃ d : Diffeomorph J J M M ∞,
        SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z}

/-- The orbit of `x` under isotopies supported in an open set is open. -/
theorem MorseCancellation.isOpen_isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdx, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) = z
    rw [hdx, hey]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

/-- The complement of the orbit of `x` inside `U` is open; with the previous lemma this makes the
orbit relatively clopen in `U`. -/
theorem MorseCancellation.isOpen_sdiff_isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (U \ isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdx, hdfix⟩
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, hd.trans he.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hdx, ← hey, e.symm_apply_apply]
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact SupportedDiffeomorph.inverse_fixed_outside e.toEquiv hefix w hw

/-- Homogeneity of a manifold: any two points of a preconnected subset of an open set `U` are
exchanged by a diffeomorphism isotopic to the identity and supported in `U`. -/
theorem MorseCancellation.exists_isotopic_pointMoving_of_preconnected {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U A : Set M} (hU : IsOpen U) (hA : IsPreconnected A)
    (hAU : A ⊆ U) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ d : Diffeomorph J J M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ isotopicPointOrbit J U x :=
    ⟨hAU hx, Diffeomorph.refl J M ∞, SupportedDiffeomorph.isotopicToIdentity_refl, rfl,
      fun _ _ => rfl⟩
  have hcover : A ⊆ isotopicPointOrbit J U x ∪ (U \ isotopicPointOrbit J U x) := by
    intro z hz
    by_cases hh : z ∈ isotopicPointOrbit J U x
    · exact Or.inl hh
    · exact Or.inr ⟨hAU hz, hh⟩
  have hdisjoint : Disjoint (isotopicPointOrbit J U x) (U \ isotopicPointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub :=
    hA.subset_left_of_subset_union (isOpen_isotopicPointOrbit hU x)
      (isOpen_sdiff_isotopicPointOrbit hU x) hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

/-- Path form of homogeneity: if `x` and `y` are joined by a path inside `U`, some diffeomorphism
isotopic to the identity and supported in `U` carries `x` to `y`. -/
theorem MorseCancellation.exists_isotopic_pointMoving_of_path {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x y : M} (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    ∃ d : Diffeomorph J J M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  apply
    exists_isotopic_pointMoving_of_preconnected (J := J) hU
      (isConnected_range γ.continuous).isPreconnected
      (show Set.range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

/-- A smooth surjection `ℝ → [0, 1]` that is flat at the two ends, used to reparametrise a path
smoothly. -/
def CurveImmersion.smoothTime (t : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (Real.smoothTransition t)

/-- `smoothTime` is smooth as a map into the unit interval with boundary. -/
theorem CurveImmersion.contMDiff_smoothTime : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ smoothTime := by
  let : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have ht : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  apply contMDiffOn_univ.mp
  exact
    hp.comp ht.contMDiff.contMDiffOn
      (fun t _ => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)

/-- `smoothTime` sends `0` to `0`. -/
theorem CurveImmersion.smoothTime_zero : smoothTime 0 = 0 := by
  apply Subtype.ext
  simp [smoothTime]

/-- `smoothTime` sends `1` to `1`. -/
theorem CurveImmersion.smoothTime_one : smoothTime 1 = 1 := by
  apply Subtype.ext
  simp [smoothTime]

/-- Two points joined by a continuous path in a manifold are joined by a smooth curve `ℝ → N`. -/
theorem exists_smooth_connecting_curve {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {x y : N} (γ : Path x y) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ f 0 = x ∧ f 1 = y := by
  let Z := EuclideanSpace ℝ (Fin 0)
  let f₀ : C(Z, N) := ContinuousMap.const Z x
  let f₁ : C(Z, N) := ContinuousMap.const Z y
  let H : f₀.Homotopy f₁ :=
    { toFun := fun q => γ q.1
      continuous_toFun := γ.continuous.comp continuous_fst
      map_zero_left := fun _ => γ.source
      map_one_left := fun _ => γ.target }
  obtain ⟨H', hH', -, -⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars (I := 𝓘(ℝ, Z)) (J := J) contMDiff_const
      contMDiff_const H
  let f : ℝ → N := fun t => H' (CurveImmersion.smoothTime t, (0 : Z))
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f :=
    hH'.comp (CurveImmersion.contMDiff_smoothTime.prodMk contMDiff_const)
  refine ⟨⟨f, hf.continuous⟩, hf, ?_, ?_⟩
  · change H' (CurveImmersion.smoothTime 0, (0 : Z)) = x
    rw [CurveImmersion.smoothTime_zero, H'.apply_zero]
    rfl
  · change H' (CurveImmersion.smoothTime 1, (0 : Z)) = y
    rw [CurveImmersion.smoothTime_one, H'.apply_one]
    rfl

/-- The set of points reachable from `x` by a diffeomorphism that is the identity outside `U`. -/
def SupportedDiffeomorph.pointOrbit {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (J : ModelWithCorners ℝ E H)
    (U : Set M) (x : M) : Set M :=
  {y | y ∈ U ∧ ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z}

/-- The orbit of `x` under diffeomorphisms supported in an open set is open. -/
theorem SupportedDiffeomorph.isOpen_pointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, ?_, ?_⟩
  · change e (d x) = z
    rw [hd, he]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

/-- The complement of that orbit inside `U` is open. -/
theorem SupportedDiffeomorph.isOpen_sdiff_pointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (U \ pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdfix⟩
  obtain ⟨e, he, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hd, ← he]
    exact e.toEquiv.symm_apply_apply y
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact inverse_fixed_outside e.toEquiv hefix w hw

/-- Any two points of a preconnected subset of an open set `U` are exchanged by a diffeomorphism
that is the identity outside `U`. -/
theorem SupportedDiffeomorph.exists_pointMoving_of_preconnected {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U S : Set M} (hU : IsOpen U) (hS : IsPreconnected S)
    (hSU : S ⊆ U) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ pointOrbit J U x := ⟨hSU hx, Diffeomorph.refl J M ∞, rfl, fun _ _ => rfl⟩
  have hcover : S ⊆ pointOrbit J U x ∪ (U \ pointOrbit J U x) := by
    intro z hz
    by_cases h : z ∈ pointOrbit J U x
    · exact Or.inl h
    · exact Or.inr ⟨hSU hz, h⟩
  have hdisjoint : Disjoint (pointOrbit J U x) (U \ pointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub :=
    hS.subset_left_of_subset_union (isOpen_pointOrbit hU x) (isOpen_sdiff_pointOrbit hU x)
      hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

/-- Path form: if `x` and `y` are joined by a path inside `U`, some diffeomorphism that is the
identity outside `U` carries `x` to `y`. -/
theorem SupportedDiffeomorph.exists_pointMoving_of_path {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U : Set M} (hU : IsOpen U) {x y : M} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ U) : ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  apply
    exists_pointMoving_of_preconnected (J := J) hU (isConnected_range γ.continuous).isPreconnected
      (show Set.range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

/-- In a manifold of dimension at least `2`, a path between two points off a finite set can be
replaced by a smooth path avoiding that finite set. -/
theorem exists_smooth_path_avoiding_finite {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {x y : N} (γ : Path x y) (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) : ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : Set.range g = S := by ext z; simp [g]
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ Set.range g := by
    intro t ht
    rw [hrange]
    rcases ht with rfl | ht
    · change f 0 ∉ S
      rw [hf0]
      exact hx
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ S
      rw [hf1]
      exact hy
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel fI g hfI hg hdim'
      ((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have hf'0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have hf'1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := hf'0, target' := hf'1 }
  refine ⟨η, hf', ?_⟩
  intro t ht
  rw [hrange] at hdisjoint
  exact Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht

/-- In dimension at least `2`, if `x` and `y` are joined by a path and both lie off a finite set
`S`, a diffeomorphism fixing `S` pointwise carries `x` to `y`. -/
theorem exists_pointMoving_fixing_finite {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {x y : N} (γ : Path x y) (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) : ∃ d : Diffeomorph J J N N ∞, d x = y ∧ ∀ z ∈ S, d z = z := by
  obtain ⟨η, _, hη⟩ := exists_smooth_path_avoiding_finite (J := J) γ hdim hS hx hy
  obtain ⟨d, hd, hfix⟩ :=
    SupportedDiffeomorph.exists_pointMoving_of_path (J := J) hS.isClosed.isOpen_compl η hη
  exact ⟨d, hd, fun z hz => hfix z (fun hn => hn hz)⟩
