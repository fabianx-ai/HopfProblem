/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Immersion.Relative.PointMoving
public import Lib.Geometry.Manifold.Immersion.Relative.Curve

/-!
# Embedded arcs with prescribed endpoint germs

Two smooth curves `a b : ℝ → N` whose endpoints `a 0` and `b 1` are joined by a path are the two
ends of a single smooth curve agreeing with `a` near `(-∞, 0]` and with `b` near `[1, ∞)`
(`CurveImmersion.exists_continuous_curve_with_endpoint_germs`, `exists_smooth_curve_with_endpoint_germs`).
When `dim N ≥ 3` and the two curves are immersions at their endpoints, the curve embedding theorem
of `Lib.Geometry.Manifold.Immersion.Relative.Curve` makes this curve an embedding and an immersion
on `[0, 1]`, off a given finite set away from its endpoints (`exists_embedded_arc_with_endpoint_germs`;
`exists_embedded_arc_with_local_endpoint_germs` for germs defined only near the endpoints), or off
the closed image of a map `o : Y → N` with `1 + dim Y < dim N`
(`MorseCancellation.exists_clean_arc_with_local_endpoint_germs`).

Supporting statements: a path between two points off the closed image of `g : Y → N`, with
`1 + dim Y < dim N`, can be replaced by a smooth path avoiding that image
(`MorseCancellation.exists_smooth_path_avoiding_closed_image`, also inside an open subset); a
continuous map which is smooth off a compact set and near a closed set `C` is homotopic rel `C` to a
smooth map (`ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact`); a curve
smooth near a parameter is the germ of a global smooth curve (`exists_smooth_curve_with_germ_at`);
and the same germ-joining statements for curves in an open subset of a normed space
(`exists_smooth_open_curve_with_germ`, `exists_smooth_open_curve_with_endpoint_germs`).

## References

* Hirsch, *Differential Topology*, Ch. 3 §2 (general position of arcs).
* Milnor, *Lectures on the h-cobordism theorem*, §6 (the arcs of the Whitney trick).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- A path between two points off the closed image of `g` can be replaced by a smooth path avoiding
that image, provided `1 + dim Y < dim N`. -/
theorem MorseCancellation.exists_smooth_path_avoiding_closed_image {E G H H' N Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] {x y : N}
    (γ : Path x y) (g : C(Y, N)) (hg : ContMDiff I J ∞ g) (hclosed : IsClosed (Set.range g))
    (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G) (hx : x ∉ Set.range g)
    (hy : y ∉ Set.range g) : ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ Set.range g := by
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ Set.range g := by
    intro t ht
    rcases ht with rfl | ht
    · change f 0 ∉ Set.range g
      rwa [hf0]
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ Set.range g
      rwa [hf1]
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range fI g hfI hg
      hclosed hdim' ((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have h0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have h1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := h0, target' := h1 }
  exact ⟨η, hf', fun t ht => Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht⟩

/-- The same statement inside an open subset `U` of the ambient manifold. -/
theorem MorseCancellation.exists_smooth_path_avoiding_closed_image_in_open {E G H H' N Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
    (U : TopologicalSpace.Opens N) {x y : U} (γ : Path x y) (g : C(Y, N)) (hg : ContMDiff I J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hx : x.val ∉ Set.range g) (hy : y.val ∉ Set.range g) :
    ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, (η t).val ∉ Set.range g := by
  obtain ⟨η, hη, havoid⟩ :=
    exists_smooth_path_avoiding_closed_image γ (OpenObstacle.restrict g U)
      (OpenObstacle.contMDiff_restrict g U hg)
      (OpenObstacle.isClosed_range_restrict g U hclosed) hdim
      (fun h => hx ((OpenObstacle.mem_range_restrict_iff g U x).mp h))
      (fun h => hy ((OpenObstacle.mem_range_restrict_iff g U y).mp h))
  exact
    ⟨η, hη, fun t ht => havoid t ((OpenObstacle.mem_range_restrict_iff g U (η t)).mpr ht)⟩

/-- A continuous map which is smooth off a compact set and smooth near a closed set `C` is homotopic
rel `C`, within a prescribed open target, to a globally smooth map. -/
theorem ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target
    {E G H H' X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] (f : C(X, N)) {K C U : Set X}
    (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) {D : Set X} {O : Set N}
    (hO : IsOpen O) (hKO : Set.MapsTo f K O) (hmaps : Set.MapsTo f D O) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ HomotopicRelWithin f f' C D O := by
  classical
  have hp (x : K) :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f (x : X) hO (hKO x.property)
  choose p hcompatible hplateau hsource using hp
  have hcover : K ⊆ ⋃ x : K, (p x).plateau := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hplateau ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hK.elim_finite_subcover (fun x : K => (p x).plateau) (fun _ => isOpen_interior) hcover
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing_within_target (fun i : s => p i.1) f (fun i => hcompatible i.1)
      hC hU hCU hfU (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  apply hsm x
  by_cases hx : x ∈ K
  · obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Or.inr ⟨⟨i, his⟩, Finset.mem_univ _, hxi⟩
  · exact Or.inl ((hfK x hx).contMDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))

/-- The same smoothing statement with an ordinary relative homotopy. -/
theorem ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact
    {E G H H' X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] (f : C(X, N)) {K C U : Set X}
    (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  obtain ⟨f', hf', hrel⟩ :=
    exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target f hK hC hU hCU hfU hfK
      isOpen_univ (Set.mapsTo_univ f K) (Set.mapsTo_univ f Set.univ)
  exact ⟨f', hf', hrel.homotopicRel⟩

/-- Two curves whose endpoints are joined by a path are the two ends of a single continuous curve `ℝ
→ N`, agreeing with the first on `(-∞, 1/4]` and with the second on `[3/4, ∞)`. -/
theorem CurveImmersion.exists_continuous_curve_with_endpoint_germs {N : Type*}
    [TopologicalSpace N] (a b : C(ℝ, N)) (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), Set.EqOn f a (Set.Iic (1 / 4 : ℝ)) ∧ Set.EqOn f b (Set.Ici (3 / 4 : ℝ)) := by
  classical
  let α : Path (a (1 / 4)) (a 0) :=
    Path.ofLine (f := fun t : ℝ => a ((1 - t) / 4))
      ((a.continuous.comp ((continuous_const.sub continuous_id).div_const 4)).continuousOn)
      (by norm_num) (by norm_num)
  let β : Path (b 1) (b (3 / 4)) :=
    Path.ofLine (f := fun t : ℝ => b (1 - t / 4))
      ((b.continuous.comp (continuous_const.sub (continuous_id.div_const 4))).continuousOn)
      (by norm_num) (by norm_num)
  let η := α.trans (γ.trans β)
  let mid : ℝ → N := fun t => η.extend (2 * t - 1 / 2)
  have hmid : Continuous mid :=
    η.continuous_extend.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hm₀ : mid (1 / 4) = a (1 / 4) := by
    change η.extend (2 * (1 / 4) - 1 / 2) = _
    norm_num
  have hm₁ : mid (3 / 4) = b (3 / 4) := by
    change η.extend (2 * (3 / 4) - 1 / 2) = _
    norm_num
  let right : ℝ → N := fun t => if t ≤ 3 / 4 then mid t else b t
  have hr : Continuous right :=
    hmid.if_le b.continuous continuous_id continuous_const (fun t ht => ht ▸ hm₁)
  let f : ℝ → N := fun t => if t ≤ 1 / 4 then a t else right t
  have hf : Continuous f :=
    a.continuous.if_le hr continuous_id continuous_const
      (by
        intro t ht
        subst t
        simpa only [right, if_pos (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)] using hm₀.symm)
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro t ht
    exact if_pos ht
  · intro t ht
    change 3 / 4 ≤ t at ht
    change (if t ≤ 1 / 4 then a t else if t ≤ 3 / 4 then mid t else b t) = b t
    rw [if_neg (show ¬t ≤ 1 / 4 by linarith)]
    by_cases hte : t = 3 / 4
    · subst t
      simpa only [if_pos le_rfl] using hm₁
    · exact if_neg (by intro h; exact hte (le_antisymm h ht))

/-- Smooth form of the previous statement: two smooth curves whose endpoints are joined by a path
are the two ends of a single smooth curve, agreeing with them on `(-∞, 1/8]` and `[7/8, ∞)`. -/
theorem exists_smooth_curve_with_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b) (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        Set.EqOn f a (Set.Iic (1 / 8 : ℝ)) ∧ Set.EqOn f b (Set.Ici (7 / 8 : ℝ)) := by
  obtain ⟨g, hgleft, hgright⟩ := CurveImmersion.exists_continuous_curve_with_endpoint_germs a b γ
  let K := Set.Icc (1 / 4 : ℝ) (3 / 4)
  let U := Set.Iio (1 / 4 : ℝ) ∪ Set.Ioi (3 / 4)
  let C := Set.Iic (1 / 8 : ℝ) ∪ Set.Ici (7 / 8)
  have hU : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have hC : IsClosed C := isClosed_Iic.union isClosed_Ici
  have hCU : C ⊆ U := by
    intro t ht
    rcases ht with ht | ht
    · change t ≤ 1 / 8 at ht
      exact Or.inl (show t < 1 / 4 by linarith)
    · change 7 / 8 ≤ t at ht
      exact Or.inr (show 3 / 4 < t by linarith)
  have hgU : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ g U := by
    intro t ht
    apply ContMDiffAt.contMDiffWithinAt
    rcases ht with ht | ht
    · have heq : g =ᶠ[𝓝 t] a := by
        filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Set.Iio (1 / 4 : ℝ) from ht)] with s hs
        exact hgleft (show s ≤ 1 / 4 from hs.le)
      exact ha.contMDiffAt.congr_of_eventuallyEq heq
    · have heq : g =ᶠ[𝓝 t] b := by
        filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (3 / 4 : ℝ) from ht)] with s hs
        exact hgright (show 3 / 4 ≤ s from hs.le)
      exact hb.contMDiffAt.congr_of_eventuallyEq heq
  have hKU : Kᶜ ⊆ U := by
    intro t ht
    change ¬(1 / 4 ≤ t ∧ t ≤ 3 / 4) at ht
    change t < 1 / 4 ∨ 3 / 4 < t
    exact not_and_or.mp ht |>.imp lt_of_not_ge lt_of_not_ge
  obtain ⟨f, hf, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact g
      CompactIccSpace.isCompact_Icc hC hU hCU hgU (hgU.mono hKU)
  refine ⟨f, hf, ?_, ?_⟩
  · intro t ht
    change t ≤ 1 / 8 at ht
    exact
      (hrel.fst_eq_snd (Or.inl ht)).symm.trans
        (hgleft (show t ∈ Set.Iic (1 / 4 : ℝ) from by change t ≤ 1 / 4; linarith))
  · intro t ht
    change 7 / 8 ≤ t at ht
    exact
      (hrel.fst_eq_snd (Or.inr ht)).symm.trans
        (hgright (show t ∈ Set.Ici (3 / 4 : ℝ) from by change 3 / 4 ≤ t; linarith))

/-- A curve that is an immersion at its two endpoints and has distinct endpoints is injective and
immersive on a compact neighbourhood of `{0, 1}`, on which it meets a given finite set only at
the endpoints. -/
theorem ManifoldImmersion.exists_clean_curve_endpoint_neighborhood {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : ℝ → N} (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hxy : f 0 ≠ f 1)
    (hi0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f 0))
    (hi1 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f 1)) {S : Set N} (hS : S.Finite) :
    ∃ C : Set ℝ,
      IsCompact C ∧
        {(0 : ℝ), 1} ⊆ interior C ∧
          Set.InjOn f C ∧
            (∀ t ∈ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
              (∀ t ∈ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ S) := by
  let B : Set ℝ := {0, 1}
  have hB : IsCompact B := ((Set.finite_singleton (1 : ℝ)).insert 0).isCompact
  have h0B : (0 : ℝ) ∈ B := by simp [B]
  have h1B : (1 : ℝ) ∈ B := by simp [B]
  have hinjB : Set.InjOn f B := by
    intro s hs t ht heq
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact (hxy heq).elim
    · exact (hxy heq.symm).elim
    · rfl
  have hiB : ∀ t ∈ B, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t) := by
    intro t ht
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hi0
    · exact hi1
  obtain ⟨V, hV, hBV, hinjV⟩ := exists_open_injOn_near_compact hf hB hinjB hiB
  let R := S \ {f 0, f 1}
  have hR : IsClosed R := (hS.subset Set.sdiff_subset).isClosed
  let U := (V ∩ {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}) ∩ f ⁻¹' Rᶜ
  have hU : IsOpen U :=
    (hV.inter (isOpen_injective_derivative hf)).inter (hR.isOpen_compl.preimage hf.continuous)
  have hBU : B ⊆ U := by
    intro t ht
    refine ⟨⟨hBV ht, hiB t ht⟩, ?_⟩
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> simp [R]
  obtain ⟨C, hC, hBC, hCU⟩ := exists_compact_between hB hU hBU
  refine ⟨C, hC, hBC, hinjV.mono (fun t ht => (hCU ht).1.1), fun t ht => (hCU ht).1.2, ?_⟩
  intro t ht htB htS
  apply (hCU ht).2
  refine ⟨htS, ?_⟩
  intro hends
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  rcases hends with h0 | h1
  · have ht0 : t = 0 := hinjV (hCU ht).1.1 (hBV h0B) h0
    exact htB (by simp [ht0])
  · have ht1 : t = 1 := hinjV (hCU ht).1.1 (hBV h1B) h1
    exact htB (by simp [ht1])


/-- Two smooth curves which are immersions at their matching endpoints and have distinct endpoints,
joined by a path, are the two ends of a single arc which is an embedding and an immersion on
`[0, 1]` and meets a given finite set only at its endpoints; it requires `dim N ≥ 3`. -/
theorem exists_embedded_arc_with_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (a b : C(ℝ, N)) (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨g, hg, hga, hgb⟩ := exists_smooth_curve_with_endpoint_germs a b ha hb γ
  have hga0 : g =ᶠ[𝓝 (0 : ℝ)] a := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)] with t ht
    change t < 1 / 8 at ht
    exact hga ht.le
  have hgb1 : g =ᶠ[𝓝 (1 : ℝ)] b := by
    filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num)] with t ht
    change 7 / 8 < t at ht
    exact hgb ht.le
  have hgxy : g 0 ≠ g 1 := by
    rw [hga0.eq_of_nhds, hgb1.eq_of_nhds]
    exact hxy
  have hig0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := by
    rw [hga0.mfderiv_eq]
    exact hia
  have hig1 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 1) := by
    rw [hgb1.mfderiv_eq]
    exact hib
  obtain ⟨C, hC, hBC, hinjC, hiC, hclean⟩ :=
    ManifoldImmersion.exists_clean_curve_endpoint_neighborhood hg hgxy hig0 hig1 hS
  obtain ⟨f, hf, hrel, hemb, hi, havoid⟩ :=
    ManifoldImmersion.exists_relative_curve_avoiding_finite g hg hdim hS
      (CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := 1)) hC.isClosed hBC
      (hinjC.mono Set.inter_subset_right) (fun t ht => hiC t ht.2) (fun t ht => hclean t ht.2)
  have hfg (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) : f =ᶠ[𝓝 t] g := by
    filter_upwards [isOpen_interior.mem_nhds (hBC ht)] with s hs
    exact (hrel.fst_eq_snd (interior_subset hs)).symm
  refine ⟨f, hf, (hfg 0 (by simp)).trans hga0, (hfg 1 (by simp)).trans hgb1, hemb, hi, ?_⟩
  intro t ht
  apply havoid t ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  intro htB
  rcases htB with ht0 | ht1
  · exact ht.1.ne' ht0
  · exact ht.2.ne ht1

/-- A curve defined and smooth near a parameter is the germ at that parameter of a globally defined
smooth curve. -/
theorem exists_smooth_curve_with_germ_at {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ} (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U)
    (hU : IsOpen U) (ht₀ : t₀ ∈ U) : ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ (f =ᶠ[𝓝 t₀] a) := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_extension_near_point ha hU ht₀
  exact ⟨⟨f, hf.continuous⟩, hf, heq⟩

/-- Version of `exists_embedded_arc_with_endpoint_germs` for curve germs defined only near the two
endpoints. -/
theorem exists_embedded_arc_with_local_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {a b : ℝ → N} {U V : Set ℝ} (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U)
    (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V) (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U)
    (h1V : (1 : ℝ) ∈ V) (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_curve_with_germ_at ha hU h0U
  obtain ⟨b', hb', heqb⟩ := exists_smooth_curve_with_germ_at hb hV h1V
  have hia' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    rw [heqa.mfderiv_eq]
    exact hia
  have hib' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    rw [heqb.mfderiv_eq]
    exact hib
  have hxy' : a' 0 ≠ b' 1 := by
    rw [heqa.eq_of_nhds, heqb.eq_of_nhds]
    exact hxy
  obtain ⟨f, hf, hfa, hfb, hemb, hi, havoid⟩ :=
    exists_embedded_arc_with_endpoint_germs a' b' ha' hb' hia' hib'
      (γ.cast heqa.eq_of_nhds heqb.eq_of_nhds) hxy' hdim hS
  exact ⟨f, hf, hfa.trans heqa, hfb.trans heqb, hemb, hi, havoid⟩

/-- Version of the previous statement in which the arc is required in addition to avoid the closed
image of a map `o` except at its endpoints; it requires `dim N ≥ 3` and `1 + dim Y < dim N`. -/
theorem MorseCancellation.exists_clean_arc_with_local_endpoint_germs {G V H H' N Y : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I : ModelWithCorners ℝ V H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I ∞ Y] [SecondCountableTopology Y] {a b : ℝ → N} {U W : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b W) (hU : IsOpen U)
    (hW : IsOpen W) (h0U : (0 : ℝ) ∈ U) (h1W : (1 : ℝ) ∈ W)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) (o : C(Y, N)) (ho : ContMDiff I J ∞ o)
    (hclosed : IsClosed (Set.range o)) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ Set.range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∈ Set.range o → t = 1) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ Set.range o := by
  obtain ⟨f, hf, hfa, hfb, hemb, hfd, -⟩ :=
    exists_embedded_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib γ hxy hdim
      (S := ∅) Set.finite_empty
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Set.range o → t = 0 := by
    filter_upwards [hfa, hclean0] with t he hc
    rw [he]
    exact hc
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ Set.range o → t = 1 := by
    filter_upwards [hfb, hclean1] with t he hc
    rw [he]
    exact hc
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := Metric.closedBall 0 r ∪ Metric.closedBall 1 s
  have h0C : C ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr)
      (fun _ ht => Or.inl (Metric.ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 1 hs)
      (fun _ ht => Or.inr (Metric.ball_subset_closedBall ht))
  have hBC : ({0, 1} : Set ℝ) ⊆ interior C := by
    intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  have hclean : ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ Set.range o := by
    intro t ht htB hto
    rcases ht.2 with ht0 | ht1
    · exact htB (Or.inl (hball0 ht0 hto))
    · exact htB (Or.inr (hball1 ht1 hto))
  have hfi : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ V < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobdim
  obtain ⟨g, hg, hrel, hge, hgd, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f o
      hf ho hclosed hself hobs CompactIccSpace.isCompact_Icc
      (show IsClosed C from Metric.isClosed_closedBall.union Metric.isClosed_closedBall) hBC hfi
      hfd hclean
  refine ⟨g, hg, ?_, ?_, hge, hgd, ?_⟩
  · filter_upwards [h0C, hfa] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · filter_upwards [h1C, hfb] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · intro t ht hto
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ hto


/-- A curve in an open subset of a normed space, smooth near a parameter, is the germ there of a
globally defined smooth curve staying in that open set. -/
theorem exists_smooth_open_curve_with_germ {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : TopologicalSpace.Opens B) {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ f : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dif_pos hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt := (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, heq⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

/-- Two curve germs in an open subset of a normed space, joined by a path in that open set, are the
two ends of a single smooth curve staying in it. -/
theorem exists_smooth_open_curve_with_endpoint_germs {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : TopologicalSpace.Opens B) {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S)) :
    ∃ f : ℝ → B, ContDiff ℝ ∞ f ∧ (∀ t, f t ∈ S) ∧ (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  obtain ⟨f, hf, hfa, hfb⟩ :=
    exists_smooth_curve_with_endpoint_germs a' b' ha' hb' (γ.cast hstart hend)
  refine
    ⟨fun t => (f t : B), ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := S)).comp hf).contDiff,
      fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb
