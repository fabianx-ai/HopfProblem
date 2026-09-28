/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.OrderedCancellation.CircleParametrization

/-!
# Transport of embedded spheres between regular levels along the flow

The gradient-like flow of an `AdaptedWindows` package carries a compact embedded submanifold of a
regular level `f = a`, lying in the basin of a lower regular level `f = b`, to an embedded
submanifold of that level (`AdaptedWindows.exists_embedded_level_transport`, families:
`exists_native_family_level_transport`, `exists_regular_band_family_transport`); attaching
spheres are transported below their critical point (`exists_native_attaching_lower_cut`,
`exists_attaching_circle_lower_transport`).  For an index-`1` critical point whose two attaching
points lie in different path components a flow with two distinct minima at the ends of the
attaching arc is realised (`realize_one_handle_minimum_branches`), and the flow line from the
`1`-handle to the higher minimum is unique (`unique_connection_of_distinct_minimum_branches`).
Cf. Milnor, *Lectures on the h-cobordism theorem*, §4.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Let `S : AdaptedWindows E f`, `a`, `b` regular values, and `γ : X → {f = a}` a smooth injective
immersion whose image lies in the basin of the level `b`.  Then there is a partial diffeomorphism
`D : {f = a} → {f = b}` with source the basin of `b` and target the basin of `a`, and a smooth
injective immersion `Γ : X → {f = b}` with `D ∘ γ = Γ`, `D⁻¹ ∘ Γ = γ`, and each `Γ z` on the flow
line of `γ z`. -/
theorem AdaptedWindows.exists_embedded_level_transport {E M G H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold J ∞ X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (γ : C(X, { x : M // f x = a })) (x₀ : X) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f b) →
            ∃ D :
              PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                { x : M // f x = a } { x : M // f x = b } ∞,
              D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f b} ∧
                D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
                  ∃ Γ : C(X, { x : M // f x = b }),
                    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
                      Function.Injective Γ ∧
                        (∀ z,
                            Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
                          (∀ z, D (γ z) = Γ z) ∧
                            (∀ z, D.symm (Γ z) = γ z) ∧
                              ∀ z, ∃ t : ℝ, S.flow t (γ z).val = (Γ z).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  change
    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f b) → _
  intro hγ hγi hγd hreach
  obtain ⟨t, ht⟩ := hreach x₀
  let zb : { x : M // f x = b } := ⟨S.flow t (γ x₀).val, ht⟩
  obtain ⟨D, hsource, htarget, horbit⟩ := S.exists_native_level_basin_transport hf ha hb (γ x₀) zb
  have hmaps (z : X) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hDγ : ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hmaps z))).comp z hγ.contMDiffAt
  let Γ : C(X, { x : M // f x = b }) := ⟨D ∘ γ, hDγ.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro x y hxy
    exact hγi (D.toPartialEquiv.injOn (hmaps x) (hmaps y) hxy)
  have hΓd : ∀ z, Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hmaps z)) (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hmaps z)).1.comp (hγd z)
  refine ⟨D, hsource, htarget, Γ, hDγ, hΓi, hΓd, fun _ => rfl, ?_, ?_⟩
  · intro z
    exact D.left_inv' (hmaps z)
  · intro z
    exact horbit (γ z) (hmaps z)

/-- If `mfderiv γ (standardCircleParametrization z)` coproduct with `B` is surjective, so is the
differential of `γ ∘ standardCircleParametrization` at `z` coproduct with `B`. -/
theorem MorseCancellation.transverse_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {γ : Circle → N}
    (hγ : ContMDiff (𝓡 1) J ∞ γ) (B : D →L[ℝ] G) (z : Hemisphere.Sphere 1)
    (htrans :
      Function.Surjective
        ((mfderiv (𝓡 1) J γ (standardCircleParametrization z) :
              EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
          B)) :
    Function.Surjective
      ((mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
        B) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (standardCircleParametrization z)
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 1) (𝓡 1) standardCircleParametrization z
  have hP : Function.Surjective P :=
    (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).surjective
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  change Function.Surjective ((L.comp P).coprod B)
  exact ContinuousLinearMap.surjective_coprod_comp_left L B P hP htrans

attribute [local instance 100] Classical.propDecidable in
/-- Let `p` be a critical point of index `2` of `S : AdaptedWindows E f` and `a < f p` a regular
value with every critical value below `f p` below `a`.  Then there are a diffeomorphism
`e : S¹ ≃ S(N_p)`, a partial diffeomorphism `D` from the lower level of `p` to `{f = a}` between
the basins, and a smooth embedded circle `Γ : S¹ → {f = a}` with `D (attachingSphere (e z)) = Γ z`
and `Γ z` on the flow line of `attachingSphere (e z)`. -/
theorem AdaptedWindows.exists_attaching_circle_lower_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    let _ := RegularLevel.chartedSpace hf ha
    ∃ e :
      Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1)
        (Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞,
      ∃ D :
        PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).LowerLevel { y : M // f y = a } ∞,
        D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
          D.target =
              {y |
                y.val ∈
                  FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p)} ∧
            ∃ Γ : C(Hemisphere.Sphere 1, { y : M // f y = a }),
              ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
                Function.Injective Γ ∧
                  (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
                    (∀ z, D ((S.data p).surgery.attachingSphere (e z)) = Γ z) ∧
                      (∀ z, D.symm (Γ z) = (S.data p).surgery.attachingSphere (e z)) ∧
                        ∀ z,
                          ∃ t : ℝ,
                            S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val :=
  by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 1
  let γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf 1).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf 1).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf 1).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf 1 (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere 1) :
    (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  obtain ⟨D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ
      (MorseCancellation.standardCircleParametrization.symm (1 : Circle)) hγ hγi hγd hreach
  exact ⟨e, D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩

attribute [local instance 100] Classical.propDecidable in
/-- Let `q` be a critical point of index `1` of `S : AdaptedWindows E f` whose two core boundary
points `u`, `v` are not joined in the lower sublevel set.  Then there is a gradient-like field
`V` with flow `G`, agreeing with `S.field` near the critical points, and two distinct minima
`p`, `r` below the window of `q`, such that the backward basin of `q` in the lower level is the
attaching sphere, `attachingSphere u` flows to `p`, `attachingSphere v` flows to `r`, every
attaching point flows to `p` or `r`, and no flow line runs from `q` to another critical point. -/
theorem AdaptedWindows.realize_one_handle_minimum_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (p r :
      ManifoldMorse.criticalPoints E f),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                MorseCancellation.nativeMorseIndex E f p = 0 ∧
                  MorseCancellation.nativeMorseIndex E f r = 0 ∧
                    p ≠ r ∧
                      f p < S.toSurgeryWindows.lower q ∧
                        f r < S.toSurgeryWindows.lower q ∧
                          (∀ x : (S.data q).LowerLevel,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
                                x ∈ Set.range (S.data q).surgery.attachingSphere) ∧
                            Filter.Tendsto
                                (fun t => G t ((S.data q).surgery.attachingSphere u).val)
                                Filter.atTop (𝓝 p.val) ∧
                              Filter.Tendsto
                                  (fun t => G t ((S.data q).surgery.attachingSphere v).val)
                                  Filter.atTop (𝓝 r.val) ∧
                                (∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                                    Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 p.val) ∨
                                      Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 r.val)) ∧
                                  ∀ j : ManifoldMorse.criticalPoints E f,
                                    j ≠ q →
                                      j ≠ p →
                                        j ≠ r →
                                          ∀ x,
                                            ¬(Filter.Tendsto (fun t => G t x) Filter.atBot
                                                  (𝓝 q.val) ∧
                                                Filter.Tendsto (fun t => G t x) Filter.atTop
                                                  (𝓝 j.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, hall⟩ :=
    S.place_one_handle_in_distinct_minimum_basins hf q hone u v hnot
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, hρ, hρbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 p.val) ∨
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 r.val) :=
    (hall w).imp ((hforward _ p.val).mpr) ((hforward _ r.val).mpr)
  refine
    ⟨V, G, p, r, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hp, hr, hpr,
      hpq, hrq, hbq, (hforward _ p.val).mpr hpu, (hforward _ r.val).mpr hrv, hends, ?_⟩
  intro j hjq hjp hjr x hx
  have hmono :=
    FlowConstruction.antitone_flow_height hf G hG (fun y hy => (hzero y).mpr (S.zero y hy))
      hdesc x
  have hforwardHeight := hf.continuous.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuous.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f q :=
    (hmono.le_of_tendsto hforwardHeight 0).trans (hmono.ge_of_tendsto hbackwardHeight 0)
  have hjq' : f j < f q :=
    lt_of_le_of_ne hle (fun h => hjq (Subtype.ext (S.distinct j.property q.property h)))
  have hjlow : f j < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper j).trans (S.separated j q hjq')
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
      (S.toSurgeryWindows.lower_lt_value q) hjlow
  let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
  have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
  have hzj : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 j.val) :=
    (MorseCancellation.flow_time_atTop_limit_iff G t x j.val).mpr hx.2
  obtain ⟨w, hw⟩ := (hbq z).mp hzq
  have hh := hends w
  rw [hw] at hh
  rcases hh with hp' | hr'
  · exact hjp (Subtype.ext (tendsto_nhds_unique hzj hp'))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzj hr'))

/-- Family version of `exists_embedded_level_transport`: a family `α : ι → X → {f = a}` of smooth
injective immersions of a compact `X` with pairwise disjoint images in the basin of the level `b`
is transported along the flow to a family `β : ι → X → {f = b}` of smooth closed embeddings with
injective differential and pairwise disjoint images. -/
theorem AdaptedWindows.exists_native_family_level_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) (α : ι → X → { x : M // f x = a }) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            (∀ j x, (α j x).val ∈ FlowCancellation.levelBasin S.flow f b) →
              ∃ β : ι → X → { x : M // f x = b },
                (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
                  (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                    (∀ j x,
                        Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
                      Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  dsimp only
  intro hα hαinj hαimm hpair hreach
  obtain ⟨P, hsource, -, horbit⟩ := S.exists_native_level_basin_transport hf ha hb za zb
  have hsrc (j : ι) (x : X) : α j x ∈ P.source := by
    rw [hsource]
    exact hreach j x
  let β : ι → X → { x : M // f x = b } := fun j => P ∘ α j
  have hβ (j : ι) : ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j) := by
    intro x
    exact
      (P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))).comp x
        (hα j).contMDiffAt
  have hinj (j : ι) : Function.Injective (β j) := by
    intro x y hxy
    exact hαinj j (P.toPartialEquiv.injOn (hsrc j x) (hsrc j y) hxy)
  refine
    ⟨β, hβ, fun j => (hβ j).continuous.isClosedEmbedding (hinj j), ?_, ?_, fun j x =>
      horbit (α j x) (hsrc j x)⟩
  · intro j x
    have hP := P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))
    change Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (P ∘ α j) x)
    rw [mfderiv_comp x (hP.mdifferentiableAt (by simp)) ((hα j).mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv P (hsrc j x)).injective.comp (hαimm j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hiz hjz
    obtain ⟨x, hx⟩ := hiz
    obtain ⟨y, hy⟩ := hjz
    have heq : α i x = α j y := P.toPartialEquiv.injOn (hsrc i x) (hsrc j y) (hx.trans hy.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨y, heq.symm⟩

/-- Let `p` be a critical point of index `n + 1` of `S : AdaptedWindows E f` and `a < f p` a regular
value with every critical value below `f p` below `a`.  Then there is a smooth closed embedding
`Γ : Sⁿ → {f = a}` with injective differential, each `Γ z` on the flow line of the attaching
point `attachingSphere (standardParametrization z)`, whose image is exactly the backward basin
of `p` in the level `a`. -/
theorem AdaptedWindows.exists_native_attaching_lower_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ Γ : C(Hemisphere.Sphere n, { y : M // f y = a }),
      ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
        Topology.IsClosedEmbedding Γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
            (∀ z,
                ∃ t : ℝ,
                  S.flow t
                      ((S.data p).surgery.attachingSphere
                          (SphereCoordinates.standardParametrization
                            (S.data p).chart.NegativeCoordinates n z)).val =
                    (Γ z).val) ∧
              ∀ y : { x : M // f x = a },
                y ∈ Set.range Γ ↔
                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates n
  let γ : C(Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf n).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf n).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf n).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf n (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere n) :
    (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  let x₀ : Hemisphere.Sphere n := Hemisphere.point Bool.true ⟨0, by simp []⟩
  obtain ⟨D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ x₀ hγ hγi hγd hreach
  refine ⟨Γ, hΓ, hΓ.continuous.isClosedEmbedding hΓi, hΓd, hflow, ?_⟩
  intro y
  exact S.transported_attaching_range_iff hf p ha e e.surjective Γ hflow y

/-- Let `b < a` be regular values of `S : AdaptedWindows E f` with no critical value in `[b, a]`.
A family `α : ι → X → {f = a}` of smooth injective immersions of a compact `X` with pairwise
disjoint images is transported along the flow to a family `β : ι → X → {f = b}` of smooth closed
embeddings with pairwise disjoint images; if `range (α j)` is the backward basin of a critical
point `q` above `a` in the level `a`, then `range (β j)` is its backward basin in the level `b`. -/
theorem AdaptedWindows.exists_regular_band_family_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) (α : ι → X → { x : M // f x = a }) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ β : ι → X → { x : M // f x = b },
              (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
                (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                  (∀ j x,
                      Function.Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
                    Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                        ∀ j q,
                          a < f q →
                            (∀ x : { y : M // f y = a },
                                x ∈ Set.range (α j) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) →
                              ∀ y : { x : M // f x = b },
                                y ∈ Set.range (β j) ↔
                                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  dsimp only
  intro hα hαinj hαimm hpair
  obtain ⟨t, ht⟩ := S.reaches_lower_in_regular_band hf hab ha hgap za
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb za ⟨S.flow t za.val, ht⟩ α hα hαinj hαimm
      hpair (fun j x => S.reaches_lower_in_regular_band hf hab ha hgap (α j x))
  refine ⟨β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j q hq hfull
  exact S.transported_backward_basin_image hf hab hb q hq (α j) (β j) hfull (horbit j)

/-- Let `q` be a critical point of index `1` of the surgery-window system `S`, `G` a flow whose
backward basin of `q` in the lower level is the attaching sphere, and let the two attaching points
`u`, `v` flow forward to the distinct critical points `p`, `r` with `f p < S.lower q`.  Then
`attachingSphere u` flows backward to `q`, and every point flowing backward to `q` and forward to
`p` lies on the flow line of `attachingSphere u`. -/
theorem MorseCancellation.unique_connection_of_distinct_minimum_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : Continuous f) (G : Flow ℝ M)
    (p r q : ManifoldMorse.criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hpr : p ≠ r) (hp : f p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
        (𝓝 q.val) ∧
      ∀ x,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val) →
            ∃ t, G t ((S.data q).surgery.attachingSphere u).val = x := by
  have hdim : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := by
    intro h
    apply hpr
    apply Subtype.ext
    exact tendsto_nhds_unique (h ▸ hu) hv
  have hbu :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
      (𝓝 q.val) :=
    (hback _).mpr (Set.mem_range_self u)
  have hsingle (x : (S.data q).LowerLevel)
    (hb : Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val))
    (hp' : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val)) :
    x = (S.data q).surgery.attachingSphere u := by
    obtain ⟨w, hw⟩ := (hback x).mp hb
    rcases Metric.unitSphere_eq_two_points_of_finrank_eq_one hdim u v huv w with h | h
    · exact (congrArg (S.data q).surgery.attachingSphere h).symm.trans hw |>.symm
    · have hx : (S.data q).surgery.attachingSphere v = x := h ▸ hw
      have hrv : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val) := hx ▸ hv
      exact False.elim (hpr (Subtype.ext (tendsto_nhds_unique hp' hrv)))
  have h :=
    FlowSuspension.unique_connection_of_level_basin_intersection G G hf
      (S.lower_lt_value q) hp id (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      ((S.data q).surgery.attachingSphere u) hbu hu hsingle
  exact ⟨h.1, h.2.2⟩

end
