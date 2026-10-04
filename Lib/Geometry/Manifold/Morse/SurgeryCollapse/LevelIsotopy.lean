/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow

/-!
# Realising an isotopy of a regular level by a gradient-like flow

An isotopy `P` of a regular level `f = a` between two critical points is realised by a new
gradient-like field whose flow through the level is the old flow composed with `P`
(`AdaptedWindows.realize_unit_level_isotopy`, Milnor, *Lectures on the h-cobordism theorem*,
Lemma 4.7); if the descending sphere of `p` and the ascending sphere of `q` meet in one point after
the isotopy, the new flow has a unique trajectory from `p` to `q`, transverse along it when the
sheets are (`realize_unit_transverse_level_isotopy`).  For an index-`1` critical point on a
manifold with a unique minimum both attaching points are moved into the basin of that minimum
(`place_one_handle_in_unique_minimum_basin`, `realize_unique_minimum_one_handle_branches`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Let `a` be a regular value of `S : AdaptedWindows E f` between the critical points `q`, `p`
(`f q < a < f p`) and `P` a diffeomorphism of the level `{f = a}` isotopic to the identity such
that exactly one point `x` of the level flows backward to `p` with `P x` flowing forward to `q`.
Then there is a gradient-like field `V` with flow `G`, agreeing with `S.field` near the critical
points, with a point `z` of the level on a flow line from `p` to `q` through which every such flow
line passes, whose backward basins in the level are those of `S.flow` and whose forward basins are
those of `S.flow ∘ P`. -/
theorem AdaptedWindows.realize_unit_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    let _ := RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (z : { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
              (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
                (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
                  (∀ x,
                      x ∉ ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                    (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                      Filter.Tendsto (fun t => G t z.val) Filter.atBot (𝓝 p.val) ∧
                        Filter.Tendsto (fun t => G t z.val) Filter.atTop (𝓝 q.val) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p.val) →
                                Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q.val) →
                                  ∃ t, G t z.val = x) ∧
                            (∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 y)) ∧
                              ∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop
                                    (𝓝 y) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount
  obtain ⟨z₀, -⟩ := Set.ncard_eq_one.mp hcount
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level ha
  obtain
    ⟨r, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband ha z₀ P hP
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val P
      (fun x y => (hgeometry x).2.1 y) (fun x y => (hgeometry x).2.2 y) hend hleft hright
  obtain ⟨z, hzb, hzf, hunique⟩ :=
    FlowSuspension.exists_unique_connection_of_unit_level_count S.flow G hf.continuous hpa
      hqa P (fun x => hback x p.val) (fun x => hforward x q.val) hcount
  exact
    ⟨V, G, z, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hzb, hzf, hunique,
      hback, hforward⟩

/-- `realize_unit_level_isotopy` with sheets: if moreover `α : X → {f = a}` and `β : Y → {f = a}` are
transverse at `(x, y)` with `β y = α x`, `α` near `x` in the backward basin of `p` and `P ∘ β` near
`y` in the forward basin of `q`, the realised flow `G` has the flow line of `α x` from `p` to `q`
as its unique connection, and the flowed-out sheets `C (u, t) = G t (α u)`,
`D (u, t) = G t (β u)` are transverse at `((x, 0), (y, 0))`. -/
theorem AdaptedWindows.realize_unit_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) {a : ℝ} (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    let _ := RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∀ (α : X → { y : M // f y = a }) (β : Y → { y : M // f y = a }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
                β y = α x →
                  NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
                    (∀ᶠ u in 𝓝 x,
                        Filter.Tendsto (fun t => S.flow t (α u).val) Filter.atBot (𝓝 p.val)) →
                      (∀ᶠ u in 𝓝 y,
                          Filter.Tendsto (fun t => S.flow t (P (β u)).val) Filter.atTop
                            (𝓝 q.val)) →
                        ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
                              (∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0) ∧
                                (∀ z,
                                    z ∉ ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
                                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ w in 𝓝 z, V w = S.field w) ∧
                                    Filter.Tendsto (fun t => G t (α x).val) Filter.atBot
                                        (𝓝 p.val) ∧
                                      Filter.Tendsto (fun t => G t (α x).val) Filter.atTop
                                          (𝓝 q.val) ∧
                                        (∀ z,
                                            Filter.Tendsto (fun t => G t z) Filter.atBot
                                                (𝓝 p.val) →
                                              Filter.Tendsto (fun t => G t z) Filter.atTop
                                                  (𝓝 q.val) →
                                                ∃ t, G t (α x).val = z) ∧
                                          (∀ (z : { w : M // f w = a }) w,
                                              Filter.Tendsto (fun t => G t z.val) Filter.atBot
                                                  (𝓝 w) ↔
                                                Filter.Tendsto (fun t => S.flow t z.val)
                                                  Filter.atBot (𝓝 w)) ∧
                                            (∀ (z : { w : M // f w = a }) w,
                                                Filter.Tendsto (fun t => G t z.val) Filter.atTop
                                                    (𝓝 w) ↔
                                                  Filter.Tendsto (fun t => S.flow t (P z).val)
                                                    Filter.atTop (𝓝 w)) ∧
                                              let C : X × ℝ → M := fun u => G u.2 (α u.1).val
                                              let D : Y × ℝ → M := fun u => G u.2 (β u.1).val
                                              MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) C
                                                  (x, 0) ∧
                                                MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) D
                                                    (y, 0) ∧
                                                  C (x, 0) = (α x).val ∧
                                                    D (y, 0) = (α x).val ∧
                                                      (∀ᶠ u in 𝓝 (x, (0 : ℝ)),
                                                          Filter.Tendsto (fun t => G t (C u))
                                                            Filter.atBot (𝓝 p.val)) ∧
                                                        (∀ᶠ u in 𝓝 (y, (0 : ℝ)),
                                                            Filter.Tendsto (fun t => G t (D u))
                                                              Filter.atTop (𝓝 q.val)) ∧
                                                          NativeTransversality.At
                                                            (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
                                                            𝓘(ℝ, E) C D (x, 0) (y, 0) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨V, G, z, hV, hG, hzero, hdesc, hgerms, -, -, hunique, hback, hforward⟩ :=
    S.realize_unit_level_isotopy hf p q hpa hqa ha P hP hcount
  have hαG : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => G t (α u).val) Filter.atBot (𝓝 p.val) := by
    filter_upwards [hαbasin] with u hu
    exact (hback (α u) p.val).mpr hu
  have hβG : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => G t (β u).val) Filter.atTop (𝓝 q.val) := by
    filter_upwards [hβbasin] with u hu
    exact (hforward (β u) q.val).mpr hu
  have hxforward : Filter.Tendsto (fun t => G t (α x).val) Filter.atTop (𝓝 q.val) := by
    have hh := hβG.self_of_nhds
    rwa [hcross] at hh
  obtain ⟨s, hs⟩ := hunique (α x).val hαG.self_of_nhds hxforward
  have huniq (w : M) (hwb : Filter.Tendsto (fun t => G t w) Filter.atBot (𝓝 p.val))
    (hwf : Filter.Tendsto (fun t => G t w) Filter.atTop (𝓝 q.val)) : ∃ t, G t (α x).val = w := by
    obtain ⟨t, ht⟩ := hunique w hwb hwf
    refine ⟨t - s, ?_⟩
    rw [← hs, ← G.map_add, sub_add_cancel, ht]
  refine
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hαG.self_of_nhds, hxforward, huniq, hback, hforward, ?_⟩
  exact
    FlowSuspension.native_transverse_basin_tubes_of_level_maps hf ha hV G hG
      (fun w hw => hdesc w (ha w hw)) α β x y hα hβ hcross htrans hαG hβG

attribute [local instance 100] Classical.propDecidable in
/-- Let `q` be a critical point of index `1` of `S : AdaptedWindows E f` and `p` the unique critical
point of index `0`.  Then there is a diffeomorphism `d` of the lower level of `q` isotopic to the
identity such that `f p < lower q` and every attaching point `d (attachingSphere w)` flows to `p`. -/
theorem AdaptedWindows.place_one_handle_in_unique_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f r = 0 → r = p) :
    let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧
        f p < S.toSurgeryWindows.lower q ∧
          ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
            Filter.Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
              Filter.atTop (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data q).lower_regular
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one hi
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := fun h => huv ((S.data q).attaching_isClosedEmbedding.injective h)
  obtain ⟨d, hd, ⟨r, hr, hru⟩, ⟨s, hs, hsv⟩⟩ :=
    MorseCancellation.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpu : Filter.Tendsto (fun t => S.flow t (d (α u)).val) Filter.atTop (𝓝 p.val) :=
    hunique r hr ▸ hru
  have hpv : Filter.Tendsto (fun t => S.flow t (d (α v)).val) Filter.atTop (𝓝 p.val) :=
    hunique s hs ▸ hsv
  refine
    ⟨d, hd, S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu, ?_⟩
  intro w
  rcases Metric.unitSphere_eq_two_points_of_finrank_eq_one hi u v huv w with rfl | rfl
  · exact hpu
  · exact hpv

attribute [local instance 100] Classical.propDecidable in
/-- Let `q` be a critical point of index `1` of `S : AdaptedWindows E f` and `p` the unique critical
point of index `0`.  Then there is an `AdaptedWindows E f` package `T` with the same charts, the
same field germs at the critical points, whose attaching points of `q` all flow to `p`, and with
no flow line from `q` to a critical point other than `p`, `q`. -/
theorem AdaptedWindows.realize_unique_minimum_one_handle_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (p q : ManifoldMorse.criticalPoints E f)
    (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f r = 0 → r = p) :
    ∃ T : AdaptedWindows E f,
      (∀ r : ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 r.val, T.field x = S.field x) ∧
        (∀ r, (T.data r).chart = (S.data r).chart) ∧
          (∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
              Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val)
                Filter.atTop (𝓝 p.val)) ∧
            ∀ r : ManifoldMorse.criticalPoints E f,
              r ≠ q →
                r ≠ p →
                  ∀ x,
                    ¬(Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 q.val) ∧
                        Filter.Tendsto (fun t => T.flow t x) Filter.atTop (𝓝 r.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, hpq, hall⟩ := S.place_one_handle_in_unique_minimum_basin hf p q hone hunique
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one hi
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  have hVz : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0 := fun x hx =>
    (hzero x).mpr (S.zero x hx)
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
      (𝓝 p.val) :=
    (hforward _ p.val).mpr (hall w)
  have hno (r : ManifoldMorse.criticalPoints E f) (hrq : r ≠ q) (hrp : r ≠ p) (x : M) :
    ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val)) := by
    intro hx
    have hmono := FlowConstruction.antitone_flow_height hf G hG hVz hdesc x
    have hle : f r ≤ f q :=
      (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.2) 0).trans
        (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.1) 0)
    have hrq' : f r < f q :=
      lt_of_le_of_ne hle (fun h => hrq (Subtype.ext (S.distinct r.property q.property h)))
    have hrlow : f r < S.toSurgeryWindows.lower q :=
      (S.toSurgeryWindows.value_lt_upper r).trans (S.separated r q hrq')
    obtain ⟨t, ht⟩ :=
      FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
        (S.toSurgeryWindows.lower_lt_value q) hrlow
    let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
    have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
      (MorseCancellation.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
    have hzr : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 r.val) :=
      (MorseCancellation.flow_time_atTop_limit_iff G t x r.val).mpr hx.2
    obtain ⟨w, hw⟩ := (hbq z).mp hzq
    have hpz := hends w
    rw [hw] at hpz
    exact hrp (Subtype.ext (tendsto_nhds_unique hzr hpz))
  have hmodel (r : ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 r.val, V x = (S.data r).chart.descentField x := by
    filter_upwards [hgerms r r.property, S.critical_model_germ r] with x hx hxs
    exact hx.trans hxs
  obtain ⟨T, hfield, hflow, hchart⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow hf hm S.distinct hV G hG hVz hdesc
      (fun r => (S.data r).chart) hmodel
  refine ⟨T, ?_, hchart, ?_, ?_⟩
  · intro r
    rw [hfield]
    exact hgerms r r.property
  · intro w
    let z := (T.data q).surgery.attachingSphere w
    have hzq : Filter.Tendsto (fun t => T.flow t z.val) Filter.atBot (𝓝 q.val) :=
      (T.attaching_basin_iff hf q z).mpr ⟨w, rfl⟩
    obtain ⟨r₀, hr₀, r, hr, -, hrlim, hheight⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
        T.descent T.distinct z.val
    have hrq : (⟨r, hr⟩ : ManifoldMorse.criticalPoints E f) ≠ q := by
      intro heq
      have hlt := (hheight ((T.data q).lower_regular z.val z.property)).1
      have hrval : r = q.val := congrArg Subtype.val heq
      rw [hrval, z.property] at hlt
      nlinarith [sq_nonneg (T.data q).radius]
    have hrp : (⟨r, hr⟩ : ManifoldMorse.criticalPoints E f) = p := by
      by_contra hne
      apply hno ⟨r, hr⟩ hrq hne z.val
      rw [hflow] at hzq hrlim
      exact ⟨hzq, hrlim⟩
    exact (congrArg Subtype.val hrp) ▸ hrlim
  · intro r hrq hrp x
    rw [hflow]
    exact hno r hrq hrp x

end
