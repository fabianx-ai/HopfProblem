/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.Combinatorics.IndexDisorder
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange

/-!
# Rearrangement: ordering the critical values by index

Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.8: every Morse function on a compact
manifold can be replaced by a *self-indexing* one with the same critical points and indices, whose
critical values increase with the index.  For two consecutive critical points with
`index q ≤ index p` a general-position isotopy of the intermediate level separates the descending
sphere of `q` from the ascending sphere of `p` (`AdaptedWindows.remove_connections_of_index_le`,
`remove_connections_of_nonincreasing_indices`; Milnor Theorem 4.4), after which the two critical
values may be exchanged (`exchange_nonincreasing_native_indices`).  Decreasing the index disorder
gives the index-ordered system
(`MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- Milnor, h-cobordism Theorem 4.4.  Let `p`, `q` be consecutive critical points of
`S : AdaptedWindows E f`, `f p < f q`, with `index q = n + 1`, `coindex p = m + 1` and
`index q ≤ index p`.  Then there is a gradient-like field `V` with flow `G`, agreeing with
`S.field` near the critical points, with no flow line from `q` to `p`. -/
theorem AdaptedWindows.remove_connections_of_index_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (n m : ℕ) (hqindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)
    (hppos : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1)
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1) := ⟨hqindex⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1) := ⟨hppos⟩
  obtain ⟨D, b, -, hb, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  have horbit' (x : (S.data p).UpperLevel) : ∃ t, S.flow t x = (b x : M) := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, ht.trans (hb x).symm⟩
  let α := (S.data p).transportedAttachingSphere (S.data q) n b.toHomeomorph
  have hα : ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf n b
  have hB := (S.data p).belt_smooth hf m
  have hdim :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) <
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace, Fintype.card_fin]
    have hh := (S.data p).chart.finrank_negative_add_positive
    omega
  obtain ⟨e, he, hdisjoint⟩ :=
    MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension hα hB hdim
  have hbasins :
    ∀ x : (S.data p).UpperLevel,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t (e x)) Filter.atTop (𝓝 p.val)) := by
    rintro x ⟨hxq, hxp⟩
    obtain ⟨v, hv⟩ := (S.transported_attaching_basin_iff hf p q n b.toHomeomorph horbit' x).mp hxq
    have hB := (S.belt_basin_iff hf p (e x)).mp hxp
    have hαx : e x ∈ Set.range (e ∘ α) := ⟨v, congrArg e hv⟩
    exact Set.disjoint_left.mp hdisjoint hαx hB
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  let z : (S.data p).UpperLevel := α (Classical.arbitrary (Hemisphere.Sphere n))
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hac hcb
      (MorseCancellation.surgery_pair_inner_band_regular p q hconsecutive hpa hbq)
      (S.data p).upper_regular z e he
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val e
      (fun x => (hgeometry x).2.1) (fun x => (hgeometry x).2.2) hend hleft hright
  refine ⟨V, G, hV, hG, fun x hx => (hzeros x).mpr (S.zero x hx), hneg, hgerms, ?_⟩
  exact
    FlowSuspension.no_connection_of_level_basin_disjointness S.flow G hf.continuous hqc hpc
      e (fun x => hback x q.val) (fun x => hforward x p.val) hbasins

/-- `remove_connections_of_index_le` without the positivity hypotheses: for consecutive critical
points `p`, `q` with `f p < f q` and `index q ≤ index p` there is a smooth field `V` with flow `G`
that vanishes at the critical points, strictly decreases `f` elsewhere, equals `S.field` near
every critical point, and has no flow line from `q` to `p`. -/
theorem AdaptedWindows.remove_connections_of_nonincreasing_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  by_cases hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_upper_index_zero hf p q hpq hqzero⟩
  by_cases hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_lower_positive_zero hf p q hpq hpzero⟩
  exact
    S.remove_connections_of_index_le hf p q hpq hconsecutive
      (Module.finrank ℝ (S.data q).chart.NegativeCoordinates - 1)
      (Module.finrank ℝ (S.data p).chart.PositiveCoordinates - 1) (by omega) (by omega) hle

/-- Let `p`, `q` be consecutive critical points of `S : AdaptedWindows E f` with `f p < f q` and
`index q ≤ index p`, on a connected manifold.  Then there is a Morse function `g` with the same
critical points, `g p = f q`, `g q = f p`, `g = f` outside the band `(lower p, upper q)` and near
the other critical points, distinct critical values, an `AdaptedWindows E g`, the same indices and
the same index counts. -/
theorem AdaptedWindows.exchange_nonincreasing_native_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle : MorseCancellation.nativeMorseIndex E f q ≤ MorseCancellation.nativeMorseIndex E f p) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            g p = f q ∧
              g q = f p ∧
                (∀ z,
                    f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                      g =ᶠ[𝓝 z] f) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                    Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
                      Nonempty (AdaptedWindows E g) ∧
                        (∀ z ∈ ManifoldMorse.criticalPoints E f,
                            MorseCancellation.nativeMorseIndex E g z =
                              MorseCancellation.nativeMorseIndex E f z) ∧
                          ∀ k,
                            MorseCancellation.nativeMorseCount E g k =
                              MorseCancellation.nativeMorseCount E f k := by
  have hle' :
    Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart,
      MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hle
  obtain ⟨V, G, hV, hG, hzeros, hneg, hgerms, hnoconnection⟩ :=
    S.remove_connections_of_nonincreasing_indices hf p q hpq hconsecutive hle'
  have hpgerm : ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p p.property, S.critical_model_germ p] with y hy hmodel
    exact hy.trans hmodel
  have hqgerm : ∀ᶠ y in 𝓝 q.val, V y = (S.data q).chart.descentField y := by
    filter_upwards [hgerms q q.property, S.critical_model_germ q] with y hy hmodel
    exact hy.trans hmodel
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, -, hexterior, -, -, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV G hG hzeros
      hneg S.distinct (S.data p).chart (S.data q).chart hpgerm hqgerm hpband hqband hpq hqband
      hpband (MorseCancellation.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive)
      hnoconnection
  obtain ⟨hinj, hnew⟩ :=
    MorseCancellation.adapted_surgery_system_after_value_exchange S hg hmg p.property q.property hcrit
      hgp hgq hothers
  exact
    ⟨g, hg, hmg, hcrit, hgp, hgq, hexterior, hothers, hinj, hnew, hindices,
      MorseCancellation.nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

/-- Milnor, h-cobordism Theorem 4.8 (rearrangement).  For a Morse function `f₀` with an
`AdaptedWindows` package on a compact connected manifold there is a Morse function `f` with the
same critical points and indices, an `AdaptedWindows E f`, whose indices increase with the
critical values, and with the same index counts as `f₀`. -/
theorem MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f₀ : M → ℝ} (S₀ : AdaptedWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : ManifoldMorse.IsMorse E f₀) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              ∃ _ : AdaptedWindows E f,
                (∀ p q : ManifoldMorse.criticalPoints E f,
                    f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
                  ∀ k, nativeMorseCount E f k = nativeMorseCount E f₀ k := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧ nativeIndexDisorder E f = n
  have hex : ∃ n, P n :=
    ⟨nativeIndexDisorder E f₀, f₀, hf₀, hm₀, rfl, fun _ _ => rfl, S₀.distinct, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hindices, hinj, hdisorder⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  have horder :
    ∀ p q : ManifoldMorse.criticalPoints E f,
      f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q := by
    by_contra hnot
    let _ := S.finite.fintype
    obtain ⟨p, q, hpq, hconsecutive, hinversion⟩ :=
      IndexDisorder.exists_adjacent_index_inversion (h :=
        fun x : ManifoldMorse.criticalPoints E f => f x)
        (fun x y h => Subtype.ext (hinj x.property y.property h))
        (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) hnot
    obtain ⟨g, hg, hmg, hcritg, hgp, hgq, -, hothers, hinjg, -, hindicesg, -⟩ :=
      S.exchange_nonincreasing_native_indices hf hm p q hpq hconsecutive hinversion.le
    have hdecrease : nativeIndexDisorder E g < nativeIndexDisorder E f :=
      nativeIndexDisorder_exchange_lt S.finite hinj p q hpq hconsecutive hinversion hcritg hgp hgq
        hothers hindicesg
    have hindicesg₀ (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hminimal := Nat.find_min' hex ⟨g, hg, hmg, hcritg.trans hcrit, hindicesg₀, hinjg, rfl⟩
    rw [← hdisorder] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact
    ⟨f, hf, hm, hcrit, hindices, S, horder,
      nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

end
