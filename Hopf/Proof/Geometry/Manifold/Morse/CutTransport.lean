/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.LinearAlgebra.Matrix.TransvectionReduction
import Lib.Geometry.Manifold.Morse.CutTransport

/-!
# Cut transport for adapted Morse windows (proof-specific)

Proof-specific material of the six-sphere formalization: this module is not
library mathematics and is not registered in `Lib.lean`.  It is the part of the
former `Lib.Geometry.Manifold.Morse.CutTransport` that the round-7 audit graded D
-- the project's index-2/3 cancellation bookkeeping for `AdaptedWindows E f` and
`SurgeryWindows`, together with the Whitney-trick sheet-passage geometry
(`LongitudinalTubeMotion`, `CenteredSheetPassage`) that shares the file.  The
general islands (sublevel inclusions, the equal-cut comparison and the isotopy
lemmas) stayed in `Lib` in `Lib.Geometry.Manifold.Morse.CutTransport`.

Contents: flow transport of sections and basins between two regular cuts
(`AdaptedWindows.level_transport_homotopic_in_sublevel`,
`backward_basin_reaches_intermediate_cut`, `transported_basin_image_of_reaching`,
`reaches_cut_of_forward_holonomy`, `section_class_of_flow_transport`,
`MorseCancellation.lower_backward_basins_preserved`, `lower_forward_basins_preserved`,
`signed_relation_of_regular_cut_transport`,
`regular_sublevel_inclusion_bijective`, `regularCutHomologyEquiv`); the canonical
middle matrix (`canonicalMiddleMatrix`, `canonicalMiddleMatrix_equalCut`,
`canonicalMiddleMatrix_single_class_addition`); sheet passages with prescribed
normal change (`exists_sheet_arc_tube_with_normal_change`,
`exists_clean_sheet_arc_tube_with_normal_change`,
`exists_relative_sheet_passages_with_normal_change`,
`LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs`,
`exists_centered_passage_clock`, `passageNormalProduct`, `relative_normal_frame_det`,
`passage_normal_relative_det_neg`, `mfderiv_normal_trace_model`,
`LongitudinalTubeMotion.normal_trace_mfderiv`, `mfderiv_retime_unit_rate`,
`fderiv_retimed_trace_parameter`, `exists_shared_passage_frames`,
`CenteredSheetPassage`, `LongitudinalTubeMotion.centeredSheetPassage`,
`bijective_trace_normal_of_native_transverse`,
`hasFDerivAt_terminal_normal_factor`); window arithmetic
(`regular_below_pivot_of_regular_lower_band`, `lower_window_le_of_radius_le`,
`common_cut_band_of_smaller_radius`, `higher_window_separation_of_value_order`,
`SurgeryWindows.regular_before_first_middle_pivot`,
`low_index_cut_of_preserved_other_values`,
`native_index_order_of_equal_index_exchange`,
`upper_point_not_on_belt_of_lower_orbit`); and the index-2/3 counting
(`consecutive_last_two_first_three`, `native_index_excluded_of_count_zero`),
plus the local instance helper `ManifoldMorse.MorseSurgeryData.instLocal1`.

Moved verbatim from `Hopf/Recognition.lean` via
`Lib/Geometry/Manifold/Morse/CutTransport.lean`; statements unchanged.
-/
open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


theorem AdaptedWindows.level_transport_homotopic_in_sublevel {E M X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [TopologicalSpace X]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (g : C(X, { y : M // f y = b })) (γ : C(X, { y : M // f y = a }))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (g x).val = (γ x).val) :
    ContinuousMap.Homotopic ((MorseCancellation.levelSublevelMap f le_rfl).comp g)
      ((MorseCancellation.levelSublevelMap f hab.le).comp γ) := by
  have hboundary (y : M) (hy : f y = a) : mvfderiv 𝓘(ℝ, E) f y (S.field y) < 0 :=
    S.descent y (ha y hy)
  have hreach (x : X) : (g x).val ∈ FlowCancellation.levelBasin S.flow f a := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, by rw [ht]; exact (γ x).property⟩
  let θ : X → ℝ := fun x => FlowCancellation.signedLevelTime S.flow f a (g x).val
  obtain ⟨hB, htime, -⟩ :=
    FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral hboundary
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact
      ContinuousAt.comp (f := fun y : X => (g y).val)
        (htime.continuousOn.continuousAt (hB.mem_nhds (hreach x)))
        (continuous_subtype_val.comp g.continuous).continuousAt
  have hhit (x : X) : f (S.flow (θ x) (g x).val) = a :=
    FlowCancellation.signedLevelTime_hits S.flow f a (hreach x)
  have hθpos (x : X) : 0 < θ x := by
    by_contra h
    have hh :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent (g x).val
        (le_of_not_gt h)
    change f (S.flow 0 (g x).val) ≤ f (S.flow (θ x) (g x).val) at hh
    rw [S.flow.map_zero_apply, (g x).property, hhit x] at hh
    exact not_le_of_gt hab hh
  have hend (x : X) : S.flow (θ x) (g x).val = (γ x).val := by
    obtain ⟨t, ht⟩ := horbit x
    have hθt : θ x = t :=
      FlowCancellation.signedLevelTime_eq_of_level S.flow hf.continuous
        (MorseCancellation.contMDiff_directionalDerivative hf S.smooth).continuous
        (fun y s => FlowConstruction.hasDerivAt_comp_integralCurve hf (S.integral y) s)
        hboundary (by rw [ht]; exact (γ x).property)
    rw [hθt]
    exact ht
  have hstay (u : unitInterval) (x : X) : f (S.flow ((u : ℝ) * θ x) (g x).val) ≤ b := by
    have hh :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent (g x).val
        (mul_nonneg u.property.1 (hθpos x).le)
    simpa only [S.flow.map_zero_apply, (g x).property] using hh
  refine
    ⟨{  toFun := fun z => ⟨S.flow ((z.1 : ℝ) * θ z.2) (g z.2).val, hstay z.1 z.2⟩
        continuous_toFun :=
          (S.flow.continuous
                ((continuous_subtype_val.comp continuous_fst).mul (hθ.comp continuous_snd))
                (continuous_subtype_val.comp (g.continuous.comp continuous_snd))).subtype_mk
            _
        map_zero_left := ?_
        map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change S.flow ((0 : ℝ) * θ x) (g x).val = (g x).val
    simp
  · intro x
    apply Subtype.ext
    change S.flow ((1 : ℝ) * θ x) (g x).val = (γ x).val
    simpa only [one_mul] using hend x


theorem MorseCancellation.regular_sublevel_inclusion_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) (k : ℕ) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) k) := by
  obtain ⟨e, he⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv hf hab hband
  have hmap : e.toFun = sublevelMap f hab := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (he x)
  have hh := (SingularHomology.homotopyEquivHomologyEquiv e k).bijective
  change Function.Bijective (SingularMayerVietoris.singularHomologyMap e.toFun k) at hh
  rwa [hmap] at hh


def MorseCancellation.canonicalMiddleMatrix {M : Type} [TopologicalSpace M] {f : M → ℝ} {r n : ℕ}
    {a : ℝ} (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a })) :
    Matrix (Fin r) (Fin n) ℤ :=
  classCoordinateMatrix B (fun j => middleSectionClass (γ j))


theorem MorseCancellation.canonicalMiddleMatrix_equalCut {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f g : M → ℝ} {a : ℝ} [Nonempty M] (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a })) :
    canonicalMiddleMatrix (B.trans (equalCutHomologyEquiv hsub))
        (fun j => equalCutSection hlevel (γ j)) =
      canonicalMiddleMatrix B γ := by
  funext i j
  change
    B.symm ((equalCutHomologyEquiv hsub).symm (middleSectionClass (equalCutSection hlevel (γ j))))
        i =
      B.symm (middleSectionClass (γ j)) i
  rw [← equalCutSection_class hsub hlevel, LinearEquiv.symm_apply_apply]

theorem MorseCancellation.native_index_order_of_equal_index_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ}
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p q : ManifoldMorse.criticalPoints E f)
    (hequal : nativeMorseIndex E f p = nativeMorseIndex E f q)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g x = f x)
    (hindices :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    ∀ x y : ManifoldMorse.criticalPoints E g,
      g x < g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y := by
  classical
  have hform (x : ManifoldMorse.criticalPoints E f) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using
      hothers x x.property (fun h => hxp (Subtype.ext h)) (fun h => hxq (Subtype.ext h))
  have hind (x : ManifoldMorse.criticalPoints E f) :
    nativeMorseIndex E f (Equiv.swap p q x) = nativeMorseIndex E f x := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hequal.symm
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hequal
    simp only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq]
  intro x y hxy
  let x' : ManifoldMorse.criticalPoints E f := ⟨x.val, hcrit ▸ x.property⟩
  let y' : ManifoldMorse.criticalPoints E f := ⟨y.val, hcrit ▸ y.property⟩
  have hxy' : f (Equiv.swap p q x') < f (Equiv.swap p q y') := by
    rw [← hform, ← hform]
    exact hxy
  have hh := horder (Equiv.swap p q x') (Equiv.swap p q y') hxy'
  rw [hind, hind] at hh
  rw [hindices x x'.property, hindices y y'.property]
  exact hh

theorem AdaptedWindows.backward_basin_reaches_intermediate_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x p : M}
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) {b : ℝ} (hxb : f x < b)
    (hbp : b < f p) : x ∈ FlowCancellation.levelBasin S.flow f b := by
  have hh : Filter.Tendsto (fun t => f (S.flow t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hback
  obtain ⟨t, ht⟩ := (hh.eventually (eventually_gt_nhds hbp)).exists
  apply
    mem_range_of_exists_le_of_exists_ge
      (hf.continuous.comp (S.flow.continuous continuous_id continuous_const))
  · refine ⟨0, ?_⟩
    change f (S.flow 0 x) ≤ b
    rw [S.flow.map_zero_apply]
    exact hxb.le
  · exact ⟨t, ht.le⟩

theorem AdaptedWindows.transported_basin_image_of_reaching {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {X : Type} {a b : ℝ}
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (p : M)
    (α : X → { y : M // f y = a }) (β : X → { y : M // f y = b })
    (hfull : ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (α x).val = (β x).val)
    (hreach :
      ∀ y : { z : M // f z = b },
        Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) →
          y.val ∈ FlowCancellation.levelBasin S.flow f a) :
    ∀ y, y ∈ Set.range β ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact
      (MorseCancellation.flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
        ((hfull (α z)).mp (Set.mem_range_self z))
  · intro hy
    obtain ⟨s, hs⟩ := hreach y hy
    let x : { z : M // f z = a } := ⟨S.flow s y.val, hs⟩
    have hx : Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) :=
      (MorseCancellation.flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hfull x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

theorem AdaptedWindows.upper_point_not_on_belt_of_lower_orbit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f) {a : ℝ}
    (ha : a < f q) (x : { y : M // f y = a }) (y : (S.data q).UpperLevel)
    (horbit : ∃ t : ℝ, S.flow t x.val = y.val) : y ∉ Set.range (S.data q).surgery.beltSphere := by
  intro hy
  have hyforward := (S.belt_basin_iff hf q y).mpr hy
  obtain ⟨t, ht⟩ := horbit
  have hxforward : Filter.Tendsto (fun s => S.flow s x.val) Filter.atTop (𝓝 q.val) := by
    rw [← ht] at hyforward
    exact (MorseCancellation.flow_time_atTop_limit_iff S.flow t x.val q.val).mp hyforward
  have hheight : Filter.Tendsto (fun s => f (S.flow s x.val)) Filter.atTop (𝓝 (f q)) :=
    hf.continuous.continuousAt.tendsto.comp hxforward
  have hh :=
    (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
          x.val).le_of_tendsto
      hheight 0
  have hqa : f q ≤ a := by simpa only [S.flow.map_zero_apply, x.property] using hh
  exact ha.not_ge hqa

theorem MorseCancellation.lower_backward_basins_preserved {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry :
      ∀ x,
        Set.range (fun t => H t x) = Set.range (fun t => S.flow t x) ∧
          (∀ p,
              Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
                Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p)) ∧
            ∀ p,
              Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p) ↔
                Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y) (p : M) (hp : f p ≤ l) :
    (∀ x,
        Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) ∧
      ∀ x,
        Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p) →
          Set.range (fun t => T.flow t x) = Set.range (fun t => S.flow t x) := by
  have hnew (x : M) (hx : Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p)) :
    ∀ t, T.flow t x = H t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono :=
      FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x
    have hagree (t : ℝ) : T.field (T.flow t x) = W (T.flow t x) :=
      hout _ ((hmono.ge_of_tendsto hheight t).trans hp)
    intro t
    rcases le_total 0 t with ht | ht
    · exact
        FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp)) H T.flow
          hH T.integral (fun s _ => hagree s) t ht
    · exact
        FlowCancellation.native_flow_eq_on_negative_halfline (hW.of_le (by simp)) H T.flow
          hH T.integral (fun s _ => hagree s) t ht
  have hold (x : M) (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) :
    ∀ t, H t x = T.flow t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    have hbound (t : ℝ) : f (H t x) ≤ l := by
      have hm : H t x ∈ Set.range (fun s => S.flow s x) := (hgeometry x).1 ▸ Set.mem_range_self t
      obtain ⟨s, hs⟩ := hm
      rw [← hs]
      exact (hmono.ge_of_tendsto hheight s).trans hp
    have hagree (t : ℝ) : W (H t x) = T.field (H t x) := (hout _ (hbound t)).symm
    intro t
    rcases le_total 0 t with ht | ht
    · exact
        FlowCancellation.native_flow_eq_on_positive_halfline (T.smooth.of_le (by simp))
          T.flow H T.integral hH (fun s _ => hagree s) t ht
    · exact
        FlowCancellation.native_flow_eq_on_negative_halfline (T.smooth.of_le (by simp))
          T.flow H T.integral hH (fun s _ => hagree s) t ht
  refine ⟨?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have heq : (fun t => T.flow t x) = fun t => H t x := funext (hnew x hx)
      rw [heq] at hx
      exact ((hgeometry x).2.2 p).mp hx
    · intro hx
      have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
      have hh := ((hgeometry x).2.2 p).mpr hx
      rwa [heq] at hh
  · intro x hx
    have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
    rw [← heq]
    exact (hgeometry x).1

theorem MorseCancellation.lower_forward_basins_preserved {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y) (y : M) (hy : f y ≤ l) :
    ∀ p,
      Filter.Tendsto (fun t => T.flow t y) Filter.atTop (𝓝 p) ↔
        Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p) := by
  have hmono :=
    FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent y
  have hbound (t : ℝ) (ht : 0 ≤ t) : f (T.flow t y) ≤ l := by
    have hh := hmono ht
    change f (T.flow t y) ≤ f (T.flow 0 y) at hh
    rw [T.flow.map_zero_apply] at hh
    exact hh.trans hy
  have heq : (fun t => T.flow t y) =ᶠ[Filter.atTop] (fun t => H t y) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact
      FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp)) H T.flow hH
        T.integral (fun s hs => hout _ (hbound s hs)) t ht
  intro p
  exact (Filter.tendsto_congr' heq).trans (hgeometry y p)

theorem AdaptedWindows.reaches_cut_of_forward_holonomy {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (D : { y : M // f y = b } → { y : M // f y = b })
    (hforward :
      ∀ x : { y : M // f y = b },
        ∀ p : M,
          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p))
    (x : { y : M // f y = b }) (y : { z : M // f z = a })
    (horbit : ∃ t : ℝ, S.flow t (D x).val = y.val) :
    x.val ∈ FlowCancellation.levelBasin T.flow f a := by
  obtain ⟨p, hp, q, hq, -, hytop, hyheight⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hqa : f q < a := by simpa only [y.property] using (hyheight (ha y.val y.property)).1
  obtain ⟨t, ht⟩ := horbit
  have hDx : Filter.Tendsto (fun s => S.flow s (D x).val) Filter.atTop (𝓝 q) := by
    rw [← ht] at hytop
    exact (MorseCancellation.flow_time_atTop_limit_iff S.flow t (D x).val q).mp hytop
  have hxtop := (hforward x q).mpr hDx
  obtain ⟨r, hr, s, hs, hxback, -, hxheight⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
      T.descent T.distinct x.val
  have hbr : b < f r := by simpa only [x.property] using (hxheight (hb x.val x.property)).2
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits T.flow hf.continuous hxback
      hxtop (hab.trans hbr) hqa

theorem AdaptedWindows.section_class_of_flow_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (β : C((Hemisphere.Sphere 2), { y : M // f y = b }))
    (α : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val) :
    SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hab.le) 2
        (MorseCancellation.middleSectionClass α) =
      MorseCancellation.middleSectionClass β := by
  have hm :=
    SingularHomology.homotopic_homologyMap
      (S.level_transport_homotopic_in_sublevel hf hab ha β α horbit) 2
  have hmaps :
    (MorseCancellation.sublevelMap f hab.le).comp ((MorseCancellation.levelSublevelMap f le_rfl).comp α) =
      (MorseCancellation.levelSublevelMap f hab.le).comp α := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [MorseCancellation.middleSectionClass, ← LinearMap.comp_apply, ←
    SingularHomology.singularHomologyMap_comp, hmaps, ← hm]
  rfl

theorem MorseCancellation.signed_relation_of_regular_cut_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (β δ γ : C((Hemisphere.Sphere 2), { y : M // f y = b }))
    (α ζ θ : C((Hemisphere.Sphere 2), { y : M // f y = a })) (k : ℤ)
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val)
    (hδ : ∀ x, ∃ t : ℝ, T.flow t (δ x).val = (ζ x).val)
    (hγ : ∀ x, ∃ t : ℝ, S.flow t (γ x).val = (θ x).val)
    (hmap :
      SingularMayerVietoris.singularHomologyMap δ 2 =
        SingularMayerVietoris.singularHomologyMap β 2 +
          k • SingularMayerVietoris.singularHomologyMap γ 2) :
    middleSectionClass ζ = middleSectionClass α + k • middleSectionClass θ := by
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap γ 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap γ 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap γ 2)
  have hclasses : middleSectionClass δ = middleSectionClass β + k • middleSectionClass γ := by
    simp only [middleSectionClass, SingularHomology.singularHomologyMap_comp,
      LinearMap.comp_apply, hmap, LinearMap.add_apply, heval, map_add, map_zsmul]
  apply (regular_sublevel_inclusion_bijective hf hab.le hband 2).1
  rw [map_add, map_zsmul, T.section_class_of_flow_transport hf hab ha δ ζ hδ,
    S.section_class_of_flow_transport hf hab ha β α hβ,
    S.section_class_of_flow_transport hf hab ha γ θ hγ]
  exact hclasses

theorem MorseCancellation.exists_sheet_arc_tube_with_normal_change {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O)
    (C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart (C.prodCongr R) Φ₁) ∧
                  Φ.target ⊆ O := by
  let Φ₂ :=
    linearTransverseChart (C.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))))
      Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hright₂ : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₂ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.trans (linearTransverseChart_axis _ Φ₁ t).symm
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, htarget⟩ :=
    exists_sheet_arc_tube ha hinj hi hdim Φ₀ Φ₂ hΦ₀ hΦ₂ hleft hright₂ hO haO
  refine ⟨R, ε, hε, Φ, hprod, haxis, hgl, ?_, htarget⟩
  filter_upwards [hgr] with z hz
  exact hz

theorem MorseCancellation.exists_clean_sheet_arc_tube_with_normal_change {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {S T O : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (hrec₀ : ∀ z ∈ Φ₀.source, Φ₀ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrec₁ : ∀ z ∈ Φ₁.source, Φ₁ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0)
    (hcount₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ S ↔ t = 0)
    (hcount₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ T ↔ t = 1) (hO : IsOpen O)
    (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O)
    (C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart (C.prodCongr R) Φ₁) ∧
                  (∀ z ∈ Φ.source, Φ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                    (∀ z ∈ Φ.source, Φ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0) ∧ Φ.target ⊆ O := by
  obtain ⟨R, r, hr, Ψ, hΨprod, haxis, hgl, hgr, hΨO⟩ :=
    exists_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright hO haO C
  let Φ₂ := linearTransverseChart (C.prodCongr R) Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hrec₂ : ∀ z ∈ Φ₂.source, Φ₂ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Φ₁ (z.1, (C z.2.1, R z.2.2)) ∈ T ↔ _
    rw [hrec₁ (z.1, (C z.2.1, R z.2.2)) hz.2, map_eq_zero_iff C C.injective]
  have hlocal₀ :
    ∀ᶠ z : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) in
      𝓝 (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))),
      Ψ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0 := by
    filter_upwards [hgl, Φ₀.open_source.mem_nhds hΦ₀] with z he hz
    rw [he]
    exact hrec₀ z hz
  have hlocal₁ :
    ∀ᶠ z : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) in
      𝓝 ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))),
      Ψ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    filter_upwards [hgr, Φ₂.open_source.mem_nhds hΦ₂] with z he hz
    rw [he]
    exact hrec₂ z hz
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΨprod ⟨ht, Metric.mem_closedBall_self hr.le⟩
  have haway₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ 0 → Ψ (t, 0) ∉ S := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₀ t ht).mp hh)
  have haway₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ 1 → Ψ (t, 0) ∉ T := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₁ t ht).mp hh)
  obtain ⟨ε, hε, Φ, hprod, hformula, hΦΨ, hrecS, hrecT⟩ :=
    exists_clean_axis_tube_restriction Ψ CompactIccSpace.isCompact_Icc hzero hS hT 0 1
      {v : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) | v.2 = 0}
      {v : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) | v.1 = 0} hlocal₀ hlocal₁
      haway₀ haway₁
  refine
    ⟨R, ε, hε, Φ, hprod, fun t => (hformula _).trans (haxis t), ?_, ?_, hrecS, hrecT,
      hΦΨ.trans hΨO⟩
  · filter_upwards [hgl] with z hz
    exact (hformula z).trans hz
  · filter_upwards [hgr] with z hz
    exact (hformula z).trans hz

theorem MorseCancellation.exists_relative_sheet_passages_with_normal_change {E M X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    {f : X → M} {g : Y → M} {b : Z → M} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g) (hfe : Topology.IsEmbedding f)
    (hge : Topology.IsEmbedding g) (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (Set.range f) (Set.range g)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hbx : f x ∉ Set.range b) (hby : g y ∉ Set.range b) (γ : Path (f x) (g y)) :
    ∃ Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source ∧
        ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source ∧
          Φ₀ 0 = f x ∧
            Φ₁ (1, 0) = g y ∧
              (∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                (∀ z ∈ Φ₁.source, Φ₁ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                  ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
                    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
                      0 < ε ∧
                        ∃ Φ :
                          PartialDiffeomorph
                            𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
                            𝓘(ℝ, E)
                            (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
                          ∃ A : LongitudinalTubeMotion Φ,
                            Set.Icc (0 : ℝ) 1 ×ˢ
                                  Metric.closedBall
                                    (0 :
                                      ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                                    ε ⊆
                                Φ.source ∧
                              Φ 0 = f x ∧
                                Φ (1, 0) = g y ∧
                                  ((Φ :
                                        (ℝ ×
                                            ((EuclideanSpace ℝ (Fin 2)) ×
                                              (EuclideanSpace ℝ (Fin 2)))) →
                                          M) =ᶠ[𝓝
                                        (0 :
                                          (ℝ ×
                                            ((EuclideanSpace ℝ (Fin 2)) ×
                                              (EuclideanSpace ℝ (Fin 2)))))]
                                      Φ₀) ∧
                                    ((Φ :
                                          (ℝ ×
                                              ((EuclideanSpace ℝ (Fin 2)) ×
                                                (EuclideanSpace ℝ (Fin 2)))) →
                                            M) =ᶠ[𝓝
                                          ((1 : ℝ),
                                            (0 :
                                              ((EuclideanSpace ℝ (Fin 2)) ×
                                                (EuclideanSpace ℝ (Fin 2)))))]
                                        linearTransverseChart (C.prodCongr R) Φ₁) ∧
                                      (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                                        (∀ z ∈ Φ.source,
                                            Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                                          Φ.target ⊆ (Set.range b)ᶜ ∧
                                            (∀ t z, z ∈ Set.range b → A.family (t, z) = z) ∧
                                              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                                  ∀ u : X,
                                                    ∀ v : Y,
                                                      A.family (t, f u) = g v ↔
                                                        t = A.time ∧ u = x ∧ v = y) ∧
                                                NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2))
                                                  (𝓡 2) 𝓘(ℝ, E)
                                                  (fun p : ℝ × X => A.family (p.1, f p.2)) g
                                                  (A.time, x) y := by
  have hx : f x ∉ Set.range g := fun h => (Set.disjoint_left.mp hdisj) ⟨x, rfl⟩ h
  have hy : g y ∉ Set.range f := fun h => (Set.disjoint_left.mp hdisj) h ⟨y, rfl⟩
  obtain
    ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, a, ha, hleft, hright, hemb, hi, hcount₀, hcount₁,
      haO⟩ :=
    exists_clean_two_sheet_arc_avoiding hf hg hfe hge hfi hgi hb hbc hdim x y hx hy hbx hby γ
  refine ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, ?_⟩
  intro C
  have hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, hrecf, hrecg, hΦO⟩ :=
    exists_clean_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright
      (isCompact_range hf.continuous).isClosed (isCompact_range hg.continuous).isClosed hrec₀
      hrec₁ hcount₀ hcount₁ hbc.isOpen_compl haO C
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, Metric.mem_closedBall_self hε.le⟩
  have h0 : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source :=
    hzero ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have hfx : Φ 0 = f x := (haxis 0).trans (hleft.eq_of_nhds.trans hΦx)
  have hgy : Φ (1, 0) = g y := (haxis 1).trans (hright.eq_of_nhds.trans hΦy)
  obtain ⟨A⟩ := nonempty_longitudinalTubeMotion Φ hzero
  refine
    ⟨R, ε, hε, Φ, A, hprod, hfx, hgy, hgl, hgr, hrecf, hrecg, hΦO, ?_,
      A.whole_sheet_crossing_iff hfe.injective hge.injective hdisj hrecf hrecg x y hfx hgy h0,
      A.whole_sheet_transverse (hf.mdifferentiable (by simp) x) (hg.mdifferentiable (by simp) y)
        (hfi x) (hgi y) hrecf hrecg hfx hgy h0⟩
  intro t z hz
  exact A.fixed_outside_target t z (fun h => hΦO h hz)

theorem MorseCancellation.LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs {U V E M X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace X] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞) (C : U ≃L[ℝ] U)
    (R : V ≃L[ℝ] V) {f : X → M} {x : X} (hf : ContinuousAt f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright :
      (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
        MorseCancellation.linearTransverseChart (C.prodCongr R) Φ₁) :
    (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)] fun p =>
      Φ₁ (Real.smoothTransition p.1 * A.destination, (C (Φ₀.symm (f p.2)).2.1, 0)) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : ContinuousAt a x :=
    (Φ₀.symm.contMDiffOn_toFun.continuousOn.continuousAt (Φ₀.open_target.mem_nhds hfx)).comp hf
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hat : Filter.Tendsto a (𝓝 x) (𝓝 (0 : W)) := by simpa only [ha0] using ha.tendsto
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ₀.target := hf.eventually (Φ₀.open_target.mem_nhds hfx)
  have hplane : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrec (a q) (Φ₀.map_target hq)).mp ⟨q, (Φ₀.right_inv hq).symm⟩
  have hat' : Filter.Tendsto (fun p : ℝ × X => a p.2) (𝓝 (A.time, x)) (𝓝 (0 : W)) :=
    hat.comp continuous_snd.continuousAt
  have hpair :
    Filter.Tendsto (fun p : ℝ × X => (p.1, a p.2)) (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) :=
    continuous_fst.continuousAt.prodMk_nhds hat'
  let z : ℝ × X → W := fun p => (Real.smoothTransition p.1 * A.destination, ((a p.2).2.1, 0))
  have hap : ContinuousAt (fun p : ℝ × X => a p.2) (A.time, x) :=
    ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha continuousAt_snd
  have hz : ContinuousAt z (A.time, x) :=
    ((Real.smoothTransition.continuous.continuousAt.comp continuousAt_fst).mul
          continuousAt_const).prodMk
      (hap.snd.fst.prodMk continuousAt_const)
  have hz0 : z (A.time, x) = (1, 0) := by
    simp only [z, A.time_value, ha0, Prod.fst_zero, Prod.snd_zero]
    rfl
  have hzt : Filter.Tendsto z (𝓝 (A.time, x)) (𝓝 ((1 : ℝ), (0 : U × V))) := by
    simpa only [hz0] using hz.tendsto
  filter_upwards [hpair.eventually (A.native_germ h0 A.time), hat'.eventually hleft,
    continuous_snd.continuousAt.eventually hfn, continuous_snd.continuousAt.eventually hplane,
    hzt.eventually hright] with p hm hl hf' hp hr
  have hpoint : Φ (a p.2) = f p.2 := hl.trans (Φ₀.right_inv hf')
  calc
    A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
      congrArg (fun y => A.family (p.1, y)) hpoint.symm
    _ = Φ ((a p.2).1 + Real.smoothTransition p.1 * A.destination, (a p.2).2) := hm
    _ = Φ (z p) := by
      apply congrArg Φ
      rw [hp.1, zero_add]
      exact Prod.ext rfl (Prod.ext rfl hp.2)
    _ = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (Φ₀.symm (f p.2)).2.1, 0)) := by
      change Φ (z p) = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, 0))
      rw [hr]
      change Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, R 0)) = _
      rw [map_zero]

theorem MorseCancellation.exists_centered_passage_clock {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D 0 = 0 ∧
        D 1 = 1 ∧
          D (1 / 2) = τ ∧
            StrictMono D ∧
              Set.MapsTo D (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ∧
                ((D : ℝ → ℝ) =ᶠ[𝓝 (1 / 2 : ℝ)] fun t => t + (τ - 1 / 2)) ∧
                  HasDerivAt (D : ℝ → ℝ) 1 (1 / 2) := by
  obtain ⟨D, hfix, hgerm, hpoint, hmono, -⟩ :=
    MorseRearrangement.exists_increasing_interval_translation
      (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by constructor <;> norm_num) hτ
  have h0 : D 0 = 0 := hfix 0 (by simp)
  have h1 : D 1 = 1 := hfix 1 (by simp)
  refine ⟨D, h0, h1, hpoint, hmono, ?_, hgerm, ?_⟩
  · intro t ht
    exact ⟨h0 ▸ hmono.monotone ht.1, h1 ▸ hmono.monotone ht.2⟩
  · exact ((hasDerivAt_id (1 / 2 : ℝ)).add_const (τ - 1 / 2)).congr_of_eventuallyEq hgerm

def MorseCancellation.passageNormalProduct {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] (c : ℝ)
    (hc : c ≠ 0) (C : U ≃L[ℝ] U) : (ℝ × U) ≃L[ℝ] (ℝ × U) :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.prodCongr C

theorem MorseCancellation.passageNormalProduct_det {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (c : ℝ) (hc : c ≠ 0) (C : U ≃L[ℝ] U) :
    (passageNormalProduct c hc C).toLinearMap.det = c * C.toLinearMap.det := by
  have hscale :
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap = c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    ext
    rfl
  change LinearMap.det ((LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap.prodMap C.toLinearMap) = _
  rw [LinearMap.det_prodMap, hscale, LinearMap.det_smul, Module.finrank_self, pow_one,
    LinearMap.det_id, mul_one]

theorem MorseCancellation.relative_normal_frame_det {U N : Type} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    (Q₀ Q₁ : (ℝ × U) ≃L[ℝ] (ℝ × U)) :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap.det =
      Q₀.toLinearMap.det⁻¹ * Q₁.toLinearMap.det := by
  have heq :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap =
      P.symm.toLinearMap.comp ((Q₀.symm.toLinearMap.comp Q₁.toLinearMap).comp P.toLinearMap) := by
    apply LinearMap.ext
    intro z
    change P.symm (Q₀.symm (B.symm (B (Q₁ (P z))))) = P.symm (Q₀.symm (Q₁ (P z)))
    rw [B.symm_apply_apply]
  rw [heq]
  have hconj := LinearMap.det_conj (Q₀.symm.toLinearMap.comp Q₁.toLinearMap) P.symm.toLinearEquiv
  calc
    _ = (Q₀.symm.toLinearMap.comp Q₁.toLinearMap).det := hconj
    _ = _ := by
      rw [LinearMap.det_comp]
      exact
        congrArg (fun t : ℝ => t * Q₁.toLinearMap.det) (LinearEquiv.det_coe_symm Q₀.toLinearEquiv)

theorem MorseCancellation.passage_normal_relative_det_neg {U N : Type} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (C : U ≃L[ℝ] U) (hC : C.toLinearMap.det < 0) :
    (((P.trans (passageNormalProduct c₁ hc₁.ne' C)).trans B).trans
          ((P.trans (passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ U))).trans
              B).symm).toLinearMap.det <
      0 := by
  rw [relative_normal_frame_det, passageNormalProduct_det, passageNormalProduct_det]
  change (c₀ * (LinearMap.id : U →ₗ[ℝ] U).det)⁻¹ * (c₁ * C.toLinearMap.det) < 0
  rw [LinearMap.det_id, mul_one]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hc₀) (mul_neg_of_pos_of_neg hc₁ hC)

theorem MorseCancellation.mfderiv_normal_trace_model {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {α : X → U} {x : X}
    (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hα0 : α x = 0) {η : ℝ → ℝ} {τ κ : ℝ}
    (hη : HasDerivAt η κ τ) (hη1 : η τ = 1) (C : U ≃L[ℝ] U) {G : (ℝ × U) → N}
    {B : (ℝ × U) →L[ℝ] N} (hG : HasFDerivAt G B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => G (η p.1 - 1, C (α p.2))) (τ, x) :
        (ℝ × U) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
          (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by
  have ht :=
    (hη.sub_const 1).hasFDerivAt.hasMFDerivAt.comp (τ, x)
      (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hu := C.hasFDerivAt.hasMFDerivAt.comp x hα.hasMFDerivAt
  have hu' := hu.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hpair :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × U) (fun p : ℝ × X => (η p.1 - 1, C (α p.2))) (τ, x)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
        (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by convert! ht.prodMk hu' using 1
  have hcenter : (η τ - 1, C (α x)) = (0 : ℝ × U) := by
    rw [hη1, hα0, map_zero, sub_self]
    rfl
  have hG' : HasFDerivAt G B (η τ - 1, C (α x)) := by rw [hcenter]; exact hG
  exact (hG'.hasMFDerivAt.comp (τ, x) hpair).mfderiv

theorem MorseCancellation.LongitudinalTubeMotion.normal_trace_mfderiv {U H X N : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H}
    [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞) (C : U ≃L[ℝ] U)
    (R : V ≃L[ℝ] V) {f : X → M} {x : X} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright :
      (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
        MorseCancellation.linearTransverseChart (C.prodCongr R) Φ₁)
    (n : M → N) (B : (ℝ × U) →L[ℝ] N)
    (hB : HasFDerivAt (fun z : ℝ × U => n (Φ₁ (1 + z.1, (z.2, 0)))) B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => n (A.family (p.1, f p.2))) (A.time, x) :
        (ℝ × U) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (deriv Real.smoothTransition A.time * A.destination)).prodMap
          (C.toContinuousLinearMap.comp
            (mfderiv I 𝓘(ℝ, U) (fun q : X => (Φ₀.symm (f q)).2.1) x))) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let α : X → U := P ∘ a
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x := (Φ₀.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x := P.differentiableAt.mdifferentiableAt.comp x ha
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hα0 : α x = 0 := by change P (a x) = 0; rw [ha0, map_zero]
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
          A.time).hasDerivAt.mul_const
      _
  let G : (ℝ × U) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  have htrace :=
    A.sheet_trace_germ_of_endpoint_germs Φ₀ Φ₁ C R hf.continuousAt h0 hΦ₀ hx hrec hleft hright
  have heq :
    (fun p : ℝ × X => n (A.family (p.1, f p.2))) =ᶠ[𝓝 (A.time, x)] fun p =>
      G (η p.1 - 1, C (α p.2)) := by
    filter_upwards [htrace] with p hp
    rw [hp]
    change n (Φ₁ (η p.1, (C (α p.2), 0))) = n (Φ₁ (1 + (η p.1 - 1), (C (α p.2), 0)))
    rw [show 1 + (η p.1 - 1) = η p.1 by ring]
  rw [heq.mfderiv_eq]
  exact MorseCancellation.mfderiv_normal_trace_model hα hα0 hη A.time_value C hB

theorem MorseCancellation.mfderiv_retime_unit_rate {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)) {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ)
    (hpoint : D σ = τ) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) :
        (ℝ × U) →L[ℝ] N) =
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) := by
  subst τ
  have hDmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D σ (ContinuousLinearMap.id ℝ ℝ) := by
    have hid : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) = ContinuousLinearMap.id ℝ ℝ := by
      ext
      simp
    have h := hD.hasFDerivAt
    change HasFDerivAt D (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) σ at h
    rw [hid] at h
    exact h.hasMFDerivAt
  have ht := hDmf.comp (σ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x))
  have hp :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (fun p : ℝ × X => (D p.1, p.2)) (σ, x)
      (ContinuousLinearMap.id ℝ (ℝ × U)) := by
    convert! ht.prodMk (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x)) using 1
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := hF
  have hc := (hF'.hasMFDerivAt.comp (σ, x) hp).mfderiv
  change
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) :
        (ℝ × U) →L[ℝ] N) =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) : (ℝ × U) →L[ℝ] N).comp
        (ContinuousLinearMap.id ℝ (ℝ × U)) at hc
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg (fun L : (ℝ × U) →L[ℝ] N => L z) hc

theorem MorseCancellation.fderiv_retimed_trace_parameter {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)) {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ)
    (hpoint : D σ = τ) (Ψ : PartialDiffeomorph 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) A (ℝ × X) ∞)
    (hΨ : (0 : A) ∈ Ψ.source) (hcenter : Ψ 0 = (σ, x)) :
    fderiv ℝ (fun z : A => F (D (Ψ z).1, (Ψ z).2)) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) : (ℝ × U) →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) Ψ 0) := by
  let G : ℝ × X → N := fun p => F (D p.1, p.2)
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := by
    rw [hpoint]
    exact hF
  have hG : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) :=
    hF'.comp (σ, x)
      ((hD.differentiableAt.mdifferentiableAt.comp (σ, x) mdifferentiableAt_fst).prodMk
        mdifferentiableAt_snd)
  have hG' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (Ψ 0) := by
    rw [hcenter]
    exact hG
  change fderiv ℝ (G ∘ Ψ) 0 = _
  rw [← mfderiv_eq_fderiv, mfderiv_comp 0 hG' (Ψ.mdifferentiableAt (by simp) hΨ), hcenter]
  rw [show
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) : (ℝ × U) →L[ℝ] N) =
        mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)
      from mfderiv_retime_unit_rate hF hD hpoint]
  rfl

theorem MorseCancellation.exists_shared_passage_frames {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N)
    (Q : (ℝ × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (hdim : Module.finrank ℝ N = 3)
    (hbij : Function.Bijective (B.comp (Q.toContinuousLinearMap.comp P))) :
    ∃ (P' : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2)))) (B' :
      (ℝ × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] N),
      P'.toContinuousLinearMap = P ∧ B'.toContinuousLinearMap = B := by
  have hPi : Function.Injective P := by
    intro x y hxy
    apply hbij.injective
    change B (Q (P x)) = B (Q (P y))
    rw [hxy]
  have hBs : Function.Surjective B := by
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact ⟨Q (P x), hx⟩
  have hdimP :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2))) := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  have hdimB : Module.finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2))) = Module.finrank ℝ N := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim]
  have hPb : Function.Bijective P :=
    ⟨hPi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimP).mp hPi⟩
  have hBb : Function.Bijective B :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimB).mpr hBs, hBs⟩
  exact
    ⟨(LinearEquiv.ofBijective P.toLinearMap hPb).toContinuousLinearEquiv,
      (LinearEquiv.ofBijective B.toLinearMap hBb).toContinuousLinearEquiv, rfl, rfl⟩

structure MorseCancellation.CenteredSheetPassage (E : Type*) {M : Type*} {X : Type*} {Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : X → M)
    (g : Y → M) (x : X) (y : Y) (O : Set M) where
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  avoids : support ⊆ Oᶜ
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ family
  zero : ∀ z, family (0, z) = z
  slices : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = family (t, z)
  fixedOutside : ∀ t z, z ∉ support → family (t, z) = z
  crossing :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y, family (t, f u) = g v ↔ t = 1 / 2 ∧ u = x ∧ v = y

def MorseCancellation.LongitudinalTubeMotion.centeredSheetPassage {E M X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ) (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hD0 : D 0 = 0) (hpoint : D (1 / 2) = A.time)
    (hinterval : Set.MapsTo D (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) {f : X → M} {g : Y → M}
    {x : X} {y : Y} {O : Set M} (havoid : Φ.target ⊆ Oᶜ)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ u : X, ∀ v : Y, A.family (t, f u) = g v ↔ t = A.time ∧ u = x ∧ v = y) :
    MorseCancellation.CenteredSheetPassage E f g x y O
    where
  family := fun p => A.family (D p.1, p.2)
  support := A.support
  compact_support := A.compact_support
  avoids := A.support_subset.trans havoid
  smooth := A.smooth.comp ((D.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  zero := by intro z; change A.family (D 0, z) = z; rw [hD0, A.zero]
  slices := fun t => A.slices (D t)
  fixedOutside := fun t z hz => A.fixedOutside (D t) z hz
  crossing := by
    intro t ht u v
    rw [hcross (D t) (hinterval ht) u v]
    constructor
    · rintro ⟨h, hu, hv⟩
      exact ⟨D.injective (h.trans hpoint.symm), hu, hv⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨hpoint, rfl, rfl⟩

theorem MorseCancellation.bijective_trace_normal_of_native_transverse {E M U H X V H' Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'} [TopologicalSpace Y]
    [ChartedSpace H' Y] [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {f : X → M} {g : Y → M} {n : M → N} {x : X} {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)) (hpoint : g y = f x)
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) f g x y)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp (mfderiv I' 𝓘(ℝ, E) g y) = 0)
    (hdim : Module.finrank ℝ U = Module.finrank ℝ N) :
    Function.Bijective (mfderiv I 𝓘(ℝ, N) (n ∘ f) x) := by
  let Q : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)
  let B : V →L[ℝ] E := mfderiv I' 𝓘(ℝ, E) g y
  let A : U →L[ℝ] E := mfderiv I 𝓘(ℝ, E) f x
  have hbij : Function.Bijective (Q.comp A) :=
    TransverseCoordinates.bijective_normal_comp Q B A hsurj
      (TransverseCoordinates.surjective_coprod_swap A B (htrans hpoint)) hzero hdim
  have hn' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (f x) := hpoint ▸ hn
  have hder : (mfderiv I 𝓘(ℝ, N) (n ∘ f) x : U →L[ℝ] N) = Q.comp A := by
    rw [mfderiv_comp x hn' hf, ← hpoint]
    rfl
  rw [hder]
  exact hbij

theorem MorseCancellation.hasFDerivAt_terminal_normal_factor {E M U V N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup U]
    [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N]
    [NormedSpace ℝ N] (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞)
    (hΦ : ((1 : ℝ), (0 : U × V)) ∈ Φ.source) {n : M → N}
    (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (1, 0))) :
    HasFDerivAt (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0))))
      (fderiv ℝ (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0)))) 0) 0 := by
  let Q : (ℝ × U) → ℝ × (U × V) := fun z => (1 + z.1, (z.2, 0))
  have hQ : ContDiff ℝ ∞ Q :=
    (contDiff_const.add contDiff_fst).prodMk (contDiff_snd.prodMk contDiff_const)
  have hQ0 : Q 0 = (1, 0) := by
    change ((1 : ℝ) + 0, ((0 : U), (0 : V))) = (1, 0)
    rw [add_zero]
    rfl
  have hΦ' : ContMDiffAt 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) ∞ Φ (Q 0) := by
    rw [hQ0]
    exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hΦ)
  have hn' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (Q 0)) := by rw [hQ0]; exact hn
  have hs : ContDiffAt ℝ ∞ (fun z : ℝ × U => n (Φ (Q z))) 0 :=
    (ContMDiffAt.comp (g := n) (f := fun z : ℝ × U => Φ (Q z)) 0 hn'
        (hΦ'.comp 0 hQ.contMDiff.contMDiffAt)).contDiffAt
  exact (hs.differentiableAt (by simp)).hasFDerivAt

theorem MorseCancellation.regular_below_pivot_of_regular_lower_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (q : ManifoldMorse.criticalPoints E f)
    {a : ℝ}
    (hband : ∀ y, f y ∈ Set.Icc a (S.lower q) → y ∉ ManifoldMorse.criticalPoints E f) :
    ∀ y, f y ∈ Set.Ico a (f q) → y ∉ ManifoldMorse.criticalPoints E f := by
  intro y hy hcrit
  by_cases hlow : f y ≤ S.lower q
  · exact hband y ⟨hy.1, hlow⟩ hcrit
  · have heq : y = q.val :=
      S.isolated q y hcrit ⟨(lt_of_not_ge hlow).le, hy.2.le.trans (S.value_lt_upper q).le⟩
    exact hy.2.ne (congrArg f heq)

theorem MorseCancellation.lower_window_le_of_radius_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : ManifoldMorse.SurgeryWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) : S.lower q ≤ T.lower q := by
  have hs : (T.data q).radius ^ 2 ≤ (S.data q).radius ^ 2 :=
    (sq_le_sq₀ (T.data q).radius_pos.le (S.data q).radius_pos.le).mpr hr
  exact sub_le_sub_left hs (f q)

theorem MorseCancellation.common_cut_band_of_smaller_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : ManifoldMorse.SurgeryWindows E f) (q : ManifoldMorse.criticalPoints E f)
    {a : ℝ} (hal : a < S.lower q)
    (hband : ∀ y, f y ∈ Set.Icc a (S.lower q) → y ∉ ManifoldMorse.criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) :
    a < T.lower q ∧
      ∀ y, f y ∈ Set.Icc a (T.lower q) → y ∉ ManifoldMorse.criticalPoints E f := by
  refine ⟨hal.trans_le (lower_window_le_of_radius_le S T q hr), ?_⟩
  intro y hy
  exact
    regular_below_pivot_of_regular_lower_band S q hband y
      ⟨hy.1, hy.2.trans_lt (T.lower_lt_value q)⟩

theorem MorseCancellation.higher_window_separation_of_value_order {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : ManifoldMorse.SurgeryWindows E f) (q p : ManifoldMorse.criticalPoints E f)
    (hhigh : S.upper q < f p) : T.upper q < f p :=
  (T.upper_lt_lower q p ((S.value_lt_upper q).trans hhigh)).trans (T.lower_lt_value p)

attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem MorseCancellation.canonicalMiddleMatrix_single_class_addition {M : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} [Nonempty M] {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (α Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a })) (q i : Fin n) (k : ℤ)
    (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass :
      middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass (α q)) :
    canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B Γ =
      canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B α *
        Matrix.transvection q i k := by
  refine eq_mul_transvection_of_columns _ _ q i k ?_ ?_
  · intro u
    simp only [canonicalMiddleMatrix, classCoordinateMatrix]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    simp only [canonicalMiddleMatrix, classCoordinateMatrix, hother j hji]

attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem MorseCancellation.SurgeryWindows.regular_before_first_middle_pivot {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {a : ℝ}
    (hcut :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z < 3 → f z < a)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (q : Fin n) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j)) :
    ∀ y, f y ∈ Set.Icc a (S.lower (p q)) → y ∉ ManifoldMorse.criticalPoints E f := by
  intro y hy hcrit
  let z : ManifoldMorse.criticalPoints E f := ⟨y, hcrit⟩
  have hlt : f z < f (p q) := hy.2.trans_lt (S.lower_lt_value (p q))
  have hle : MorseCancellation.nativeMorseIndex E f z ≤ 3 := (horder z (p q) hlt).trans_eq (hp q)
  have heq : MorseCancellation.nativeMorseIndex E f z = 3 := by
    apply Nat.le_antisymm hle
    by_contra hnot
    exact (hcut z (lt_of_not_ge hnot)).not_ge hy.1
  obtain ⟨j, hj⟩ := hcomplete z heq
  by_cases hjq : j = q
  · exact (ne_of_lt hlt) (congrArg f (congrArg Subtype.val (hj.symm.trans (congrArg p hjq))))
  · have hreverse : f (p q) < f z := by simpa only [hj] using hfirst j hjq
    exact hlt.not_gt hreverse

attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem MorseCancellation.low_index_cut_of_preserved_other_values {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {g : M → ℝ} {a : ℝ}
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hindices :
      ∀ z ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (houtside : ∀ z ∈ ManifoldMorse.criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z)
    (hcut : ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z < 3 → f z < a) :
    ∀ z : ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z < 3 → g z < a := by
  intro z hz
  let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
  have hidx : nativeMorseIndex E f zf < 3 := by
    rw [← hindices z zf.property]
    exact hz
  have hother : ∀ j, z.val ≠ (p j).val := by
    intro j hj
    have heq : zf = p j := Subtype.ext hj
    rw [heq, hp j] at hidx
    exact (lt_irrefl _ hidx)
  rw [houtside z zf.property hother]
  exact hcut zf hidx


attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
def MorseCancellation.regularCutHomologyEquiv {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a ≤ b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ b } 2 :=
  LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) 2)
    (regular_sublevel_inclusion_bijective hf hab hband 2)

theorem ManifoldMorse.MorseSurgeryData.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩


theorem MorseCancellation.consecutive_last_two_first_three {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f g : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (p : ManifoldMorse.criticalPoints E f) (hp : nativeMorseIndex E f p = 2)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hindices :
      ∀ z ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (hfixed :
      ∀ z ∈ ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 3 → g z = f z)
    (hcut :
      ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z < 3 → f z < S.upper p)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E g,
        g x < g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y)
    (q : ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hfirst :
      ∀ z : ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = 3 → z ≠ q → g q < g z) :
    ∀ z : ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q) := by
  let pg : ManifoldMorse.criticalPoints E g := ⟨p.val, hcrit.symm ▸ p.property⟩
  have hpg : nativeMorseIndex E g pg = 2 := (hindices p p.property).trans hp
  have hgp : g p = f p := hfixed p p.property (by omega)
  intro z hz
  have hle : nativeMorseIndex E g z ≤ 3 := (horder z q hz.2).trans_eq hq
  have hge : 2 ≤ nativeMorseIndex E g z := hpg.symm.trans_le (horder pg z hz.1)
  have hcases : nativeMorseIndex E g z = 2 ∨ nativeMorseIndex E g z = 3 := by omega
  rcases hcases with hi2 | hi3
  · let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
    have hfidx : nativeMorseIndex E f zf = 2 := (hindices z zf.property).symm.trans hi2
    have hgz : g z = f z := hfixed z zf.property (by change nativeMorseIndex E f zf ≠ 3; omega)
    have hvalue : f p < f z := by
      have hh := hz.1
      rwa [hgp, hgz] at hh
    have hupper : f z < S.upper p := hcut zf (by omega)
    have heq : z.val = p.val :=
      S.isolated p z zf.property ⟨((S.lower_lt_value p).trans hvalue).le, hupper.le⟩
    exact hvalue.ne (congrArg f heq).symm
  · have hne : z ≠ q := fun heq =>
      hz.2.ne (congrArg (fun x : ManifoldMorse.criticalPoints E g => g x) heq)
    exact (hfirst z hi3 hne).not_gt hz.2

theorem MorseCancellation.native_index_excluded_of_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) {k : ℕ} (hcount : nativeMorseCount E f k = 0) :
    ∀ z ∈ ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ k := by
  have hfinite :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

end
