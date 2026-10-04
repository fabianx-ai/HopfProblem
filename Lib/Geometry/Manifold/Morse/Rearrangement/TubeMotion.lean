/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Morse.Rearrangement.TransverseChart
public import Lib.Geometry.Manifold.Morse.Rearrangement.IntervalTranslation
public import Lib.Geometry.Manifold.Morse.Rearrangement.LongitudinalBlend
public import Lib.Geometry.Manifold.Morse.Rearrangement.SmoothTransition
/-!
# Longitudinal motions of a tube and sheet crossings

`MorseCancellation.LongitudinalTubeMotion Φ`, for a tube chart `Φ : ℝ × V → M`, is a smooth
family `family : ℝ × M → M` of diffeomorphisms, the identity at time `0`, with compact support
inside `Φ.target`, which in the chart is the longitudinal blend of an increasing profile
(fixed outside a box, moving `0` to `destination > 1`) with the time cutoff
`Real.smoothTransition`. It moves the axis point `Φ 0` along the axis
(`LongitudinalTubeMotion.native_axis`), reaching `Φ (1, 0)` exactly at the unique `time`
(`crossing_axis`, `unique_time`), and is fixed outside the tube (`fixed_outside_target`).
Existence: `nonempty_longitudinalTubeMotion`, from `exists_tube_support_box`,
`exists_increasing_interval_translation`, `longitudinalBlend_slices` and
`SupportedDiffeomorph.exists_supported_isotopy_extension`.

If two injective sheets `f : X → M`, `g : Y → M` with disjoint ranges meet the chart
`Φ : ℝ × (U × V) → M` exactly as the coordinate slices `{t = 0, z₂ = 0}` and `{t = 1, z₁ = 0}`,
then `family (t, f x) = g y` holds for `t ∈ Icc 0 1` iff `t = time`, `x = x₀`, `y = y₀`
(`whole_sheet_crossing_iff`): the moved sheet meets the other sheet in a single point, and
transversally there (`whole_sheet_transverse`, through
`surjective_sheet_coordinate_mfderiv` and `native_coordinate_plane_trace_transverse`).

This is the local model of the Whitney trick: an isotopy supported near an arc creates one
transverse intersection point of two sheets (Milnor, *Lectures on the h-cobordism theorem*,
§6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Longitudinal tube motions -/

/-- A supported longitudinal motion of a tube preserving its axis and germ data. -/
structure MorseCancellation.LongitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) where
  profile : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
  cutoff : V → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_germ : cutoff =ᶠ[𝓝 (0 : V)] fun _ => 1
  cutoff_zero : cutoff 0 = 1
  destination : ℝ
  destination_gt_one : 1 < destination
  profile_zero : profile 0 = destination
  profile_germ : (profile : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] fun s => s + destination
  time : ℝ
  time_mem : time ∈ Set.Ioo (0 : ℝ) 1
  time_value : Real.smoothTransition time * destination = 1
  time_rate : 0 < deriv Real.smoothTransition time * destination
  unique_time : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.smoothTransition t * destination = 1 ↔ t = time
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  support_subset : support ⊆ Φ.target
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ y, family (0, y) = y
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = family (t, y)
  fixedOutside : ∀ t y, y ∉ support → family (t, y) = y
  model_source :
    ∀ t z, z ∈ Φ.source → longitudinalBlend profile cutoff Real.smoothTransition (t, z) ∈ Φ.source
  formula :
    ∀ t z,
      z ∈ Φ.source →
        family (t, Φ z) = Φ (longitudinalBlend profile cutoff Real.smoothTransition (t, z))

/-- The trivial longitudinal tube motion exists. -/
theorem MorseCancellation.nonempty_longitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ V]
    [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) : Nonempty (LongitudinalTubeMotion Φ) := by
  obtain ⟨l, u, r, hl, hu, hr, hbox⟩ := exists_tube_support_box Φ haxis
  let c : ℝ := (1 + u) / 2
  have hc : 1 < c := by dsimp only [c]; linarith
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcu : c < u := by dsimp only [c]; linarith
  have h0I : (0 : ℝ) ∈ Set.Ioo l u := ⟨hl, zero_lt_one.trans hu⟩
  have hcI : c ∈ Set.Ioo l u := ⟨hl.trans hcpos, hcu⟩
  obtain ⟨D, hDfix, hDgerm, hD0, -, hDpos⟩ :=
    MorseRearrangement.exists_increasing_interval_translation h0I hcI
  let β : ContDiffBump (0 : V) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβgerm : (β : V → ℝ) =ᶠ[𝓝 (0 : V)] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : V) β.rIn_pos] with z hz
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  have hβrange : ∀ z : V, β z ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨β.nonneg, β.le_one⟩
  have hηrange : ∀ t : ℝ, Real.smoothTransition t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hmodel :=
    longitudinalBlend_smooth D.contMDiff.contDiff β.contDiff
      (Real.smoothTransition.contDiff (n := ⊤))
  have hsource : Set.Icc l u ×ˢ tsupport (β : V → ℝ) ⊆ Φ.source := by
    rw [β.tsupport_eq]
    exact hbox
  obtain ⟨F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hsrc, hformula⟩ :=
    SupportedDiffeomorph.exists_supported_isotopy_extension Φ hmodel
      (longitudinalBlend_zero Real.smoothTransition.zero)
      (longitudinalBlend_slices D.contMDiff.contDiff β.contDiff β.hasCompactSupport hDpos hDfix
        hβrange hηrange)
      (CompactIccSpace.isCompact_Icc.prod β.hasCompactSupport.isCompact) hsource
      (longitudinalBlend_fixed_outside Real.smoothTransition hDfix)
  have hcInv : 1 / c ∈ Set.Ioo (0 : ℝ) 1 := ⟨one_div_pos.mpr hcpos, (div_lt_one hcpos).mpr hc⟩
  obtain ⟨τ, hτ, hτvalue, hτrate, hτunique⟩ := Real.smoothTransition.exists_unique_eq_of_mem_Ioo hcInv
  refine
    ⟨{  profile := D
        cutoff := β
        cutoff_smooth := β.contDiff
        cutoff_germ := hβgerm
        cutoff_zero := hβgerm.self_of_nhds
        destination := c
        destination_gt_one := hc
        profile_zero := hD0
        profile_germ := by simpa only [sub_zero] using hDgerm
        time := τ
        time_mem := hτ
        time_value := (eq_div_iff hcpos.ne').mp hτvalue
        time_rate := mul_pos hτrate hcpos
        unique_time := ?_
        family := F
        support := K
        compact_support := hK
        support_subset := hKΦ
        smooth := hF
        zero := hF0
        slices := hFd
        fixedOutside := hFfix
        model_source := hsrc
        formula := hformula }⟩
  intro t ht
  rw [← eq_div_iff hcpos.ne']
  exact hτunique t ht

/-- The model motion fixes the axis. -/
theorem MorseCancellation.LongitudinalTubeMotion.model_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancellation.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, (0, 0)) =
      (Real.smoothTransition t * A.destination, 0) := by
  simp only [MorseCancellation.longitudinalBlend, MorseCancellation.longitudinalBlendDisplacement,
    A.cutoff_zero, A.profile_zero, mul_one, sub_zero, zero_add]

/-- The model motion has the prescribed axis germ. -/
theorem MorseCancellation.LongitudinalTubeMotion.model_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancellation.longitudinalBlend A.profile A.cutoff Real.smoothTransition =ᶠ[𝓝 (t, (0, 0))]
      fun p : ℝ × (ℝ × V) => (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.1) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_fst.continuousAt.comp continuous_snd.continuousAt
  have hz : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.2) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_snd.continuousAt.comp continuous_snd.continuousAt
  filter_upwards [hs.eventually A.profile_germ, hz.eventually A.cutoff_germ] with p hp hβ
  simp only [MorseCancellation.longitudinalBlend, MorseCancellation.longitudinalBlendDisplacement, hp, hβ,
    mul_one, add_sub_cancel_left]

/-- The native motion fixes the chart axis. -/
theorem MorseCancellation.LongitudinalTubeMotion.native_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    A.family (t, Φ 0) = Φ (Real.smoothTransition t * A.destination, 0) := by
  rw [A.formula t 0 h0]
  exact congrArg Φ (A.model_axis t)

/-- The native motion has the prescribed axis germ. -/
theorem MorseCancellation.LongitudinalTubeMotion.native_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    (fun p : ℝ × (ℝ × V) => A.family (p.1, Φ p.2)) =ᶠ[𝓝 (t, 0)] fun p =>
      Φ (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : ∀ᶠ p : ℝ × (ℝ × V) in 𝓝 (t, 0), p.2 ∈ Φ.source :=
    continuous_snd.continuousAt.eventually (Φ.open_source.mem_nhds h0)
  filter_upwards [A.model_germ t, hs] with p hp hs
  rw [A.formula p.1 p.2 hs, hp]

/-- The motion is fixed outside the target tube. -/
theorem MorseCancellation.LongitudinalTubeMotion.fixed_outside_target {V E H M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (t : ℝ) (y : M) (hy : y ∉ Φ.target) : A.family (t, y) = y :=
  A.fixedOutside t y (fun h => hy (A.support_subset h))

/-- The moved axis point where the sheet crosses. -/
theorem MorseCancellation.LongitudinalTubeMotion.crossing_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) : A.family (A.time, Φ 0) = Φ (1, 0) := by
  rw [A.native_axis h0, A.time_value]

/-- The whole sheet crosses the level exactly at the crossing axis. -/
theorem MorseCancellation.LongitudinalTubeMotion.whole_sheet_crossing_iff {U V E H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M}
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (x₀ : X) (y₀ : Y)
    (hx₀ : Φ 0 = f x₀) (hy₀ : Φ (1, 0) = g y₀) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : X) (y : Y) :
    A.family (t, f x) = g y ↔ t = A.time ∧ x = x₀ ∧ y = y₀ := by
  constructor
  · intro he
    have htarget : f x ∈ Φ.target := by
      by_contra hn
      have hxy : f x = g y := (A.fixed_outside_target t (f x) hn).symm.trans he
      exact (Set.disjoint_left.mp hdisj) ⟨x, rfl⟩ ⟨y, hxy.symm⟩
    let z := Φ.symm (f x)
    have hz : z ∈ Φ.source := Φ.map_target htarget
    have hzfx : Φ z = f x := Φ.right_inv htarget
    have hfz := (hrecf z hz).mp ⟨x, hzfx.symm⟩
    let w := MorseCancellation.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, z)
    have hw : w ∈ Φ.source := A.model_source t z hz
    have hwgy : Φ w = g y := by
      calc
        Φ w = A.family (t, Φ z) := (A.formula t z hz).symm
        _ = A.family (t, f x) := (congrArg (fun p => A.family (t, p)) hzfx)
        _ = g y := he
    have hgw := (hrecg w hw).mp ⟨y, hwgy.symm⟩
    have hu : z.2.1 = 0 := hgw.2
    have hz0 : z = 0 := Prod.ext hfz.1 (Prod.ext hu hfz.2)
    have hwaxis : w = (Real.smoothTransition t * A.destination, 0) := by
      dsimp only [w]
      rw [hz0]
      exact A.model_axis t
    have htimevalue : Real.smoothTransition t * A.destination = 1 :=
      (congrArg Prod.fst hwaxis).symm.trans hgw.1
    have htτ : t = A.time := (A.unique_time t ht).mp htimevalue
    have hx : x = x₀ := hfi (hzfx.symm.trans ((congrArg Φ hz0).trans hx₀))
    have hwy : Φ w = g y₀ := by
      rw [hwaxis, htimevalue]
      exact hy₀
    exact ⟨htτ, hx, hgi (hwgy.symm.trans hwy)⟩
  · rintro ⟨ht, hx, hy⟩
    rw [ht, hx, hy]
    calc
      A.family (A.time, f x₀) = A.family (A.time, Φ 0) :=
        congrArg (fun p => A.family (A.time, p)) hx₀.symm
      _ = Φ (1, 0) := (A.crossing_axis h0)
      _ = g y₀ := hy₀

/-- The sheet coordinate derivative is surjective along the axis. -/
theorem MorseCancellation.surjective_sheet_coordinate_mfderiv {U W H X : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (P : W →L[ℝ] U) (Q : U →L[ℝ] W) (b : W) {a : X → W} {x : X}
    (ha : MDifferentiableAt I 𝓘(ℝ, W) a x) (hi : Function.Injective (mfderiv I 𝓘(ℝ, W) a x))
    (hgerm : a =ᶠ[𝓝 x] fun y => Q (P (a y)) + b) :
    Function.Surjective (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) := by
  have hP : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, U) P (a x) := P.differentiableAt.mdifferentiableAt
  have hα := hP.comp x ha
  have hQ : HasMFDerivAt 𝓘(ℝ, U) 𝓘(ℝ, W) (fun u => Q u + b) (P (a x)) Q :=
    (Q.hasFDerivAt.add_const b).hasMFDerivAt
  have heq : (mfderiv I 𝓘(ℝ, W) a x : U →L[ℝ] W) = Q.comp (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) :=
    hgerm.mfderiv_eq.trans (hQ.comp x hα.hasMFDerivAt).mfderiv
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) (P ∘ a) x
  change Function.Surjective D
  apply (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp
  intro u v huv
  apply hi
  rw [heq]
  exact congrArg Q huv

/-- The native coordinate plane traces the sheet transversely. -/
theorem MorseCancellation.native_coordinate_plane_trace_transverse {U H X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] {V H' Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] {α : X → U} {β : Y → V} {x : X} {y : Y} {η : ℝ → ℝ}
    {τ κ : ℝ} (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y)
    (hαs : Function.Surjective (mfderiv I 𝓘(ℝ, U) α x))
    (hβs : Function.Surjective (mfderiv I' 𝓘(ℝ, V) β y)) (hη : HasDerivAt η κ τ) (hκ : κ ≠ 0) :
    NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, ℝ × (U × V))
      (fun p : ℝ × X => (η p.1, (α p.2, 0))) (fun q : Y => (1, (0, β q))) (τ, x) y := by
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) α x
  let E : V →L[ℝ] V := mfderiv I' 𝓘(ℝ, V) β y
  let C : (ℝ × U) →L[ℝ] ℝ :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).comp (ContinuousLinearMap.fst ℝ ℝ U)
  let L : (ℝ × U) →L[ℝ] ℝ × (U × V) := C.prod ((D.comp (ContinuousLinearMap.snd ℝ ℝ U)).prod 0)
  let R : V →L[ℝ] ℝ × (U × V) := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod E)
  have htime :=
    hη.hasFDerivAt.hasMFDerivAt.comp (τ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hcoord := hα.hasMFDerivAt.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) (fun _ : ℝ × X => (0 : V)) (τ, x) 0 :=
    hasMFDerivAt_const _ _
  have hT :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × (U × V)) (fun p : ℝ × X => (η p.1, (α p.2, (0 : V))))
      (τ, x) L := by convert! htime.prodMk (hcoord.prodMk hzero) using 1
  have hone : HasMFDerivAt I' 𝓘(ℝ, ℝ) (fun _ : Y => (1 : ℝ)) y 0 := hasMFDerivAt_const _ _
  have hz : HasMFDerivAt I' 𝓘(ℝ, U) (fun _ : Y => (0 : U)) y 0 := hasMFDerivAt_const _ _
  have hB : HasMFDerivAt I' 𝓘(ℝ, ℝ × (U × V)) (fun q : Y => ((1 : ℝ), ((0 : U), β q))) y R := by
    convert! hone.prodMk (hz.prodMk hβ.hasMFDerivAt) using 1
  intro _
  rw [hT.mfderiv, hB.mfderiv]
  change Function.Surjective (L.coprod R)
  rintro ⟨s, u, v⟩
  obtain ⟨a, ha⟩ := hαs u
  obtain ⟨b, hb⟩ := hβs v
  refine ⟨((s / κ, a), b), ?_⟩
  apply Prod.ext
  · change s / κ * κ + 0 = s
    rw [add_zero, div_mul_cancel₀ s hκ]
  · change (D a + 0, 0 + E b) = (u, v)
    rw [add_zero, zero_add]
    exact Prod.ext ha hb

/-- The whole moved sheet remains transverse to the level. -/
theorem MorseCancellation.LongitudinalTubeMotion.whole_sheet_transverse {U V E HU HV H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace H] {I : ModelWithCorners ℝ U HU}
    {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y]
    [ChartedSpace HV Y] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hfi : Function.Injective (mfderiv I J f x)) (hgi : Function.Injective (mfderiv I' J g y))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (hx : Φ 0 = f x)
    (hy : Φ (1, 0) = g y) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) :
    NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' J (fun p : ℝ × X => A.family (p.1, f p.2)) g
      (A.time, x) y := by
  let W := ℝ × (U × V)
  let a : X → W := Φ.symm ∘ f
  let b : Y → W := Φ.symm ∘ g
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let Q : U →L[ℝ] W := (0 : U →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ U).prod (0 : U →L[ℝ] V))
  let R : W →L[ℝ] V := (ContinuousLinearMap.snd ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let S : V →L[ℝ] W := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod (ContinuousLinearMap.id ℝ V))
  have h1 : ((1 : ℝ), (0 : U × V)) ∈ Φ.source := by
    have hh := A.model_source A.time ((0 : ℝ), (0 : U × V)) h0
    rw [A.model_axis, A.time_value] at hh
    exact hh
  have hfx : f x ∈ Φ.target := hx ▸ Φ.map_source h0
  have hgy : g y ∈ Φ.target := hy ▸ Φ.map_source h1
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x := (Φ.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hb : MDifferentiableAt I' 𝓘(ℝ, W) b y := (Φ.symm.mdifferentiableAt (by simp) hgy).comp y hg
  have hai : Function.Injective (mfderiv I 𝓘(ℝ, W) a x) := by
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hfx) hf]
    exact (PartialChart.bijective_mfderiv Φ.symm hfx).injective.comp hfi
  have hbi : Function.Injective (mfderiv I' 𝓘(ℝ, W) b y) := by
    rw [mfderiv_comp y (Φ.symm.mdifferentiableAt (by simp) hgy) hg]
    exact (PartialChart.bijective_mfderiv Φ.symm hgy).injective.comp hgi
  have ha0 : a x = 0 := (congrArg Φ.symm hx).symm.trans (Φ.left_inv h0)
  have hb1 : b y = (1, 0) := (congrArg Φ.symm hy).symm.trans (Φ.left_inv h1)
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ.target :=
    hf.continuousAt.eventually (Φ.open_target.mem_nhds hfx)
  have hgn : ∀ᶠ q in 𝓝 y, g q ∈ Φ.target :=
    hg.continuousAt.eventually (Φ.open_target.mem_nhds hgy)
  have hca : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrecf (a q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hcb : ∀ᶠ q in 𝓝 y, (b q).1 = 1 ∧ (b q).2.1 = 0 := by
    filter_upwards [hgn] with q hq
    exact (hrecg (b q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hagerm : a =ᶠ[𝓝 x] fun q => Q (P (a q)) + (0 : W) := by
    filter_upwards [hca] with q hq
    change a q = (0, ((a q).2.1, 0)) + (0 : W)
    rw [add_zero]
    exact Prod.ext hq.1 (Prod.ext rfl hq.2)
  have hbgerm : b =ᶠ[𝓝 y] fun q => S (R (b q)) + ((1 : ℝ), (0 : U × V)) := by
    filter_upwards [hcb] with q hq
    change b q = (0, (0, (b q).2.2)) + ((1 : ℝ), (0 : U × V))
    apply Prod.ext
    · change (b q).1 = 0 + 1
      simpa only [zero_add] using hq.1
    · apply Prod.ext
      · change (b q).2.1 = 0 + 0
        simpa only [zero_add] using hq.2
      · change (b q).2.2 = (b q).2.2 + 0
        exact (add_zero _).symm
  let α : X → U := P ∘ a
  let β : Y → V := R ∘ b
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x := P.differentiableAt.mdifferentiableAt.comp x ha
  have hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y := R.differentiableAt.mdifferentiableAt.comp y hb
  have hαs := MorseCancellation.surjective_sheet_coordinate_mfderiv P Q 0 ha hai hagerm
  have hβs := MorseCancellation.surjective_sheet_coordinate_mfderiv R S (1, 0) hb hbi hbgerm
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
          A.time).hasDerivAt.mul_const
      _
  let T : ℝ × X → W := fun p => (η p.1, (α p.2, 0))
  let B : Y → W := fun q => (1, (0, β q))
  have hT : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, W) T (A.time, x) :=
    (hη.differentiableAt.mdifferentiableAt.comp (A.time, x) mdifferentiableAt_fst).prodMk_space
      ((hα.comp (A.time, x) mdifferentiableAt_snd).prodMk_space mdifferentiableAt_const)
  have hB : MDifferentiableAt I' 𝓘(ℝ, W) B y :=
    mdifferentiableAt_const.prodMk_space (mdifferentiableAt_const.prodMk_space hβ)
  have hT0 : T (A.time, x) = (1, 0) := by
    change (η A.time, (P (a x), (0 : V))) = (1, 0)
    rw [ha0, map_zero]
    exact Prod.ext A.time_value rfl
  have hB0 : B y = (1, 0) := by
    change ((1 : ℝ), ((0 : U), R (b y))) = (1, 0)
    rw [hb1]
    rfl
  have hmodel : NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, W) T B (A.time, x) y :=
    MorseCancellation.native_coordinate_plane_trace_transverse hα hβ hαs hβs hη A.time_rate.ne'
  have hnative :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff Φ hT hB
          (hB0.trans hT0.symm) (hT0 ▸ h1)).mp
      hmodel
  have hq :
    Filter.Tendsto (fun p : ℝ × X => (p.1, a p.2)) (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) := by
    have hcont : ContinuousAt (fun p : ℝ × X => (p.1, a p.2)) (A.time, x) :=
      continuousAt_fst.prodMk
        (ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha.continuousAt continuousAt_snd)
    simpa only [ha0] using hcont.tendsto
  have hFgerm : (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)] (Φ ∘ T) := by
    filter_upwards [hq.eventually (A.native_germ h0 A.time),
      continuous_snd.continuousAt.eventually hfn, continuous_snd.continuousAt.eventually hca] with
      p hmove hp hplane
    have hpoint : Φ (a p.2) = f p.2 := Φ.right_inv hp
    calc
      A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
        congrArg (fun z => A.family (p.1, z)) hpoint.symm
      _ = Φ ((a p.2).1 + η p.1, (a p.2).2) := hmove
      _ = (Φ ∘ T) p := by
        apply congrArg Φ
        change ((a p.2).1 + η p.1, (a p.2).2) = (η p.1, ((a p.2).2.1, 0))
        rw [hplane.1, zero_add]
        exact Prod.ext rfl (Prod.ext rfl hplane.2)
  have hGgerm : g =ᶠ[𝓝 y] (Φ ∘ B) := by
    filter_upwards [hgn, hcb] with q hq hplane
    calc
      g q = Φ (b q) := (Φ.right_inv hq).symm
      _ = (Φ ∘ B) q := congrArg Φ (Prod.ext hplane.1 (Prod.ext hplane.2 rfl))
  intro _
  rw [hFgerm.mfderiv_eq, hGgerm.mfderiv_eq]
  exact hnative (congrArg Φ (hB0.trans hT0.symm))
