/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Connection.MinimumBasins

/-!
# Belt arcs and meridians of a handle

Let `S : AdaptedWindows E f` be surgery windows adapted to a descent field and `q` a critical
point with split Morse chart `(S.data q).chart`.

* `nativeBeltArc S q u v s`: the arc `s ↦ splitChart.symm (BeltPassage.upper radius s u v)` in
  the upper level through the belt-sphere point `v`; it has constant height
  (`nativeBeltArc_height`), passes through the belt sphere only at `s = 0`
  (`nativeBeltArc_zero`, `nativeBeltArc_belt_eq_iff`), is injective on `[-1, 1]`
  (`nativeBeltArc_injOn`) and smooth on `(-1, 1)` (`nativeBeltArc_contMDiffOn`).
* `nativeLowerMeridianFamily`, `nativeLowerMeridian S q v s`: a family of maps of the attaching
  sphere into the lower level, equal to the attaching sphere at `s = 0`
  (`nativeLowerMeridian_zero`) and homotopic to it (`nativeLowerMeridian_homotopic_attaching`).
* `nativeUpperMeridian S q v s`: the corresponding maps into the upper level; the flow carries
  the upper meridian to the lower one (`nativeUpperMeridian_flow`) and the upper meridian avoids
  the belt sphere (`nativeUpperMeridian_avoids_belt`).

These arcs and meridians realise the intersection of the belt (right-hand) sphere of one handle
with the attaching (left-hand) sphere of the next; cf. Milnor, *Lectures on the h-cobordism
theorem*, §3 and §5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### The belt arc and meridians -/

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc through the native belt point. -/
def MorseCancellation.nativeBeltArc {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) : M :=
  (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius s u.val v.val)

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc coordinates land in the target. -/
theorem MorseCancellation.nativeBeltArc_coordinates_mem_target {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    BeltPassage.upper (S.data q).radius s u.val v.val ∈
      (S.data q).chart.splitChart.target :=
  (S.data q).block
    (BeltPassage.upper_mem_block (S.data q).radius_pos hs
      (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property))

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc's height. -/
theorem MorseCancellation.nativeBeltArc_height {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    f (nativeBeltArc S q u v s) = S.toSurgeryWindows.upper q := by
  rw [nativeBeltArc,
    (S.data q).chart.splitChart_inverse_equation
      (nativeBeltArc_coordinates_mem_target S q u v hs)]
  have hh :=
    BeltPassage.upper_height (S.data q).radius s (mem_sphere_zero_iff_norm.mp u.property)
      (mem_sphere_zero_iff_norm.mp v.property)
  change
    -‖(BeltPassage.upper (S.data q).radius s u.val v.val).1‖ ^ 2 +
        ‖(BeltPassage.upper (S.data q).radius s u.val v.val).2‖ ^ 2 =
      (S.data q).radius ^ 2 at hh
  dsimp only [ManifoldMorse.SurgeryWindows.upper]
  linarith

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc at zero. -/
theorem MorseCancellation.nativeBeltArc_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeBeltArc S q u v 0 = ((S.data q).surgery.beltSphere v).val := by
  rw [nativeBeltArc, BeltPassage.upper_zero, (S.data q).belt_eq,
    (S.data q).chart.beltCoreMap_coe]

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc hits the belt sphere exactly at zero. -/
theorem MorseCancellation.nativeBeltArc_belt_eq_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v w : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val ↔ s = 0 ∧ v = w := by
  constructor
  · intro heq
    have hzero := nativeBeltArc_coordinates_mem_target S q u w (s := 0) (by simp)
    rw [BeltPassage.upper_zero] at hzero
    rw [nativeBeltArc, (S.data q).belt_eq, (S.data q).chart.beltCoreMap_coe] at heq
    have hcoords :=
      (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
        (nativeBeltArc_coordinates_mem_target S q u v hs) hzero heq
    have hu : u.val ≠ 0 := by
      intro h
      have hn := mem_sphere_zero_iff_norm.mp u.property
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    have hs0 : s = 0 := by
      have hfst : ((S.data q).radius * s) • u.val = 0 := congrArg Prod.fst hcoords
      have hz : (S.data q).radius * s = 0 := (smul_eq_zero.mp hfst).resolve_right hu
      exact (mul_eq_zero.mp hz).resolve_left (S.data q).radius_pos.ne'
    refine ⟨hs0, ?_⟩
    rw [hs0, BeltPassage.upper_zero] at hcoords
    exact
      Subtype.ext (smul_right_injective _ (S.data q).radius_pos.ne' (congrArg Prod.snd hcoords))
  · rintro ⟨rfl, rfl⟩
    exact nativeBeltArc_zero S q u v

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc is injective. -/
theorem MorseCancellation.nativeBeltArc_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    Set.InjOn (nativeBeltArc S q u v) (Set.Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  have hcoords :=
    (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
      (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr hs))
      (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ht)) hst
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hfst : ((S.data q).radius * s) • u.val = ((S.data q).radius * t) • u.val :=
    congrArg Prod.fst hcoords
  exact mul_left_cancel₀ (S.data q).radius_pos.ne' (smul_left_injective ℝ hu hfst)

attribute [local instance 100] Classical.propDecidable in
/-- The belt arc is smooth. -/
theorem MorseCancellation.nativeBeltArc_contMDiffOn {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (nativeBeltArc S q u v) (Set.Ioo (-1 : ℝ) 1) := by
  apply
    (S.data q).chart.splitChart.contMDiffOn_invFun.comp
      (BeltPassage.contDiff_upper (S.data q).radius u.val v.val).contMDiff.contMDiffOn
  intro s hs
  exact nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

/-- The lower meridian's coordinates land in the target. -/
theorem MorseCancellation.nativeLowerMeridian_coordinates_mem_target {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    BeltPassage.lower (S.data q).radius s u.val v.val ∈
      (S.data q).chart.splitChart.target := by
  have hh :=
    BeltPassage.upper_mem_block (S.data q).radius_pos
      (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)
      (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  exact (S.data q).block ⟨hh.2, hh.1⟩

/-- The lower meridian's height. -/
theorem MorseCancellation.nativeLowerMeridian_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    f
        ((S.data q).chart.splitChart.symm
          (BeltPassage.lower (S.data q).radius s u.val v.val)) =
      S.toSurgeryWindows.lower q := by
  rw [(S.data q).chart.splitChart_inverse_equation
      (nativeLowerMeridian_coordinates_mem_target S q u v s)]
  have hh :=
    BeltPassage.upper_height (S.data q).radius (s : ℝ)
      (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  change
    -‖(BeltPassage.lower (S.data q).radius s u.val v.val).2‖ ^ 2 +
        ‖(BeltPassage.lower (S.data q).radius s u.val v.val).1‖ ^ 2 =
      (S.data q).radius ^ 2 at hh
  dsimp only [ManifoldMorse.SurgeryWindows.lower]
  linarith

/-- The lower meridian family under the flow. -/
def MorseCancellation.nativeLowerMeridianFamily {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    C(unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      (S.data q).LowerLevel)
    where
  toFun
    z :=
    ⟨(S.data q).chart.splitChart.symm
        (BeltPassage.lower (S.data q).radius z.1 z.2.val v.val),
      nativeLowerMeridian_height S q z.2 v z.1⟩
  continuous_toFun := by
    have hsize :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hdir :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hcoords :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          BeltPassage.lower (S.data q).radius (z.1 : ℝ) z.2.val v.val) := by
      unfold BeltPassage.lower
      exact
        ((continuous_const.mul
                  (Real.continuous_sqrt.comp (continuous_const.add (hsize.pow 2)))).smul
              hdir).prodMk
          ((continuous_const.mul hsize).smul continuous_const)
    exact
      ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hcoords
            (fun z => nativeLowerMeridian_coordinates_mem_target S q z.2 v z.1)).subtype_mk
        _

/-- The lower meridian of the native handle. -/
def MorseCancellation.nativeLowerMeridian {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).LowerLevel) :=
  (nativeLowerMeridianFamily S q v).comp ((ContinuousMap.const _ s).prodMk (ContinuousMap.id _))

/-- The upper meridian of the native handle. -/
def MorseCancellation.nativeUpperMeridian {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).UpperLevel)
    where
  toFun
    u :=
    ⟨nativeBeltArc S q u v s,
      nativeBeltArc_height S q u v (by rw [abs_of_nonneg s.property.1]; exact s.property.2)⟩
  continuous_toFun := by
    have hcoords :
      Continuous
        (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          BeltPassage.upper (S.data q).radius (s : ℝ) u.val v.val) := by
      unfold BeltPassage.upper
      have hneg :
        Continuous
          (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
            ((S.data q).radius * (s : ℝ)) • u.val) :=
        (continuous_subtype_val :
              Continuous
                (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
                  u.val)).const_smul
          ((S.data q).radius * (s : ℝ))
      have hpos :
        Continuous
          (fun _ : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
            ((S.data q).radius * Real.sqrt (1 + (s : ℝ) ^ 2)) • v.val) :=
        continuous_const
      exact hneg.prodMk hpos
    exact
      ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hcoords
            (fun u =>
              nativeBeltArc_coordinates_mem_target S q u v
                (by rw [abs_of_nonneg s.property.1]; exact s.property.2))).subtype_mk
        _

/-- The lower meridian at zero. -/
theorem MorseCancellation.nativeLowerMeridian_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeLowerMeridian S q v 0 = (S.data q).surgery.attachingSphere := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm (BeltPassage.lower (S.data q).radius 0 u.val v.val) =
      _
  rw [BeltPassage.lower_zero, (S.data q).attaching_eq,
    (S.data q).chart.attachingCoreMap_coe]

/-- The upper meridian is the flow of the lower meridian. -/
theorem MorseCancellation.nativeUpperMeridian_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    S.flow (BeltPassage.time s) ((nativeUpperMeridian S q v s) u).val =
      ((nativeLowerMeridian S q v s) u).val :=
  S.flow_belt_passage q hs s.property.2 u v

/-- The lower meridian is homotopic to the attaching sphere. -/
theorem MorseCancellation.nativeLowerMeridian_homotopic_attaching {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    (nativeLowerMeridian S q v s).Homotopic (S.data q).surgery.attachingSphere := by
  let shrink : C(unitInterval, unitInterval) :=
    ⟨fun t => unitInterval.symm t * s, unitInterval.continuous_symm.mul continuous_const⟩
  have h0 : shrink 0 = s := by simp [shrink]
  have h1 : shrink 1 = 0 := by simp [shrink]
  let H : (nativeLowerMeridian S q v s).Homotopy (S.data q).surgery.attachingSphere :=
    { toFun := fun z => nativeLowerMeridianFamily S q v (shrink z.1, z.2)
      continuous_toFun :=
        (nativeLowerMeridianFamily S q v).continuous.comp
          ((shrink.continuous.comp continuous_fst).prodMk continuous_snd)
      map_zero_left := by
        intro u
        rw [h0]
        rfl
      map_one_left := by
        intro u
        rw [h1]
        exact
          congrArg
            (fun g :
                C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                  (S.data q).LowerLevel) =>
              g u)
            (nativeLowerMeridian_zero S q v) }
  exact ⟨H⟩

/-- The upper meridian avoids the belt sphere. -/
theorem MorseCancellation.nativeUpperMeridian_avoids_belt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    nativeUpperMeridian S q v s u ∉ Set.range (S.data q).surgery.beltSphere := by
  rintro ⟨w, hw⟩
  have he :=
    (nativeBeltArc_belt_eq_iff S q u v w
          (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)).mp
      (congrArg Subtype.val hw.symm)
  exact hs.ne' he.1

end
