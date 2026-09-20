/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.RankThreeModel
import Lib.Geometry.Manifold.Morse.BeltCancellation

/-!
# Belt-sphere cancellation: lower transport and the radial parameter chart (proof-specific)

Proof-specific material of the six-sphere formalization: this module is not library
mathematics and is not registered in `Lib.lean`.  It is the part of
`Lib.Geometry.Manifold.Morse.BeltCancellation` that the round-7 audit graded D and that no
`Lib` module consumes, so it can be returned to `Hopf/Proof/`:

* `AdaptedWindows.belt_complement_reaches_lower_level`,
  `exists_belt_complement_lower_transport`, `exists_lower_transport_with_meridians`,
  `exists_lower_passage_homology_relation` and
  `MorseCancellation.lower_transport_upperMeridian_eq`: the transport of the complement of a
  belt sphere down to a lower regular level and the homology relation it produces, all stated
  for the project's `AdaptedWindows E f` in the dimension-`6`, index-`2` instance;
* `MorseCancellation.radialParameterChart` and its four computation lemmas
  (`radialParameterChart_zero_mem_source`, `radialParameterChart_zero`,
  `radialParameterChart_apply`, `radialParameterChart_link`): the chart on
  `Hemisphere.Sphere 2` used by the project's passage-homology computation.

The rest of `BeltCancellation` stays in `Lib` only because the `Lib` module
`Lib.Geometry.Manifold.Morse.SurgeryCollapse` consumes it.

Moved verbatim from `Hopf/SingularHomology.lean` via
`Lib/Geometry/Manifold/Morse/BeltCancellation.lean`; statements unchanged.
-/
open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

universe u v

noncomputable section


theorem AdaptedWindows.belt_complement_reaches_lower_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (y : (S.data p).UpperLevel) (hy : y ∉ Set.range (S.data p).surgery.beltSphere) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨a, ha, b, hb, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hyreg : y.val ∉ ManifoldMorse.criticalPoints E f :=
    (S.data p).upper_regular y.val y.property
  have hbelow : f b < S.toSurgeryWindows.lower p := by
    rcases lt_trichotomy (f b) (f p) with h | h | h
    · exact (S.toSurgeryWindows.value_lt_upper ⟨b, hb⟩).trans (S.separated ⟨b, hb⟩ p h)
    · have heq : b = p.val := S.distinct hb p.property h
      subst b
      exact (hy ((S.belt_basin_iff hf p y).mp hforward)).elim
    · have hup : f y.val < f b := by
        rw [y.property]
        exact (S.separated p ⟨b, hb⟩ h).trans (S.toSurgeryWindows.lower_lt_value ⟨b, hb⟩)
      exact (not_lt_of_ge hup.le (hheights hyreg).1).elim
  have hlow : S.toSurgeryWindows.lower p < f y.val := by
    rw [y.property]
    exact (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hlow.trans (hheights hyreg).2) hbelow

theorem AdaptedWindows.exists_belt_complement_lower_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  obtain ⟨P, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
  have hsrc (x : ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel)) :
    x.val ∈ P.source := hsource.symm ▸ S.belt_complement_reaches_lower_level hf p x.val x.property
  let D :
    C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
      (S.data p).LowerLevel) :=
    ⟨fun x => P x.val,
      P.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val hsrc⟩
  refine ⟨D, fun x => horbit x.val (hsrc x), ?_⟩
  intro x y t hty
  obtain ⟨s, hs⟩ := horbit x.val (hsrc x)
  have hshared : S.flow 0 (D x).val = S.flow (s - t) y.val := by
    rw [S.flow.map_zero_apply]
    change (P x.val).val = S.flow (s - t) y.val
    rw [← hs, ← hty, ← S.flow.map_add, sub_add_cancel]
  apply Subtype.ext
  exact
    MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z ((S.data p).lower_regular z hz)) (D x).property y.property hshared


theorem MorseCancellation.lower_transport_upperMeridian_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (p : ManifoldMorse.criticalPoints E f)
    (D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel))
    (hD : ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    D.comp (nativeUpperMeridianInComplement S p v s hs) = nativeLowerMeridian S p v s := by
  apply ContinuousMap.ext
  intro u
  exact
    hD (nativeUpperMeridianInComplement S p v s hs u) (nativeLowerMeridian S p v s u)
      (BeltPassage.time s) (nativeUpperMeridian_flow S p v s hs u)

theorem AdaptedWindows.exists_lower_transport_with_meridians {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          ∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
            (hs : 0 < (s : ℝ)),
            (D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w s hs)).Homotopic
              (S.data p).surgery.attachingSphere := by
  obtain ⟨D, horbit, hunique⟩ := S.exists_belt_complement_lower_transport hf p u v
  refine ⟨D, horbit, hunique, ?_⟩
  intro w s hs
  rw [MorseCancellation.lower_transport_upperMeridian_eq S p D hunique w s hs]
  exact MorseCancellation.nativeLowerMeridian_homotopic_attaching S p w s

theorem AdaptedWindows.exists_lower_passage_homology_relation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (H : C(ℝ × Hemisphere.Sphere 2, (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : Hemisphere.Sphere 2)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : Hemisphere.Sphere 2,
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          (∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
              (hs : 0 < (s : ℝ)),
              (D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w s hs)).Homotopic
                (S.data p).surgery.attachingSphere) ∧
            let G :=
              D.comp
                (PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            (∀ z : ({(τ, x₀)}ᶜ : Set (ℝ × Hemisphere.Sphere 2)),
                z.val.1 ∈ Set.Icc (0 : ℝ) 1 → ∃ t : ℝ, S.flow t (H z.val).val = (G z).val) ∧
              ∀ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
                SingularMayerVietoris.singularHomologyMap
                    (G.comp (PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
                  SingularMayerVietoris.singularHomologyMap
                      (G.comp (PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                    SingularMayerVietoris.singularHomologyMap
                      (G.comp (PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 := by
  obtain ⟨D, horbit, hunique, hmeridian⟩ := S.exists_lower_transport_with_meridians hf p u v
  refine ⟨D, horbit, hunique, hmeridian, ?_, ?_⟩
  · intro z hz
    have hh :=
      horbit
        (PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere)
          hτ x₀ hcross z)
    rw [PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross z hz] at hh
    exact hh
  · intro ε hε hεx
    exact
      PassageHomology.punctured_cylinder_trace_relation hτ x₀ hε hεx
        (D.comp
          (PassageHomology.puncturedPassageTrace H
            (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross))
        2 (by decide)


def MorseCancellation.radialParameterChart (τ : ℝ) (u : (Hemisphere.Sphere 2)) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) (EuclideanSpace ℝ (Fin 3))
      (ℝ × (Hemisphere.Sphere 2)) ∞ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let b := PassageHomology.cylinderPuncture τ u
  let T : Diffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toEquiv :=
        { toFun := fun z => b + z
          invFun := fun z => z - b
          left_inv := fun z => add_sub_cancel_left b z
          right_inv := by intro z; simp }
      contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  exact
    T.toPartialDiffeomorph.trans
      (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm

theorem MorseCancellation.radialParameterChart_zero_mem_source (τ : ℝ)
    (u : (Hemisphere.Sphere 2)) :
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ (radialParameterChart τ u).source := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Set.univ ∧
      PassageHomology.cylinderPuncture τ u + 0 ∈
        (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).target
  rw [add_zero, PassageHomology.radialCylinderChart_mem_target]
  exact
    ⟨Set.mem_univ _,
      norm_pos_iff.mp
        (by rw [PassageHomology.norm_cylinderPuncture]; exact Real.exp_pos τ)⟩

theorem MorseCancellation.radialParameterChart_zero (τ : ℝ) (u : (Hemisphere.Sphere 2)) :
    radialParameterChart τ u 0 = (τ, u) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm
        (PassageHomology.cylinderPuncture τ u + 0) =
      (τ, u)
  rw [add_zero]
  have heq :
    PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u (τ, u) =
      PassageHomology.cylinderPuncture τ u :=
    rfl
  rw [← heq]
  exact
    (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).left_inv
      (PassageHomology.radialCylinderChart_mem_source (EuclideanSpace ℝ (Fin 3)) 2 u
        (τ, u))

theorem MorseCancellation.radialParameterChart_apply (τ : ℝ) (u : (Hemisphere.Sphere 2))
    (z : (EuclideanSpace ℝ (Fin 3))) (hz : PassageHomology.cylinderPuncture τ u + z ≠ 0) :
    radialParameterChart τ u z =
      (PassageHomology.radialCylinderHomeomorph (EuclideanSpace ℝ (Fin 3))).symm
        ⟨PassageHomology.cylinderPuncture τ u + z, hz⟩ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact
    PassageHomology.radialCylinderChart_symm_eq (EuclideanSpace ℝ (Fin 3)) 2 u
      (PassageHomology.cylinderPuncture τ u + z) hz

theorem MorseCancellation.radialParameterChart_link (τ : ℝ) (u : (Hemisphere.Sphere 2)) (ε : ℝ)
    (hε : 0 < ε) (hεu : ε < Real.exp τ) (w : (Hemisphere.Sphere 2)) :
    radialParameterChart τ u (ε • w.val) =
      (PassageHomology.cylinderLink τ u ε hε hεu w).val := by
  have hz : PassageHomology.cylinderPuncture τ u + ε • w.val ≠ 0 :=
    (PassageHomology.linkingSphere (PassageHomology.cylinderPuncture τ u) ε hε
          (by rwa [PassageHomology.norm_cylinderPuncture]) w).property.1
  exact radialParameterChart_apply τ u (ε • w.val) hz

end
