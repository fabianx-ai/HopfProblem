/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.RearrangementAmbient
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.RegularLevel
import Hopf.Proof.Geometry.Manifold.Morse.OrderedCancellation.MiddleIndexBlocks
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport

/-!
# Families of attaching two-spheres of an index-three block (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement carries `Module.finrank ℝ E = 6` or a
`Hemisphere.Sphere 2` family: the descent of a family of attaching `2`-spheres of index-`3`
windows through one window (`AdaptedWindows.exists_middle_family_descent`,
`exists_middle_family_step`, `exists_middle_basin_family_step`,
`exists_regular_band_middle_basin_family`) and its iteration over an index-`3` block
(`exists_middle_block_realization`, `exists_ordered_middle_family`), producing a
`MorseCancellation.IsNativeMiddleBasinFamily` in a regular level below the block.

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statements unchanged.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

theorem AdaptedWindows.exists_middle_family_descent {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (p : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 3)
    (α : ι → (Hemisphere.Sphere 2) → (S.data p).UpperLevel) {P : Set (S.data p).UpperLevel}
    (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ β : ι → (Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                                  (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (β j x).val) ∧
                                    ∀ j x q,
                                      Filter.Tendsto (fun t => T.flow t (β j x).val) Filter.atBot
                                          (𝓝 q) ↔
                                        Filter.Tendsto (fun t => S.flow t (α j x).val)
                                          Filter.atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hs := (S.data p).chart.finrank_negative_add_positive
      have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
      omega⟩
  dsimp only
  intro hα hαinj hαimm hpair
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) <
      Module.finrank ℝ (RegularLevel.Model E) := by simp [RegularLevel.Model, hdim]
  obtain ⟨D, K, hK, -, ⟨A⟩, havoid⟩ :=
    MorseRearrangement.exists_whole_family_avoidance α hα ((S.data p).belt_smooth hf 2)
      hdim' hP hαP
  let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp []⟩
  let u :=
    SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2 x₀
  let v :=
    SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected⟩ :=
    S.exists_relative_level_surgery_system hf hm (S.data p).upper_regular
      ((S.data p).surgery.beltSphere v) ε hε D K P hK A
  have hreach (j : ι) (x : (Hemisphere.Sphere 2)) :
    (α j x).val ∈ FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
    apply S.reaches_old_lower_of_belt_avoidance T hf p D hforward (α j x)
    intro hx
    exact Set.disjoint_left.mp (havoid j) ⟨x, rfl⟩ hx
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    T.exists_native_family_level_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u) α hα hαinj hαimm
      hpair hreach
  refine ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j x q
  obtain ⟨t, ht⟩ := horbit j x
  rw [← ht]
  exact (MorseCancellation.flow_time_atBot_limit_iff T.flow t (α j x).val q).trans (hback (α j x) q)

theorem AdaptedWindows.exists_middle_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) (n : ℕ)
    (α : Fin n → (Hemisphere.Sphere 2) → (S.data p).UpperLevel)
    {P : Set (S.data p).UpperLevel} (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ Γ : Fin (n + 1) → (Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (Γ j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (Γ j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (Γ j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) ∧
                                  (∀ x,
                                      ∃ t : ℝ,
                                        T.flow t
                                            (MorseCancellation.nativeIndexThreeAttachingSphere T p hp
                                                x).val =
                                          (Γ 0 x).val) ∧
                                    (∀ y : (S.data p).LowerLevel,
                                        y ∈ Set.range (Γ 0) ↔
                                          Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot
                                            (𝓝 p.val)) ∧
                                      (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (Γ j.succ x).val) ∧
                                        (∀ j x q,
                                            Filter.Tendsto (fun t => T.flow t (Γ j.succ x).val)
                                                Filter.atBot (𝓝 q) ↔
                                              Filter.Tendsto (fun t => S.flow t (α j x).val)
                                                Filter.atBot (𝓝 q)) ∧
                                          ∀ j q,
                                            S.toSurgeryWindows.upper p < f q →
                                              (∀ x : (S.data p).UpperLevel,
                                                  x ∈ Set.range (α j) ↔
                                                    Filter.Tendsto (fun t => S.flow t x.val)
                                                      Filter.atBot (𝓝 q)) →
                                                ∀ y : (S.data p).LowerLevel,
                                                  y ∈ Set.range (Γ j.succ) ↔
                                                    Filter.Tendsto (fun t => T.flow t y.val)
                                                      Filter.atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  dsimp only
  intro hα hαinj hαimm hpair
  obtain
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, hlabels⟩ :=
    S.exists_middle_family_descent hf hm hdim p hp α hP hαP ε hε hα hαinj hαimm hpair
  let _ : Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (T.data p).chart).symm.trans hp⟩
  have hgap (q : ManifoldMorse.criticalPoints E f) (hqp : f q < f p) :
    f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper q).trans (S.separated q p hqp)
  obtain ⟨γ, hγ, hγe, hγi, hγflow, hγrange⟩ :=
    T.exists_native_attaching_lower_cut hf p 2 (S.data p).lower_regular
      (S.toSurgeryWindows.lower_lt_value p) hgap
  have hdisj (j : Fin n) : Disjoint (Set.range γ) (Set.range (β j)) := by
    apply Set.disjoint_left.mpr
    intro z hzγ hzβ
    obtain ⟨x, hx⟩ := hzβ
    have hb := (hγrange z).mp hzγ
    rw [← hx] at hb
    exact S.not_backward_basin_on_upper_level hf p (α j x) ((hlabels j x p.val).mp hb)
  let Γ : Fin (n + 1) → (Hemisphere.Sphere 2) → (S.data p).LowerLevel := Fin.cases γ β
  have hΓpair : Pairwise (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdisj j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdisj i).symm
      | succ j => exact hβpair (fun h => hij (congrArg Fin.succ h))
  refine
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, Γ, ?_, ?_, ?_, hΓpair, hγflow, hγrange,
      horbit, hlabels, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hγ
    | succ j => exact hβ j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγe
    | succ j => exact hβe j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγi
    | succ j => exact hβi j
  · intro j q hq hfull
    apply
      T.transported_backward_basin_image hf
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
        (S.data p).lower_regular q hq (α j) (β j)
    · intro x
      exact (hfull x).trans (hback x q).symm
    · exact horbit j

theorem AdaptedWindows.exists_regular_band_middle_basin_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j)) (α : Fin n → (Hemisphere.Sphere 2) → { x : M // f x = a })
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ β : Fin n → (Hemisphere.Sphere 2) → { x : M // f x = b },
      MorseCancellation.IsNativeMiddleBasinFamily S hf hb p β ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨β, hβs, hβe, hβi, hβpair, hflow, hβfull⟩ :=
    S.exists_regular_band_family_transport hf hab ha hb hgap za α hs (fun j => (he j).injective)
      hi hpair
  exact ⟨β, ⟨hβs, hβe, hβi, hβpair, fun j => hβfull j (p j).val (hp j) (hfull j)⟩, hflow⟩

theorem AdaptedWindows.exists_middle_basin_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (q : ManifoldMorse.criticalPoints E f)
    (hq : MorseCancellation.nativeMorseIndex E f q = 3) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → (Hemisphere.Sphere 2) → (S.data q).UpperLevel)
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p α)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ r, 0 < ε r) :
    ∃ T : AdaptedWindows E f,
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
        (∀ r, (T.data r).radius < ε r) ∧
          (∀ r ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 r, T.field y = S.field y) ∧
            ∃ Γ : Fin (n + 1) → (Hemisphere.Sphere 2) → (S.data q).LowerLevel,
              MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular (Fin.cases q p)
                Γ := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨T, hcharts, hradii, hgerms, -, -, Γ, hΓs, hΓe, hΓi, hΓpair, -, hΓzero, -, -, hΓfull⟩ :=
    S.exists_middle_family_step hf hm hdim q hq n α isClosed_empty (fun j => Set.disjoint_empty _)
      ε hε hs (fun j => (he j).injective) hi hpair
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓs, hΓe, hΓi, hΓpair, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact hΓzero
  | succ j => exact hΓfull j (p j).val (hp j) (hfull j)

theorem AdaptedWindows.exists_middle_block_realization {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (n : ℕ) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (horder : StrictMono (fun j => f (p j))) (habove : ∀ j, c < f (p j))
    (hblock :
      ∀ j (q : ManifoldMorse.criticalPoints E f), c < f q → f q ≤ f (p j) → q ∈ Set.range p)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    ∃ T : AdaptedWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
        (∀ q, (T.data q).radius < ε q) ∧
          (∀ q ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
            ∃ α : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = c },
              MorseCancellation.IsNativeMiddleBasinFamily T hf hc p α := by
  induction n generalizing S c ε with
  |
    zero =>
    obtain ⟨T, hfield, -, hcharts, hradii⟩ :=
      MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
        S.integral S.zero S.descent (fun q => (S.data q).chart) S.critical_model_germ ε hε
    refine ⟨T, hcharts, hradii, ?_, (fun j => Fin.elim0 j), ?_⟩
    · intro q hq
      exact Filter.Eventually.of_forall (fun y => congrFun hfield y)
    · exact
        ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j⟩
  | succ n ih =>
    let a := S.toSurgeryWindows.upper (p 0)
    have hpa : f (p 0) < a := S.toSurgeryWindows.value_lt_upper (p 0)
    have htail (j : Fin n) : a < f (p j.succ) :=
      (S.separated (p 0) (p j.succ) (horder (Fin.succ_pos j))).trans
        (S.toSurgeryWindows.lower_lt_value (p j.succ))
    have htailblock (j : Fin n) (q : ManifoldMorse.criticalPoints E f) (haq : a < f q)
      (hqj : f q ≤ f (p j.succ)) : q ∈ Set.range (fun i : Fin n => p i.succ) := by
      obtain ⟨i, hi⟩ := hblock j.succ q ((habove 0).trans (hpa.trans haq)) hqj
      cases i using Fin.cases with
      | zero => exact (not_lt_of_ge haq.le (hi ▸ hpa)).elim
      | succ i => exact ⟨i, hi⟩
    let δ := Real.sqrt (f (p 0) - c)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (sub_pos.mpr (habove 0))
    let η : ManifoldMorse.criticalPoints E f → ℝ := fun q =>
      Min.min (ε q) (Min.min (S.data q).radius δ)
    have hη (q : ManifoldMorse.criticalPoints E f) : 0 < η q :=
      lt_min (hε q) (lt_min (S.data q).radius_pos hδ)
    obtain ⟨T, hchartsT, hradiiT, hgermsT, α, hα⟩ :=
      ih S (S.data (p 0)).upper_regular (fun j => p j.succ) (fun j => hp j.succ)
        (fun i j hij => horder (Fin.succ_lt_succ_iff.mpr hij)) htail htailblock η hη
    have hradius : (T.data (p 0)).radius < (S.data (p 0)).radius :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hradδ : (T.data (p 0)).radius < δ :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hupper : T.toSurgeryWindows.upper (p 0) < a := by
      have hh :=
        mul_pos (sub_pos.mpr hradius)
          (add_pos (S.data (p 0)).radius_pos (T.data (p 0)).radius_pos)
      change f (p 0) + (T.data (p 0)).radius ^ 2 < f (p 0) + (S.data (p 0)).radius ^ 2
      nlinarith
    have hlower : c < T.toSurgeryWindows.lower (p 0) := by
      have hh := mul_pos (sub_pos.mpr hradδ) (add_pos hδ (T.data (p 0)).radius_pos)
      have hs : δ ^ 2 = f (p 0) - c := Real.sq_sqrt (sub_pos.mpr (habove 0)).le
      change c < f (p 0) - (T.data (p 0)).radius ^ 2
      nlinarith
    have hgapUpper :
      ∀ q ∈ ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc (T.toSurgeryWindows.upper (p 0)) a := by
      intro q hq hh
      have heq :=
        S.isolated (p 0) q hq
          ⟨((S.toSurgeryWindows.lower_lt_value (p 0)).trans
                  (T.toSurgeryWindows.value_lt_upper (p 0))).le.trans
              hh.1,
            hh.2⟩
      rw [heq] at hh
      exact not_le_of_gt (T.toSurgeryWindows.value_lt_upper (p 0)) hh.1
    let _ : Fact (Module.finrank ℝ (S.data (p 0)).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hs := (S.data (p 0)).chart.finrank_negative_add_positive
        have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data (p 0)).chart).symm.trans (hp 0)
        omega⟩
    let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
    let v :=
      SphereCoordinates.standardParametrization (S.data (p 0)).chart.PositiveCoordinates 2
        x₀
    obtain ⟨β, hβ, -⟩ :=
      T.exists_regular_band_middle_basin_family hf hupper (S.data (p 0)).upper_regular
        (T.data (p 0)).upper_regular hgapUpper ((S.data (p 0)).surgery.beltSphere v)
        (fun j => p j.succ) htail α hα
    obtain ⟨U, hchartsU, hradiiU, hgermsU, Γ, hΓ⟩ :=
      T.exists_middle_basin_family_step hf hm hdim (p 0) (hp 0) (fun j => p j.succ)
        (fun j => hupper.trans (htail j)) β hβ ε hε
    have hp_cases : Fin.cases (p 0) (fun j => p j.succ) = p := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hp_cases] at hΓ
    have hbelow (q : ManifoldMorse.criticalPoints E f) (hqp : f q < f (p 0)) : f q < c := by
      by_contra h
      have hcq : c < f q :=
        lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (fun heq => hc q.val heq q.property))
      obtain ⟨j, hj⟩ := hblock 0 q hcq hqp.le
      have hh := horder.monotone (Fin.zero_le j)
      rw [hj] at hh
      exact not_lt_of_ge hh hqp
    have hgapLower :
      ∀ q ∈ ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc c (T.toSurgeryWindows.lower (p 0)) := by
      intro q hq hh
      exact
        not_le_of_gt (hbelow ⟨q, hq⟩ (hh.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p 0))))
          hh.1
    obtain ⟨Ω, hΩ, -⟩ :=
      U.exists_regular_band_middle_basin_family hf hlower (T.data (p 0)).lower_regular hc
        hgapLower (MorseCancellation.nativeIndexThreeAttachingSphere T (p 0) (hp 0) x₀) p
        (fun j =>
          (T.toSurgeryWindows.lower_lt_value (p 0)).trans_le (horder.monotone (Fin.zero_le j)))
        Γ hΓ
    refine ⟨U, fun q => (hchartsU q).trans (hchartsT q), hradiiU, ?_, Ω, hΩ⟩
    intro q hq
    filter_upwards [hgermsU q hq, hgermsT q hq] with y hyU hyT
    exact hyU.trans hyT

theorem AdaptedWindows.exists_ordered_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock r n)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ T : AdaptedWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
          (∀ p ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
            ∃ α : Fin n → (Hemisphere.Sphere 2) → (S.data q).UpperLevel,
              MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).upper_regular
                (MorseCancellation.nativeMiddleBlockPoint S r n hn) α := by
  let W := S.toSurgeryWindows
  have hnW : r + n < W.count := hn
  let q := W.point ⟨r, by omega⟩
  let p := MorseCancellation.nativeMiddleBlockPoint S r n hn
  have hp (j : Fin n) : MorseCancellation.nativeMorseIndex E f (p j) = 3 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have horder : StrictMono (fun j => f (p j)) := by
    intro i j hij
    apply W.point_strictMono
    change r + i.val + 1 < r + j.val + 1
    omega
  have habove (j : Fin n) : W.upper q < f (p j) := by
    have hqj : f q < f (p j) := W.point_strictMono (by change r < r + j.val + 1; omega)
    exact (W.separated q (p j) hqj).trans (W.lower_lt_value (p j))
  have hblock (j : Fin n) (z : ManifoldMorse.criticalPoints E f) (hz : W.upper q < f z)
    (hzj : f z ≤ f (p j)) : z ∈ Set.range p := by
    obtain ⟨k, rfl⟩ := W.point.surjective z
    have hrk : r < k.val := W.point_strictMono.lt_iff_lt.mp ((W.value_lt_upper q).trans hz)
    have hkj : k.val ≤ r + j.val + 1 := W.point_strictMono.le_iff_le.mp hzj
    let i : Fin n := ⟨k.val - (r + 1), by omega⟩
    refine ⟨i, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (k.val - (r + 1)) + 1 = k.val
    omega
  exact
    S.exists_middle_block_realization hf hm hdim n (S.data q).upper_regular p hp horder habove
      hblock ε hε

end
