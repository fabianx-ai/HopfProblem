/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData
import Lib.Geometry.Manifold.Whitney.FrameField.IntersectionCoordinates

/-!
# Sheet frames and normal detectors along a strip

For the strip normal data of a sheet (`StripNormalData`) and a tubular chart, this file studies the
sheet differential along the centre line: its base frame in the plane directions
(`StripNormalData.sheetBaseFrame`), its smoothness in the parameter, and its completion by the
block of the chart transition on the complementary directions (`StripNormalData.sheetComplement`)
to the invertible transition derivative
(`StripNormalData.sheet_coprod_complement_eq`, `StripNormalData.isInvertible_sheet_coprod_complement`).

For an ambient map `q`, the normal detector `StripNormalData.normalDetector` is the derivative of
`q` in the tubular chart along the centre line: smooth in the parameter, surjective where `dq` is,
killing the sheet differential when `q` vanishes on the sheet, and composing with it to the
derivative of `q` read in the strip chart (`StripNormalData.normalDetector_comp_sheet`).

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6 (computing intersection signs from a
defining map of one sheet).

## Tags

normal frame, chart transition, intersection sign
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The plane component of the sheet differential along the sheet directions: the base frame of the
sheet at the parameter `t`. -/
def StripNormalData.sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    A →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) Z).comp
    ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A))

/-- The sheet differential depends smoothly on the parameter where the centre line is in the source
of the strip chart and its image in the target of the tubular chart. -/
theorem StripNormalData.contDiffOn_sheetDifferential {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetDifferential Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hs : ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
    htransition.comp (t, 0) (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, (0 : A))) := contDiff_id.prodMk contDiff_const
  exact ((hs.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

/-- The sheet base frame depends smoothly on the parameter on the same set. -/
theorem StripNormalData.contDiffOn_sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  contDiffOn_const.clm_comp ((d.contDiffOn_sheetDifferential Ψ).clm_comp contDiffOn_const)

/-- If the centre line lands in the target of the tubular chart over all of `[0, 1]`, the sheet base
frame is smooth on an open neighbourhood of `[0, 1]`. -/
theorem StripNormalData.exists_open_sheetBaseFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ) U := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact
    ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target), hO.preimage hc,
      fun t ht => ⟨d.line ht, htarget t ht⟩, d.contDiffOn_sheetBaseFrame Ψ⟩

/-- In the tubular chart, the sheet differential splits along the sheet directions into its plane
part, the base frame, and its normal part, the normal frame. -/
theorem StripNormalData.sheetDifferential_transverse_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (u : A) : d.sheetDifferential Ψ t (0, u) = (d.sheetBaseFrame Ψ t u, d.normalFrame Ψ t u) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun L : A →L[ℝ] Z => L u) (d.normal_sheetDifferential Ψ ht htarget)

/-- The derivative at the centre of the transition from the strip chart to the tubular chart. -/
def StripNormalData.tubularTransitionDerivative {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    StripCoordinates.Space A B →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)

/-- The block of that derivative on the complementary directions `B` of the strip chart: the
complement of the sheet in the tubular chart. -/
def StripNormalData.sheetComplement {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    B →L[ℝ] ((ℝ × ℝ) × Z) :=
  (d.tubularTransitionDerivative Ψ t).comp (ContinuousLinearMap.inr ℝ (ℝ × A) B)

/-- The transition derivative is smooth in the parameter where the centre line is in the source of
the strip chart and its image in the target of the tubular chart. -/
theorem StripNormalData.contDiffOn_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.tubularTransitionDerivative Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact ((htransition.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

/-- The sheet complement is smooth in the parameter on the same set. -/
theorem StripNormalData.contDiffOn_sheetComplement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetComplement Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  (d.contDiffOn_tubularTransitionDerivative Ψ).clm_comp contDiffOn_const

/-- The transition derivative is bijective, being the derivative of a transition between two
charts. -/
theorem StripNormalData.bijective_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    Function.Bijective (d.tubularTransitionDerivative Ψ t) := by
  unfold tubularTransitionDerivative
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (StripCoordinates.center t) (Ψ.symm.mdifferentiableAt (by simp) htarget)
      (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  exact
    (PartialChart.bijective_mfderiv Ψ.symm htarget).comp
      (PartialChart.bijective_mfderiv d.chart (d.line ht))

/-- The sheet differential and the sheet complement together make up the transition derivative:
`sheetDifferential ⊞ sheetComplement = tubularTransitionDerivative`. -/
theorem StripNormalData.sheet_coprod_complement_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t) =
      d.tubularTransitionDerivative Ψ t := by
  rw [d.sheetDifferential_eq Ψ ht htarget]
  apply ContinuousLinearMap.ext
  intro z
  change
    d.tubularTransitionDerivative Ψ t (z.1, 0) + d.tubularTransitionDerivative Ψ t (0, z.2) =
      d.tubularTransitionDerivative Ψ t z
  rw [← map_add]
  simp

/-- Consequently the frame `sheetDifferential ⊞ sheetComplement` is invertible. -/
theorem StripNormalData.isInvertible_sheet_coprod_complement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) [FiniteDimensional ℝ A]
    [FiniteDimensional ℝ B] {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ((d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t)).IsInvertible := by
  apply FrameField.isInvertible_coprod_of_bijective
  rw [d.sheet_coprod_complement_eq Ψ ht htarget]
  exact d.bijective_tubularTransitionDerivative Ψ ht htarget

/-- The derivative in the tubular chart of an ambient map `q`, at the point of the centre line with
parameter `t`: the linear detector of the normal directions of `q`. -/
def StripNormalData.normalDetector {A B Z E M N : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) (t : ℝ) :
    ((ℝ × ℝ) × Z) →L[ℝ] N :=
  fderiv ℝ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t)))

/-- An ambient map smooth at a centre point is smooth in the tubular chart near the corresponding
point. -/
theorem StripNormalData.contDiffAt_normalMap_in_tube {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    ContDiffAt ℝ ∞ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t))) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq
  exact
    (hq'.comp _
        (Ψ.contMDiffOn_toFun.contMDiffAt
          (Ψ.open_source.mem_nhds (Ψ.map_target' htarget)))).contDiffAt

/-- The normal detector is smooth on `[0, 1]` when the ambient map is smooth on an open set
containing the centre line. -/
theorem StripNormalData.contDiffOn_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ O) :
    ContDiffOn ℝ ∞ (d.normalDetector Ψ q) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have hqΨ :=
    d.contDiffAt_normalMap_in_tube Ψ q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht)))
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  have hx : ContDiffAt ℝ ∞ (fun s => Ψ.symm (d.chart (StripCoordinates.center s))) t :=
    (d.contDiffAt_tubularTransition Ψ ht (htarget t ht)).comp t hc.contDiffAt
  exact ((hqΨ.fderiv_right (by simp)).comp t hx).contDiffWithinAt

/-- The normal detector is the composite of the differential of the ambient map with the
differential of the tubular chart. -/
theorem StripNormalData.normalDetector_eq_mfderiv_comp {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    d.normalDetector Ψ q t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)) : E →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ
            (Ψ.symm (d.chart (StripCoordinates.center t))) :
          ((ℝ × ℝ) × Z) →L[ℝ] E) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) q
      (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq.mdifferentiableAt (by simp)
  unfold normalDetector
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp _ hq' (Ψ.mdifferentiableAt (by simp) (Ψ.map_target' htarget)), hinv]

/-- The normal detector is surjective wherever the differential of the ambient map is. -/
theorem StripNormalData.surjective_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t)))
    (hqs :
      Function.Surjective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)))) :
    Function.Surjective (d.normalDetector Ψ q t) := by
  rw [d.normalDetector_eq_mfderiv_comp Ψ q htarget hq]
  exact hqs.comp (PartialChart.bijective_mfderiv Ψ (Ψ.map_target' htarget)).surjective

/-- If the ambient map vanishes on the sheet, its normal detector kills the sheet differential. -/
theorem StripNormalData.normalDetector_comp_sheet_eq_zero {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O) (hzero : ∀ y ∈ S ∩ O, q y = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : d.chart (StripCoordinates.center t) ∈ O) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) = 0 := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnearS : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), i w ∈ d.chart.source :=
    hi.preimage_mem_nhds (d.chart.open_source.mem_nhds (d.line ht))
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target ∩ O :=
    hd.preimage_mem_nhds ((Ψ.open_target.inter hO).mem_nhds ⟨htarget, hcenter⟩)
  have hvanish : ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun _ => 0) := by
    filter_upwards [hnearS, hnear] with w hw hwo
    change q (Ψ (Ψ.symm (d.chart (i w)))) = 0
    have hinv : Ψ (Ψ.symm (d.chart (i w))) = d.chart (i w) := Ψ.right_inv' hwo.1
    rw [hinv]
    exact hzero _ ⟨(d.sheet _ hw).mpr rfl, hwo.2⟩
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget (hq.contMDiffAt (hO.mem_nhds hcenter))
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  have hder : fderiv ℝ ((q ∘ Ψ) ∘ d.sheetTransition Ψ) (t, (0 : A)) = 0 := by
    rw [hvanish.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : N) (t, (0 : A))).fderiv
  exact hchain.symm.trans hder

/-- The normal detector composed with the sheet differential is the derivative of the ambient map
read in the strip chart of the sheet. -/
theorem StripNormalData.normalDetector_comp_sheet {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) =
      fderiv ℝ (fun w : ℝ × A => q (d.chart (w, 0))) (t, 0) := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target :=
    hd.preimage_mem_nhds (Ψ.open_target.mem_nhds htarget)
  have heq :
    ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun w : ℝ × A => q (d.chart (w, 0))) := by
    filter_upwards [hnear] with w hw
    exact congrArg q (Ψ.right_inv' hw)
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget hq
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  exact hchain.symm.trans heq.fderiv_eq

end
