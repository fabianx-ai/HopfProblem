/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData

/-!
# Retiming the sheet transitions of a strip

The affine change of time coordinate `sheetTimeCoordinates : (s, u) ↦ ((s + 1) / 2, u)` carries
the boundary-arc parameter `[-1, 1]` of the bigon to the strip parameter `[0, 1]`; its inverse is
`sheetTimeInverse`, and its derivative is `halfTimeDerivative`. For the normal data `d` of a sheet
along a strip and a chart `Ψ`, the transition from the strip chart of the sheet to `Ψ`, restricted
to the sheet directions and read in the retimed parameter, is smooth on an open domain containing
the centre line (`StripNormalData.contDiffOn_retimedSheetTransition`,
`StripNormalData.retimedDomain_contains_center`) with derivative the sheet differential composed
with the retiming derivative (`StripNormalData.hasFDerivAt_retimedSheetTransition`).

These are the chain-rule computations used to build coordinates adapted to two sheets along a
Whitney disc; cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

chart transition, chain rule
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- The derivative of the affine retiming `s ↦ (s + 1) / 2` of the time coordinate. -/
def WhitneyPairModel.halfTimeDerivative {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : (ℝ × A) →L[ℝ] (ℝ × A) :=
  (((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ A)).prod (ContinuousLinearMap.snd ℝ ℝ A)

/-- The retiming derivative halves the time coordinate and leaves the sheet directions alone. -/
theorem WhitneyPairModel.halfTimeDerivative_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (v : (ℝ × A)) : halfTimeDerivative v = (v.1 / 2, v.2) := by
  apply Prod.ext
  · change (1 / 2 : ℝ) * v.1 = v.1 / 2
    ring
  · rfl

/-- The affine change of time coordinate `s ↦ (s + 1) / 2` carrying the boundary-arc parameter `[-1,
1]` to `[0, 1]`. -/
def WhitneyPairModel.sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : (ℝ × A) :=
  halfTimeDerivative p + ((1 / 2 : ℝ), 0)

/-- Value of the retiming of the time coordinate. -/
theorem WhitneyPairModel.sheetTimeCoordinates_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : sheetTimeCoordinates p = ((p.1 + 1) / 2, p.2) := by
  rw [sheetTimeCoordinates, halfTimeDerivative_apply]
  apply Prod.ext
  · change p.1 / 2 + 1 / 2 = (p.1 + 1) / 2
    ring
  · exact add_zero _

/-- The retiming sends the boundary-arc parameter `2 t - 1` to `t`. -/
theorem WhitneyPairModel.sheetTimeCoordinates_center {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (t : ℝ) : sheetTimeCoordinates (2 * t - 1, (0 : A)) = (t, 0) := by
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- The retiming is smooth. -/
theorem WhitneyPairModel.contDiff_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeCoordinates (A := A)) :=
  (halfTimeDerivative (A := A)).contDiff.add contDiff_const

/-- The retiming has derivative `halfTimeDerivative` everywhere. -/
theorem WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : HasFDerivAt sheetTimeCoordinates halfTimeDerivative p :=
  halfTimeDerivative.hasFDerivAt.add_const ((1 / 2 : ℝ), (0 : A))

/-- The domain of the transition from the strip chart of a sheet to a tubular chart, read along the
sheet directions. -/
def StripNormalData.sheetTransitionDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B) ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target)

/-- The domain of the sheet transition is open. -/
theorem StripNormalData.isOpen_sheetTransitionDomain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.sheetTransitionDomain Ψ) := by
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact hO.preimage (ContinuousLinearMap.inl ℝ (ℝ × A) B).continuous

/-- The sheet transition is smooth on its domain. -/
theorem StripNormalData.contDiffOn_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetTransition Ψ) (d.sheetTransitionDomain Ψ) := by
  have hfull : ContDiffOn ℝ ∞ (Ψ.symm ∘ d.chart) (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    (Ψ.contMDiffOn_invFun.comp (d.chart.contMDiffOn_toFun.mono Set.inter_subset_left)
        (fun _ hp => hp.2)).contDiffOn
  exact hfull.comp (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffOn (fun _ hp => hp)

/-- The sheet transition read in the boundary-arc time parameter. -/
def StripNormalData.retimedSheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  d.sheetTransition Ψ ∘ WhitneyPairModel.sheetTimeCoordinates

/-- The domain of the retimed sheet transition. -/
def StripNormalData.retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  WhitneyPairModel.sheetTimeCoordinates ⁻¹' d.sheetTransitionDomain Ψ

/-- The domain of the retimed sheet transition is open. -/
theorem StripNormalData.isOpen_retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.retimedDomain Ψ) :=
  (d.isOpen_sheetTransitionDomain Ψ).preimage
    WhitneyPairModel.contDiff_sheetTimeCoordinates.continuous

/-- The retimed sheet transition is smooth on its domain. -/
theorem StripNormalData.contDiffOn_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.retimedSheetTransition Ψ) (d.retimedDomain Ψ) :=
  (d.contDiffOn_sheetTransition Ψ).comp
    WhitneyPairModel.contDiff_sheetTimeCoordinates.contDiffOn (fun _ hp => hp)

/-- The centre of the strip at a parameter of `[0, 1]` lies in the domain of the retimed
transition. -/
theorem StripNormalData.retimedDomain_contains_center {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (2 * t - 1, (0 : A)) ∈ d.retimedDomain Ψ := by
  change WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0) ∈ d.sheetTransitionDomain Ψ
  rw [WhitneyPairModel.sheetTimeCoordinates_center]
  exact ⟨d.line ht, htarget⟩

/-- The derivative of the retimed sheet transition at a centre point is the sheet differential
composed with the retiming derivative. -/
theorem StripNormalData.hasFDerivAt_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    HasFDerivAt (d.retimedSheetTransition Ψ)
      ((d.sheetDifferential Ψ t).comp WhitneyPairModel.halfTimeDerivative) (2 * t - 1, 0) :=
  by
  have hd :
    HasFDerivAt (d.sheetTransition Ψ) (d.sheetDifferential Ψ t)
      (WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0)) := by
    rw [WhitneyPairModel.sheetTimeCoordinates_center]
    exact ((d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp (2 * t - 1, (0 : A)) (WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates _)


/-- The inverse `s ↦ 2 s - 1` of the retiming of the time coordinate. -/
def WhitneyPairModel.sheetTimeInverse {A : Type*} (q : (ℝ × A)) : (ℝ × A) :=
  (2 * q.1 - 1, q.2)

/-- The inverse retiming is smooth. -/
theorem WhitneyPairModel.contDiff_sheetTimeInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeInverse (A := A)) := by
  unfold sheetTimeInverse
  fun_prop

/-- The inverse retiming is a left inverse of the retiming. -/
theorem WhitneyPairModel.sheetTimeInverse_leftInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.LeftInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change 2 * ((q.1 + 1) / 2) - 1 = q.1
    ring
  · rfl

/-- The inverse retiming is a right inverse of the retiming. -/
theorem WhitneyPairModel.sheetTimeInverse_rightInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.RightInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change (2 * q.1 - 1 + 1) / 2 = q.1
    ring
  · rfl


end
