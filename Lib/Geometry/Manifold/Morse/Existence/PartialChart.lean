/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating

/-!
# Restrictions of partial diffeomorphisms

A `PartialDiffeomorph` `Φ` between manifolds restricts to a partial diffeomorphism on any open
subset of its source (`PartialChart.restrictSource`) or of its target
(`PartialChart.restrictTarget`), and its manifold derivative is bijective at every point of its
source. Consequently, for an injective continuous linear map `L : N →L[ℝ] F` from an inner product
space, the map `v ↦ Φ (L v)` on the unit sphere of `N` has injective derivative wherever
`L v ∈ Φ.source` (cf. Lee, *Introduction to Smooth Manifolds*, Ch. 4, local diffeomorphisms
and immersions).

## Main definitions and results

* `PartialChart.restrictSource`, `PartialChart.restrictTarget`
* `PartialChart.bijective_mfderiv`, `PartialChart.injective_mfderiv_linear_sphere`

## Tags

partial diffeomorphism, chart, derivative
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Restricted partial charts -/

/-- A partial chart restricted in source. -/
def PartialChart.restrictSource {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {U : Set M} (hU : IsOpen U) : PartialDiffeomorph I J M N ∞
    where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left

/-- A partial chart restricted in target. -/
def PartialChart.restrictTarget {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {V : Set N} (hV : IsOpen V) :
    PartialDiffeomorph I J M N ∞ :=
  (restrictSource Φ.symm hV).symm

/-- A partial chart has bijective derivative. -/
theorem PartialChart.bijective_mfderiv {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source) :
    Function.Bijective (mfderiv I J Φ x) := by
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  exact hdiff.mfderiv_bijective hx

/-- The linearized sphere map has injective derivative. -/
theorem PartialChart.injective_mfderiv_linear_sphere {N F E H M : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ} [Fact (Module.finrank ℝ N = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞) (L : N →L[ℝ] F) (hL : Function.Injective L)
    (u : Metric.sphere (0 : N) 1) (hu : L (u : N) ∈ Φ.source) :
    Function.Injective (mfderiv (𝓡 n) I (fun v : Metric.sphere (0 : N) 1 => Φ (L (v : N))) u) := by
  have hcoesm : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (Subtype.val : Metric.sphere (0 : N) 1 → N) :=
    contMDiff_coe_sphere (E := N) (n := n)
  have hcoe := hcoesm.mdifferentiableAt (x := u) (by simp)
  have hlinear : MDifferentiableAt 𝓘(ℝ, N) 𝓘(ℝ, F) L (u : N) :=
    L.differentiableAt.mdifferentiableAt
  have hinner := hlinear.comp u hcoe
  have hsphere :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, N) (Subtype.val : Metric.sphere (0 : N) 1 → N) u) := by
    convert! injective_mvfderiv_subtypeVal_sphere u
  change Function.Injective (mfderiv (𝓡 n) I (Φ ∘ (L ∘ Subtype.val)) u)
  rw [mfderiv_comp u (Φ.mdifferentiableAt (by simp) hu) hinner, mfderiv_comp u hlinear hcoe,
    mfderiv_eq_fderiv, L.fderiv]
  exact (bijective_mfderiv Φ hu).injective.comp (hL.comp hsphere)
