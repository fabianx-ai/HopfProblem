/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.SurgeryWindows

/-!
# The standard diffeomorphism `S¹ ≃ Circle`

`MorseCancellation.standardCircleParametrization` is the smooth diffeomorphism from the unit
sphere `Hemisphere.Sphere 1` of `ℝ²` to Mathlib's `Circle ⊆ ℂ`; precomposition with it preserves
smoothness, injectivity and injectivity of the differential of a curve `Circle → N`.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- The smooth diffeomorphism `Hemisphere.Sphere 1 ≃ Circle` between the unit sphere of `ℝ²` and
the unit circle of `ℂ`, the standard parametrisation of `SphereCoordinates` for `ℂ`. -/
def MorseCancellation.standardCircleParametrization :
    Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1) Circle ∞ := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  exact SphereCoordinates.standardParametrization ℂ 1

/-- If `γ : Circle → N` is smooth then so is `γ ∘ standardCircleParametrization`. -/
theorem MorseCancellation.contMDiff_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ) :
    ContMDiff (𝓡 1) J ∞ (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.contMDiff

/-- If `γ : Circle → N` is injective then so is `γ ∘ standardCircleParametrization`. -/
theorem MorseCancellation.injective_comp_standardCircle {N : Type*} [TopologicalSpace N]
    {γ : Circle → N} (hγ : Function.Injective γ) :
    Function.Injective (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.injective

/-- If `γ : Circle → N` is smooth with injective differential everywhere, then
`γ ∘ standardCircleParametrization` has injective differential at every `z`. -/
theorem MorseCancellation.injective_derivative_comp_standardCircle {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hi : ∀ z, Function.Injective (mfderiv (𝓡 1) J γ z)) (z : Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z) := by
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  exact
    (hi _).comp
      (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).injective

end
