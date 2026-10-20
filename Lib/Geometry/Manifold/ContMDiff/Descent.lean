/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Geometry.Manifold.RestrictScalars

/-!
# Descent of manifold differentiability

Manifold differentiability descends through a surjective local diffeomorphism: locally compose
with its smooth inverse.  A scalar-restriction variant accepts a local diffeomorphism over a
larger normed field while proving differentiability over the smaller field.
-/

@[expose] public section

open Filter Function Manifold Set

open scoped ContDiff

/-- Differentiability descends through a surjective local diffeomorphism. -/
theorem contMDiff_of_comp_surjective_localDiffeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F F' H K K' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace P] [ChartedSpace K' P]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K)
    (L : ModelWithCorners 𝕜 F' K') {n : ℕ∞ω} {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hsurj : Surjective f) {g : N → P}
    (hgf : ContMDiff I L n (g ∘ f)) : ContMDiff J L n g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := hgf.contMDiffAt.comp (f x) (hf x).localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with z hz
  change g z = g (f ((hf x).localInverse z))
  rw [show f ((hf x).localInverse z) = z from hz]

/-- Scalar-restricted differentiability descends through a surjective local diffeomorphism over
the larger field.  This avoids repackaging the local diffeomorphism after scalar restriction. -/
theorem contMDiff_of_comp_surjective_localDiffeomorph_restrictScalars
    {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    {E F F' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace F' P]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsLocalDiffeomorph 𝓘(𝕜', E) 𝓘(𝕜', F) n f)
    (hsurj : Surjective f) {g : N → P}
    (hgf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F') n (g ∘ f)) :
    ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, F') n g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := hgf.contMDiffAt.comp (f x)
    ((hf x).localInverse_contMDiffAt.restrictScalars (𝕜 := 𝕜))
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with z hz
  change g z = g (f ((hf x).localInverse z))
  rw [show f ((hf x).localInverse z) = z from hz]

/-- Smoothness on an open set follows from smoothness of the canonical open-subtype
restriction. -/
theorem contMDiffOn_of_contMDiff_restriction
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K)
    (n : ℕ∞ω) (U : TopologicalSpace.Opens M) (f : M → N)
    (h : ContMDiff I J n (fun x : U ↦ f x)) : ContMDiffOn I J n f U := by
  intro x hx
  let xU : U := ⟨x, hx⟩
  exact (contMDiffAt_subtype_iff.mp (h xU)).contMDiffWithinAt
