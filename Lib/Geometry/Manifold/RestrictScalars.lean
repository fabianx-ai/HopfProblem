/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Restricting the scalar field of a manifold

A manifold whose coordinate changes are smooth over a normed field extension
is a manifold, with the same charts and regularity, over the smaller field.
-/

@[expose] public section

open Function Manifold

open scoped ContDiff

namespace IsManifold

/-- Restrict the scalar field of a manifold modelled on a normed vector space. -/
theorem restrictScalars (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {𝕜' E M : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
    [IsScalarTower 𝕜 𝕜' E] [TopologicalSpace M] [ChartedSpace E M]
    (n : ℕ∞ω) [IsManifold 𝓘(𝕜', E) n M] : IsManifold 𝓘(𝕜, E) n M := by
  apply isManifold_of_contDiffOn 𝓘(𝕜, E) n M
  intro e e' he he'
  have h := (contDiffGroupoid n 𝓘(𝕜', E)).compatible he he'
  have hc : ContDiffOn 𝕜' n (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa only [contDiffPregroupoid, mfld_simps] using h.1
  simpa only [mfld_simps] using hc.restrict_scalars 𝕜

end IsManifold

universe u v

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {n : ℕ∞ω}

/-- Restrict the scalar field in manifold differentiability within a set, retaining the same
charts and differentiability order. -/
theorem ContMDiffWithinAt.restrictScalars {f : M → N} {s : Set M} {x : M}
    (h : ContMDiffWithinAt 𝓘(𝕜', E) 𝓘(𝕜', F) n f s x) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f s x := by
  rw [contMDiffWithinAt_iff]
  have hx := contMDiffWithinAt_iff.mp h
  refine ⟨hx.1, ?_⟩
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_comp, comp_id] using hx.2.restrict_scalars 𝕜

/-- Pointwise version of manifold scalar restriction. -/
theorem ContMDiffAt.restrictScalars {f : M → N} {x : M}
    (h : ContMDiffAt 𝓘(𝕜', E) 𝓘(𝕜', F) n f x) :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x :=
  ContMDiffWithinAt.restrictScalars h

/-- Global version of manifold scalar restriction. -/
theorem ContMDiff.restrictScalars {f : M → N}
    (h : ContMDiff 𝓘(𝕜', E) 𝓘(𝕜', F) n f) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f :=
  fun x ↦ ContMDiffAt.restrictScalars (h x)

/-- On-set version of manifold scalar restriction. -/
theorem ContMDiffOn.restrictScalars {f : M → N} {s : Set M}
    (h : ContMDiffOn 𝓘(𝕜', E) 𝓘(𝕜', F) n f s) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n f s :=
  fun x hx ↦ ContMDiffWithinAt.restrictScalars (h x hx)

/-- Restrict the scalar field of a diffeomorphism, retaining its underlying equivalence. -/
def Diffeomorph.restrictScalars
    (e : Diffeomorph 𝓘(𝕜', E) 𝓘(𝕜', F) M N n) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) M N n where
  toEquiv := e.toEquiv
  contMDiff_toFun := e.contMDiff.restrictScalars
  contMDiff_invFun := e.symm.contMDiff.restrictScalars

/-- Restrict the scalar field of a partial diffeomorphism, retaining its underlying partial
equivalence. -/
def PartialDiffeomorph.restrictScalars
    (e : PartialDiffeomorph 𝓘(𝕜', E) 𝓘(𝕜', F) M N n) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) M N n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := e.contMDiffOn_toFun.restrictScalars
  contMDiffOn_invFun := e.contMDiffOn_invFun.restrictScalars
