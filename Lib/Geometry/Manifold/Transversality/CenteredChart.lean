/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Transversality.Diffeomorph
/-!
# Translations and centred charts

Translation by a vector as a diffeomorphism of a normed space, and the chart of a manifold modelled
on a normed space translated so that the origin is sent to a prescribed point.

## Main definitions

* `NativeParametrization.translation`
* `NativeParametrization.centered`, with `NativeParametrization.centered_zero`
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- Translation by a vector, as a diffeomorphism of a normed space. -/
def NativeParametrization.translation {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : D) : Diffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D D ∞
    where
  toEquiv :=
    { toFun := fun x => x + a
      invFun := fun x => x - a
      left_inv := fun _ => add_sub_cancel_right _ _
      right_inv := fun _ => sub_add_cancel _ _ }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

/-- The chart of a manifold at a point `x`, translated so that `0` is sent to `x`; a parametrisation
of a neighbourhood of `x` centred at the origin.
-/
def NativeParametrization.centered {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] (x : N) :
    PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D N ∞ :=
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  (translation (c x)).toPartialDiffeomorph'.trans c.symm

/-- The origin lies in the source of the centred parametrisation. -/
theorem NativeParametrization.zero_mem_centered_source {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : (0 : D) ∈ (centered (D := D) x).source := by
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  refine ⟨Set.mem_univ _, ?_⟩
  change 0 + c x ∈ c.target
  rw [zero_add]
  exact c.map_source' (mem_extChartAt_source x)

/-- The centred parametrisation sends the origin to the given point. -/
theorem NativeParametrization.centered_zero {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : centered (D := D) x (0 : D) = x := by
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  change c.symm (0 + c x) = x
  rw [zero_add]
  exact c.left_inv' (mem_extChartAt_source x)

/-- The given point lies in the target of its centred parametrisation. -/
theorem NativeParametrization.mem_centered_target {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : x ∈ (centered (D := D) x).target := by
  have hx := (centered (D := D) x).map_source' (zero_mem_centered_source (D := D) x)
  rwa [centered_zero] at hx
