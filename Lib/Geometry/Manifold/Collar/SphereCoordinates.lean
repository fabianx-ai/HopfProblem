/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The diffeomorphism of unit spheres induced by a linear isometry

A linear isometric equivalence `L : N ≃ₗᵢ[ℝ] P` of real inner product spaces of dimension
`n + 1` restricts to a diffeomorphism between their unit spheres
(`SphereCoordinates.ofLinearIsometry`), for the manifold structure of
`Mathlib.Geometry.Manifold.Instances.Sphere`.

## Tags

sphere, linear isometry, diffeomorphism
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

/-- Sphere coordinates induced by a linear isometry. -/
def SphereCoordinates.ofLinearIsometry {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] {n : ℕ}
    [Fact (Module.finrank ℝ N = n + 1)] [Fact (Module.finrank ℝ P = n + 1)] (L : N ≃ₗᵢ[ℝ] P) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : N) 1) (Metric.sphere (0 : P) 1) ∞ := by
  have hforward (x : Metric.sphere (0 : N) 1) : L (x : N) ∈ Metric.sphere (0 : P) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.norm_map] using x.property
  have hinverse (y : Metric.sphere (0 : P) 1) : L.symm (y : P) ∈ Metric.sphere (0 : N) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.symm.norm_map] using y.property
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, P) ∞ (fun x : Metric.sphere (0 : N) 1 => L (x : N)) :=
    L.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  have hi : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (fun y : Metric.sphere (0 : P) 1 => L.symm (y : P)) :=
    L.symm.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  exact
    { toFun := fun x => ⟨L x, hforward x⟩
      invFun := fun y => ⟨L.symm y, hinverse y⟩
      left_inv := fun x => Subtype.ext (L.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (L.apply_symm_apply y)
      contMDiff_toFun := hs.codRestrict_sphere hforward
      contMDiff_invFun := hi.codRestrict_sphere hinverse }
