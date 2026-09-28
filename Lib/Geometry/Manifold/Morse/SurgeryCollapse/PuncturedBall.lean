/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.Geometry.Manifold.Morse.SublevelSets

/-!
# The punctured ball deformation retracts onto a sphere

The punctured open ball `PuncturedBall.Space E R = {x | 0 < ‖x‖ < R}` deformation retracts onto
the sphere of radius `r < R` (`PuncturedBall.deformation`), so the unit sphere is homotopy
equivalent to the punctured ball (`PuncturedBall.sphereHomotopyEquiv`), cf. Hatcher, *Algebraic
Topology*, Example 0.2 / Proposition 2.22 (`ℝⁿ ∖ 0 ≃ Sⁿ⁻¹`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Projecting the point `fromSphere R r hr hrR u` of radius `r` back to the unit sphere returns
`u`. -/
theorem PuncturedBall.toSphere_fromSphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) (u : Metric.sphere (0 : E) 1) :
    toSphere R (fromSphere R r hr hrR u) = u :=
  PuncturedRadial.toSphere_fromSphere r hr u

/-- The radial homotopy from the identity of the punctured ball `PuncturedBall.Space E R` to the
retraction `fromSphere R r ∘ toSphere R` onto the sphere of radius `r`, `0 < r < R`. -/
def PuncturedBall.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (ContinuousMap.id (Space E R)).Homotopy ((fromSphere R r hr hrR).comp (toSphere R))
    where
  toFun
    q :=
    ⟨blendVector R r q, PuncturedRadial.blendVector_ne_zero r hr (q.1, toPunctured R q.2),
      norm_blendVector_lt R r hr hrR q.1 q.2⟩
  continuous_toFun := (continuous_blendVector R r).subtype_mk _
  map_zero_left
    x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured]
  map_one_left
    x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      PuncturedRadial.toSphere, RadialExtension.direction, div_eq_mul_inv, smul_smul]

/-- Hatcher, Example 0.2: the unit sphere of `E` is homotopy equivalent to the punctured ball
`PuncturedBall.Space E R`, by `fromSphere R r` and `toSphere R` (`0 < r < R`). -/
def PuncturedBall.sphereHomotopyEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) : Metric.sphere (0 : E) 1 ≃ₕ Space E R
    where
  toFun := fromSphere R r hr hrR
  invFun := toSphere R
  left_inv := by
    have h :
      (toSphere (E := E) R).comp (fromSphere R r hr hrR) =
        ContinuousMap.id (Metric.sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere R r hr hrR)
    rw [h]
  right_inv := ⟨(deformation R r hr hrR).symm⟩

end
