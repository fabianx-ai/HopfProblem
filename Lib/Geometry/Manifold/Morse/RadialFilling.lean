/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.SurgeryWindows

/-!
# Radial filling of a null-homotopic sphere map

A null-homotopy `H` from `f : C(Sⁿ, M)` to a constant map can be read as a single
continuous map on the closed ball: `RadialFilling.filling H b` sends a vector `v`
of the ambient space to `H (radialTime v, direction b v)`, where `radialTime`
runs the homotopy parameter from `1` at the centre down to `0` on the unit sphere
with the cut-offs `1/4` and `3/4` (so the filling is constant near the centre and
equal to `f` near the boundary), and `direction b v` normalises `v`, with the
base point `b` as the value at `0`.

`filling_eq_center` and `filling_eq_boundary` identify the filling on the two
plateaux and `filling_on_sphere` says it restricts to `f` on the unit sphere.

Extracted from `Lib.Geometry.Manifold.Morse.SurgeryHomology`, where the round-7
audit found it as an unrelated third subject.

## Main declarations

* `RadialFilling.direction`, `RadialFilling.radialTime`, `RadialFilling.filling`
* `RadialFilling.filling_eq_center`, `RadialFilling.filling_eq_boundary`,
  `RadialFilling.filling_on_sphere`

## References

* [Allen Hatcher, *Algebraic topology*][hatcher02], §0 (a map of the sphere is
  null-homotopic iff it extends over the ball).

## Tags

null-homotopy, sphere, ball, cone, radial
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- Given a base point `b : Hemisphere.Sphere n` and a vector `v` of the ambient space
`Hemisphere.Ambient (n + 1)`, `RadialFilling.direction b v` is the point of the unit sphere in
direction `v`: the normalisation `v / ‖v‖` when `v ≠ 0`, and `b` when `v = 0`. -/
def RadialFilling.direction {n : ℕ} (b : Hemisphere.Sphere n)
    (v : Hemisphere.Ambient (n + 1)) : Hemisphere.Sphere n := by
  classical
    exact
    if hv : v = 0 then b
    else
      ⟨NormedSpace.normalize v, by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩

/-- Hypotheses: a base point `b : Hemisphere.Sphere n` and a nonzero ambient vector `v`.
Conclusion: away from the origin `direction b v` is, as a vector of the ambient space, the
normalisation `NormedSpace.normalize v`. -/
theorem RadialFilling.direction_coe {n : ℕ} (b : Hemisphere.Sphere n)
    {v : Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    (direction b v : Hemisphere.Ambient (n + 1)) = NormedSpace.normalize v := by
  classical simp only [direction, dif_neg hv]

/-- Hypotheses: a base point `b` and a point `v`, both on `Hemisphere.Sphere n`.
Conclusion: `direction` fixes the unit sphere, `direction b v.1 = v`. -/
theorem RadialFilling.direction_of_mem_sphere {n : ℕ} (b v : Hemisphere.Sphere n) :
    direction b v.1 = v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hv : v.1 ≠ 0 := by intro h; simp [h] at hn
  apply Subtype.ext
  rw [direction_coe b hv, NormedSpace.normalize_eq_self_of_norm_eq_one hn]

/-- Given an ambient vector `v : Hemisphere.Ambient (n + 1)`, `RadialFilling.radialTime v` is the
homotopy parameter `1 - ‖v‖` clamped to `unitInterval`: it is `1` at the centre and `0` on and
outside the unit sphere. -/
def RadialFilling.radialTime {n : ℕ} (v : Hemisphere.Ambient (n + 1)) :
    unitInterval :=
  Set.projIcc 0 1 zero_le_one (1 - ‖v‖)

/-- Hypotheses: an ambient vector `v : Hemisphere.Ambient (n + 1)` (none beyond that).
Conclusion: the real number underlying `radialTime v` is `max 0 (min 1 (1 - ‖v‖))`. -/
theorem RadialFilling.coe_radialTime {n : ℕ} (v : Hemisphere.Ambient (n + 1)) :
    (radialTime v : ℝ) = Max.max 0 (Min.min 1 (1 - ‖v‖)) :=
  rfl

/-- Hypotheses: an ambient vector `v` with `3 / 4 ≤ ‖v‖`.
Conclusion: `(radialTime v : ℝ) ≤ 1 / 4`, so on the outer plateau the homotopy parameter stays in
the bottom quarter of `unitInterval`. -/
theorem RadialFilling.radialTime_le_quarter {n : ℕ} {v : Hemisphere.Ambient (n + 1)}
    (hv : 3 / 4 ≤ ‖v‖) : (radialTime v : ℝ) ≤ 1 / 4 := by
  rw [coe_radialTime]
  exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith))

/-- Hypotheses: an ambient vector `v` with `‖v‖ ≤ 1 / 4`.
Conclusion: `3 / 4 ≤ (radialTime v : ℝ)`, so near the centre the homotopy parameter stays in the
top quarter of `unitInterval`. -/
theorem RadialFilling.three_quarters_le_radialTime {n : ℕ}
    {v : Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : 3 / 4 ≤ (radialTime v : ℝ) := by
  rw [coe_radialTime]
  exact le_max_of_le_right (le_min (by norm_num) (by linarith))

/-- Hypotheses: an ambient vector `v` with `0 < ‖v‖` and `‖v‖ < 1`.
Conclusion: `radialTime` is smooth at `v` as a map `Hemisphere.Ambient (n + 1) → unitInterval`
for the models `𝓘(ℝ, Hemisphere.Ambient (n + 1))` and `𝓡∂ 1`; the two bounds keep `v` off the
singularity of the norm and `1 - ‖v‖` in the interior of the clamp. -/
theorem RadialFilling.contMDiffAt_radialTime {n : ℕ} {v : Hemisphere.Ambient (n + 1)}
    (hv : 0 < ‖v‖) (hunit : ‖v‖ < 1) :
    ContMDiffAt 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡∂ 1) ∞ radialTime v := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have hm : 1 - ‖v‖ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hn : Set.Icc (0 : ℝ) 1 ∈ 𝓝 (1 - ‖v‖) := Icc_mem_nhds (by linarith) (by linarith)
  have hproj := (hp _ hm).contMDiffAt hn
  have hnorm : ContDiffAt ℝ ∞ (Norm.norm : Hemisphere.Ambient (n + 1) → ℝ) v :=
    contDiffAt_norm ℝ (norm_pos_iff.mp hv)
  exact hproj.comp v (contDiffAt_const.sub hnorm).contMDiffAt

/-- Given a topological space `M`, a map `f : C(Hemisphere.Sphere n, M)`, a point `c : M`, a
homotopy `H` from `f` to the constant map at `c`, and a base point `b : Hemisphere.Sphere n`,
`RadialFilling.filling H b` is the map on the ambient space sending `v` to
`H (radialTime v, direction b v)`: the null-homotopy read as a single map on the closed ball. -/
def RadialFilling.filling {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n) (v : Hemisphere.Ambient (n + 1)) : M :=
  H (radialTime v, direction b v)

/-- Hypotheses: a null-homotopy `H` from `f` to the constant map at `c`, a base point `b`, the
assumption `htop` that `H (t, x) = c` whenever `3 / 4 ≤ (t : ℝ)`, and an ambient vector `v` with
`‖v‖ ≤ 1 / 4`.
Conclusion: `filling H b v = c`, i.e. the filling is constant on the inner plateau. -/
theorem RadialFilling.filling_eq_center {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c)
    {v : Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : filling H b v = c :=
  htop _ _ (three_quarters_le_radialTime hv)

/-- Hypotheses: a null-homotopy `H` from `f` to the constant map at `c`, a base point `b`, the
assumption `hbottom` that `H (t, x) = f x` whenever `(t : ℝ) ≤ 1 / 4`, and an ambient vector `v`
with `3 / 4 ≤ ‖v‖`.
Conclusion: `filling H b v = f (direction b v)`, i.e. on the outer plateau the filling is `f`
composed with the radial projection. -/
theorem RadialFilling.filling_eq_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    {v : Hemisphere.Ambient (n + 1)} (hv : 3 / 4 ≤ ‖v‖) :
    filling H b v = f (direction b v) :=
  hbottom _ _ (radialTime_le_quarter hv)

/-- Hypotheses: a null-homotopy `H` from `f` to the constant map at `c`, a base point `b`, the
assumption `hbottom` that `H (t, x) = f x` whenever `(t : ℝ) ≤ 1 / 4`, and a point `v` of
`Hemisphere.Sphere n`.
Conclusion: `filling H b v.1 = f v`, i.e. the filling restricts to `f` on the unit sphere. -/
theorem RadialFilling.filling_on_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (v : Hemisphere.Sphere n) : filling H b v.1 = f v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  rw [filling_eq_boundary H b hbottom (by rw [hn]; norm_num), direction_of_mem_sphere]
