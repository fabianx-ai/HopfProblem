/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.Topology.Homotopy.HandleRetraction

/-!
# The disk–cube homeomorphism

For a finite-dimensional real normed space `V` and a continuous linear equivalence
`L : V ≃L[ℝ] (Fin n → ℝ)`, the closed unit ball `DiskCylinder.Disk (E := V)` is
homeomorphic to the unit cube `Fin n → unitInterval`, and the norm-one boundary of
the ball corresponds to `Cube.boundary (Fin n)`. No `0 < n` hypothesis is required.

## Outline of the construction

1. `DiskCube.target L` is the pulled-back cube `L ⁻¹' realCubeSet n`; it is compact
   (`target_compact`), convex (`target_convex`), and has nonempty interior
   (`target_interior_nonempty`).
2. `DiskCube.exists_ambient` applies Mathlib's ambient-homeomorphism lemma
   `exists_homeomorph_image_eq` (from `Mathlib/Analysis/Convex/GaugeRescale.lean`,
   for bounded convex sets with nonempty interiors, preserving interior, closure, and
   frontier) to the closed unit ball and `target L`, obtaining a self-homeomorphism
   `ambient L` of `V` mapping the ball onto the target and its frontier onto the
   target's frontier (`ambient_image`, `ambient_frontier`, `ambient_mem_iff`).
3. `DiskCube.homeomorph` composes `ambient L`, `L`, and `realCubeHomeomorph n` and
   restricts to the closed unit ball.
4. `DiskCube.boundary_iff` and `DiskCube.symm_boundary_iff` give the forward and
   inverse norm-one boundary tests via `frontier_closedBall` and
   `mem_sphere_zero_iff_norm`.

This file uses plain imports until its dependencies support the module system.

## Main definitions and results

* `DiskCube.homeomorph : DiskCylinder.Disk (E := V) ≃ₜ (Fin n → unitInterval)`: the
  closed unit ball of a finite-dimensional normed space is homeomorphic to the unit
  cube, via `L : V ≃L[ℝ] (Fin n → ℝ)`.
* `DiskCube.boundary_iff`: `homeomorph L z ∈ Cube.boundary (Fin n) ↔ ‖z‖ = 1`.

## References

* `Mathlib/Analysis/Convex/GaugeRescale.lean`, `exists_homeomorph_image_eq`
  (ambient homeomorphism between bounded convex bodies).
* `Lib/docs/C15-DISKCUBE.md` (typed ledger and extraction provenance).

## Tags

disk, cube, homeomorphism, normed space, boundary
-/

open Set Topology

noncomputable section

/-- The pulled-back cube: the inverse image of the real cube `realCubeSet n` under
the continuous linear equivalence `L`. -/
def DiskCube.target {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Set V :=
  L ⁻¹' Hurewicz.realCubeSet n

/-- The pulled-back cube is compact, as the preimage of the compact `realCubeSet`
under the homeomorphism `L`. -/
theorem DiskCube.target_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : IsCompact (target L) :=
  L.toHomeomorph.isCompact_preimage.mpr (Hurewicz.isCompact_realCubeSet n)

/-- The pulled-back cube is convex, as the linear preimage of the convex
`realCubeSet`. -/
theorem DiskCube.target_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Convex ℝ (target L) :=
  (Hurewicz.convex_realCubeSet n).linear_preimage L.toLinearMap

/-- The pulled-back cube has nonempty interior. -/
theorem DiskCube.target_interior_nonempty {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : (interior (target L)).Nonempty := by
  obtain ⟨v, hv⟩ := Hurewicz.interior_realCubeSet_nonempty n
  refine ⟨L.symm v, ?_⟩
  change L.symm v ∈ interior (L.toHomeomorph ⁻¹' Hurewicz.realCubeSet n)
  rw [← L.toHomeomorph.preimage_interior]
  change L (L.symm v) ∈ interior (Hurewicz.realCubeSet n)
  rwa [L.apply_symm_apply]

/-- There is an ambient self-homeomorphism of `V` simultaneously carrying the closed
unit ball onto `target L` and the ball's frontier onto the target's frontier. -/
theorem DiskCube.exists_ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ∃ e : V ≃ₜ V,
      e '' Metric.closedBall (0 : V) 1 = target L ∧
        e '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L) := by
  obtain ⟨e, _, he, hb⟩ :=
    exists_homeomorph_image_eq (convex_closedBall (0 : V) 1)
      (show (interior (Metric.closedBall (0 : V) 1)).Nonempty from
        ⟨0, Metric.ball_subset_interior_closedBall (by simp)⟩)
      ((ProperSpace.isCompact_closedBall (0 : V) 1).isVonNBounded ℝ) (target_convex L)
      (target_interior_nonempty L) ((target_compact L).isVonNBounded ℝ)
  exact
    ⟨e, by
      simpa only [Metric.isClosed_closedBall.closure_eq,
        (target_compact L).isClosed.closure_eq] using he,
      hb⟩

/-- The chosen ambient homeomorphism supplied by `DiskCube.exists_ambient`. -/
def DiskCube.ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : V ≃ₜ V :=
  Classical.choose (exists_ambient L)

/-- The ambient homeomorphism carries the closed unit ball onto `target L`. -/
theorem DiskCube.ambient_image {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' Metric.closedBall (0 : V) 1 = target L :=
  (Classical.choose_spec (exists_ambient L)).1

/-- The ambient homeomorphism carries the ball's frontier onto the target's
frontier. -/
theorem DiskCube.ambient_frontier {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L) :=
  (Classical.choose_spec (exists_ambient L)).2

/-- Membership test: `v` lies in the closed unit ball iff `L (ambient L v)` lies in
the real cube. -/
theorem DiskCube.ambient_mem_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (v : V) :
    v ∈ Metric.closedBall (0 : V) 1 ↔ L (ambient L v) ∈ Hurewicz.realCubeSet n := by
  change v ∈ Metric.closedBall (0 : V) 1 ↔ ambient L v ∈ target L
  rw [← ambient_image]
  exact ((ambient L).injective.mem_set_image).symm

/-- The disk–cube homeomorphism: the closed unit ball of `V` restricted through the
ambient homeomorphism, `L`, and `realCubeHomeomorph n`. -/
def DiskCube.homeomorph {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    DiskCylinder.Disk (E := V) ≃ₜ (Fin n → (unitInterval)) :=
  (((ambient L).trans L.toHomeomorph).subtype (ambient_mem_iff L)).trans
    (Hurewicz.realCubeHomeomorph n)

/-- Forward boundary test: the image of a ball point lies on the cube boundary iff
the point has norm one. -/
theorem DiskCube.boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ))
    (z : DiskCylinder.Disk (E := V)) :
    homeomorph L z ∈ Cube.boundary (Fin n) ↔ ‖(z : V)‖ = 1 := by
  change Hurewicz.realCubeHomeomorph n _ ∈ Cube.boundary (Fin n) ↔ _
  rw [Hurewicz.realCubeHomeomorph_mem_boundary_iff]
  change L (ambient L z.val) ∈ frontier (Hurewicz.realCubeSet n) ↔ _
  have hpre :
    L (ambient L z.val) ∈ frontier (Hurewicz.realCubeSet n) ↔
      ambient L z.val ∈ frontier (target L) := by
    change ambient L z.val ∈ L.toHomeomorph ⁻¹' frontier (Hurewicz.realCubeSet n) ↔ _
    rw [L.toHomeomorph.preimage_frontier]
    rfl
  rw [hpre, ← ambient_frontier]
  rw [(ambient L).injective.mem_set_image]
  rw [frontier_closedBall (0 : V) (one_ne_zero), mem_sphere_zero_iff_norm]

/-- Inverse boundary test: the inverse image of a cube point has norm one iff the
point lies on the cube boundary. -/
theorem DiskCube.symm_boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → (unitInterval)) :
    ‖((homeomorph L).symm z : V)‖ = 1 ↔ z ∈ Cube.boundary (Fin n) := by
  rw [← boundary_iff, Homeomorph.apply_symm_apply]

