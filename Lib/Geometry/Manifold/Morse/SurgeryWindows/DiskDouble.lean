/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.HandleAttachment

/-!
# The double of a disk along a boundary homeomorphism

For a normed space `E` with closed unit ball `DiskDouble.Disk E` and unit sphere
`DiskDouble.Boundary E`, the twisted double `DiskDouble.Space e` glues two copies of the disk
along a homeomorphism `e` of the sphere. `DiskDouble.homeomorphUntwisted` shows it is
homeomorphic to the untwisted double, by extending `e⁻¹` radially over the second disk
(the Alexander trick, `RadialExtension.closedBallHomeomorph`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- The closed unit disk. -/
abbrev DiskDouble.Disk (E : Type*) [NormedAddCommGroup E] :=
  Metric.closedBall (0 : E) 1

/-- The boundary sphere of the disk. -/
abbrev DiskDouble.Boundary (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

/-- A boundary point included into the disk. -/
def DiskDouble.boundary (E : Type*) [NormedAddCommGroup E] (x : Boundary E) : Disk E :=
  ⟨x, Metric.sphere_subset_closedBall x.property⟩

/-- The relation gluing two disks along a boundary homeomorphism. -/
def DiskDouble.Rel {E : Type*} [NormedAddCommGroup E] (e : Boundary E ≃ₜ Boundary E) :
    Disk E ⊕ Disk E → Disk E ⊕ Disk E → Prop
  | .inl x, .inr y => ∃ z : Boundary E, x = boundary E z ∧ y = boundary E (e z)
  | _, _ => False

/-- The double of a disk along a boundary homeomorphism. -/
abbrev DiskDouble.Space {E : Type*} [NormedAddCommGroup E] (e : Boundary E ≃ₜ Boundary E) :=
  Quot (DiskDouble.Rel e)

/-- The twist moved onto the second disk. -/
def DiskDouble.untwist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) : Disk E ⊕ Disk E ≃ₜ Disk E ⊕ Disk E :=
  (Homeomorph.refl (Disk E)).sumCongr (RadialExtension.closedBallHomeomorph e.symm)

/-- The twisted relation is the untwisted identity relation. -/
theorem DiskDouble.rel_untwist_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) (x y : Disk E ⊕ Disk E) :
    DiskDouble.Rel e x y ↔
      DiskDouble.Rel (Homeomorph.refl (Boundary E)) (untwist e x) (untwist e y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => rfl
    | inr
      y =>
      change
        (∃ z, x = boundary E z ∧ y = boundary E (e z)) ↔
          ∃ z,
            x = boundary E z ∧ RadialExtension.closedBallHomeomorph e.symm y = boundary E z
      constructor
      · rintro ⟨z, rfl, rfl⟩
        refine ⟨z, rfl, ?_⟩
        simp [boundary]
      · rintro ⟨z, hx, hy⟩
        refine ⟨z, hx, ?_⟩
        apply (RadialExtension.closedBallHomeomorph e.symm).injective
        rw [hy]
        simp [boundary]
  | inr x => cases y <;> rfl

/-- A twisted double is homeomorphic to the untwisted double. -/
def DiskDouble.homeomorphUntwisted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) : Space e ≃ₜ Space (Homeomorph.refl (Boundary E)) :=
  Homeomorph.Quot.congr (untwist e) (rel_untwist_iff e)

