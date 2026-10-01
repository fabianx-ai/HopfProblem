/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.HandleAttachment

/-!
# The interior of the new piece of a surgery

For a surgery boundary pair `d : SurgeryBoundaryPair N P R X Y` (Milnor, *Lectures on the
h-cobordism theorem*, §3: the level `Y` after surgery is the exterior together with the new
piece `D(N) × S(P)`), the new interior `d.NewInterior` is the complement of the new exterior.
It is open (`SurgeryBoundaryPair.isOpen_newInterior`), homeomorphic to
`OpenUnitBall N × S(P)` (`SurgeryBoundaryPair.newInteriorHomeomorph`), and contains the belt
sphere `{0} × S(P)` as the points with zero first coordinate
(`SurgeryBoundaryPair.newInteriorHomeomorph_mem_belt_iff`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- The open unit ball of a normed space. -/
abbrev PuncturedHandle.OpenUnitBall (N : Type*) [NormedAddCommGroup N] :=
  { x : N // ‖x‖ < 1 }

/-- The new level's interior: the complement plus the open new piece. -/
abbrev SurgeryBoundaryPair.NewInterior {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) : Set Y :=
  (Set.range d.newExterior)ᶜ

/-- The new interior is open. -/
theorem SurgeryBoundaryPair.isOpen_newInterior {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) : IsOpen d.NewInterior :=
  d.newExterior_closed.isClosed_range.isOpen_compl

/-- A new piece lies in the exterior exactly off the belt. -/
theorem SurgeryBoundaryPair.newPiece_mem_exterior_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (p : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P) :
    d.newPiece p ∈ Set.range d.newExterior ↔ ‖(p.1 : N)‖ = 1 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨q, -, rfl⟩ := (d.new_overlap r p).mp hr
    exact mem_sphere_zero_iff_norm.mp q.1.property
  · intro hp
    let q : PuncturedHandle.UnitSphere N × PuncturedHandle.UnitSphere P :=
      (⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2)
    exact ⟨d.boundary q, (d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩⟩

/-- Every new piece lies in the new interior. -/
theorem SurgeryBoundaryPair.newPiece_mem_newInterior_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (p : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P) :
    d.newPiece p ∈ d.NewInterior ↔ ‖(p.1 : N)‖ < 1 := by
  change ¬d.newPiece p ∈ Set.range d.newExterior ↔ _
  rw [d.newPiece_mem_exterior_iff]
  constructor
  · intro hp
    rcases lt_or_eq_of_le p.1.property with h | h
    · exact h
    · exact (hp h).elim
  · exact fun h => h.ne

/-- The new interior lies in the union of the exterior and new piece. -/
theorem SurgeryBoundaryPair.newInterior_subset_range {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y) :
    d.NewInterior ⊆ Set.range d.newPiece := by
  intro y hy
  have hc : y ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by rw [d.new_cover]; trivial
  exact hc.resolve_left hy

/-- The parametrization of the new interior by the open handle. -/
def SurgeryBoundaryPair.newInteriorParameter {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) :
    (PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) ≃ₜ
      (d.newPiece ⁻¹' d.NewInterior)
    where
  toFun p := ⟨(⟨p.1, p.1.property.le⟩, p.2), (d.newPiece_mem_newInterior_iff _).mpr p.1.property⟩
  invFun p := (⟨p.val.1, (d.newPiece_mem_newInterior_iff _).mp p.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The open new handle is homeomorphic to the new interior. -/
def SurgeryBoundaryPair.newInteriorHomeomorph {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) :
    (PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) ≃ₜ
      d.NewInterior :=
  d.newInteriorParameter.trans
    (d.newPiece_closed.isEmbedding.homeomorphOfSubsetRange d.newInterior_subset_range)

/-- Belt-sphere points lie in the new interior. -/
theorem SurgeryBoundaryPair.beltSphere_mem_newInterior {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (v : PuncturedHandle.UnitSphere P) : d.beltSphere v ∈ d.NewInterior := by
  apply (d.newPiece_mem_newInterior_iff (PuncturedHandle.ballZero, v)).mpr
  simp [PuncturedHandle.ballZero]

/-- A new-interior point lies on the belt exactly at the core. -/
theorem SurgeryBoundaryPair.newInteriorHomeomorph_mem_belt_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (p : PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) :
    (d.newInteriorHomeomorph p : Y) ∈ Set.range d.beltSphere ↔ (p.1 : N) = 0 :=
  d.newPiece_mem_belt_iff (⟨p.1, p.1.property.le⟩, p.2)

