/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.DiskDouble

/-!
# Hemisphere coordinates on the unit sphere

The unit sphere `Hemisphere.Sphere n` of `ℝⁿ⁺¹` (Mathlib's `Metric.sphere 0 1` in
`EuclideanSpace ℝ (Fin (n + 1))`) is the union of the two graphs
`x ↦ (±√(1 - ‖x‖²), x)` over the closed unit ball `Hemisphere.Ball n` of `ℝⁿ`
(`Hemisphere.point`). Each graph map is continuous and injective, and the two agree exactly over
the boundary sphere (`Hemisphere.point_false_eq_true_iff`), which exhibits the sphere as a
double of the disk (`Lib.Geometry.Manifold.Morse.SurgeryWindows.DiskDouble`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- The ambient Euclidean space of dimension `n`. -/
abbrev Hemisphere.Ambient (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

/-- The closed unit ball in `n` dimensions. -/
abbrev Hemisphere.Ball (n : ℕ) :=
  DiskDouble.Disk (Ambient n)

/-- The unit sphere in `n + 1` dimensions. -/
abbrev Hemisphere.Sphere (n : ℕ) :=
  Metric.sphere (0 : Ambient (n + 1)) 1

/-- The hemisphere height `√(1 − ‖x‖²)`. -/
def Hemisphere.radius {n : ℕ} (x : Ball n) : ℝ :=
  Real.sqrt (1 - ‖(x : Ambient n)‖ ^ 2)

/-- The radius squared is `1 − ‖x‖²`. -/
theorem Hemisphere.radius_sq {n : ℕ} (x : Ball n) :
    radius x ^ 2 = 1 - ‖(x : Ambient n)‖ ^ 2 := by
  apply Real.sq_sqrt
  have hx : ‖(x : Ambient n)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  nlinarith [norm_nonneg (x : Ambient n)]

/-- The hemisphere point above or below a ball point. -/
def Hemisphere.vector {n : ℕ} (b : Bool) (x : Ball n) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.cons (if b then radius x else -radius x) (x : Ambient n))

/-- The zeroth hemisphere vector. -/
@[simp]
theorem Hemisphere.vector_zero {n : ℕ} (b : Bool) (x : Ball n) :
    vector b x 0 = if b then radius x else -radius x :=
  rfl

/-- The successor hemisphere vector. -/
@[simp]
theorem Hemisphere.vector_succ {n : ℕ} (b : Bool) (x : Ball n) (i : Fin n) :
    vector b x i.succ = (x : Ambient n) i :=
  rfl

/-- The hemisphere vector has norm one. -/
theorem Hemisphere.vector_norm_sq {n : ℕ} (b : Bool) (x : Ball n) : ‖vector b x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ]
  rw [← EuclideanSpace.real_norm_sq_eq]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq] <;> rw [radius_sq] <;> ring

/-- A hemisphere point of the sphere. -/
def Hemisphere.point {n : ℕ} (b : Bool) (x : Ball n) : Sphere n :=
  ⟨vector b x, by
    rw [mem_sphere_zero_iff_norm]
    have h := vector_norm_sq b x
    nlinarith [norm_nonneg (vector b x)]⟩

/-- The hemisphere point at zero. -/
@[simp]
theorem Hemisphere.point_zero {n : ℕ} (b : Bool) (x : Ball n) :
    (point b x : Ambient (n + 1)) 0 = if b then radius x else -radius x :=
  rfl

/-- The hemisphere radius is continuous. -/
theorem Hemisphere.continuous_radius {n : ℕ} : Continuous (radius (n := n)) := by
  unfold radius
  fun_prop

/-- The hemisphere vector is continuous. -/
theorem Hemisphere.continuous_vector {n : ℕ} (b : Bool) : Continuous (vector (n := n) b) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases b
    · exact continuous_radius.neg
    · exact continuous_radius
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val

/-- The hemisphere point map is continuous. -/
theorem Hemisphere.continuous_point {n : ℕ} (b : Bool) : Continuous (point (n := n) b) :=
  (continuous_vector b).subtype_mk _

/-- Each hemisphere parametrization is injective. -/
theorem Hemisphere.point_injective {n : ℕ} (b : Bool) :
    Function.Injective (point (n := n) b) := by
  intro x y h
  apply Subtype.ext
  ext i
  exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h

/-- The hemisphere radius on the boundary. -/
@[simp]
theorem Hemisphere.radius_boundary {n : ℕ} (x : DiskDouble.Boundary (Ambient n)) :
    radius (DiskDouble.boundary (Ambient n) x) = 0 := by
  have hx : ‖(x : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp [radius, DiskDouble.boundary, hx]

/-- The two hemispheres agree on the boundary. -/
theorem Hemisphere.point_boundary {n : ℕ} (x : DiskDouble.Boundary (Ambient n)) :
    point Bool.false (DiskDouble.boundary (Ambient n) x) =
      point Bool.true (DiskDouble.boundary (Ambient n) x) := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rfl

/-- Hemisphere points coincide exactly at boundary points. -/
theorem Hemisphere.point_false_eq_true_iff {n : ℕ} (x y : Ball n) :
    point Bool.false x = point Bool.true y ↔
      ∃ z : DiskDouble.Boundary (Ambient n),
        x = DiskDouble.boundary (Ambient n) z ∧
          y = DiskDouble.boundary (Ambient n) z := by
  constructor
  · intro h
    have hxy : x = y := by
      apply Subtype.ext
      ext i
      exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h
    subst y
    have hr : radius x = 0 := by
      have hh := congrArg (fun z : Sphere n => (z : Ambient (n + 1)) 0) h
      simp only [point_zero, Bool.false_eq_true, ↓reduceIte] at hh
      linarith
    have hn : ‖(x : Ambient n)‖ = 1 := by
      have hs := radius_sq x
      rw [hr] at hs
      nlinarith [norm_nonneg (x : Ambient n)]
    exact ⟨⟨x, mem_sphere_zero_iff_norm.mpr hn⟩, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    exact point_boundary z

