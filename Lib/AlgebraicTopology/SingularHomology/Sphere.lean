/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The unit sphere: charts, latitudes, and connectedness

The unit sphere `UnitSphere n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` with the
elementary computations used throughout the sphere-homology files:

* stereographic presentations and the equator/latitude decomposition
  (`Latitude.height`, `Latitude.point`, `Latitude.point_surjective`: every point off the
  equator is on a unique latitude);
* `unitSphere_pathConnectedSpace` for `n ≥ 1`.

Consumed by `Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean` (the homology of
`Sⁿ`) and `Lib/AlgebraicTopology/SingularHomology/Suspension.lean` (sphere-circle
dictionary).

## Main definitions and results

* `SphereHomology.UnitSphere n` : the unit sphere of `EuclideanSpace ℝ (Fin (n+1))`.
* `SphereHomology.Latitude.*` : the latitude decomposition.
* `SphereHomology.unitSphere_pathConnectedSpace` : path connectedness for `n ≥ 1`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.2 (sphere as two charts)

## Tags

unit sphere, latitudes, path connectedness
-/



open Set Function Filter Manifold Topology

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### The unit sphere -/

/-- The unit sphere in `EuclideanSpace ℝ (Fin (n+1))`. -/
abbrev SphereHomology.UnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Unit-sphere points have norm one. -/
@[simp]
theorem SphereHomology.unitSphere_norm {n : ℕ} (x : UnitSphere n) : ‖x.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

/-- The chosen basepoint of the sphere. -/
def SphereHomology.basePoint (n : ℕ) : UnitSphere n :=
  ⟨PiLp.single 2 (0 : Fin (n + 1)) (1 : ℝ), by simp⟩

/-- Every unit sphere is nonempty. -/
instance SphereHomology.unitSphere_nonempty (n : ℕ) : Nonempty (UnitSphere n) :=
  ⟨basePoint n⟩

/-- Every unit sphere is compact. -/
instance SphereHomology.unitSphere_compactSpace (n : ℕ) : CompactSpace (UnitSphere n) :=
  inferInstance

/-! ### Latitude coordinates -/

/-- The height coordinate `-1` to `1` of a latitude parameter. -/
def SphereHomology.Latitude.height (t : unitInterval) : ℝ :=
  2 * (t : ℝ) - 1

/-- The radius of the latitude circle at parameter `t`. -/
def SphereHomology.Latitude.radius (t : unitInterval) : ℝ :=
  Real.sqrt (1 - height t ^ 2)

/-- The squared height is at most one. -/
theorem SphereHomology.Latitude.height_sq_le_one (t : unitInterval) : height t ^ 2 ≤ 1 := by
  have h0 := t.property.1
  have h1 := t.property.2
  dsimp [height]
  nlinarith

/-- The radius squared is `1 - height²`. -/
theorem SphereHomology.Latitude.radius_sq (t : unitInterval) : radius t ^ 2 = 1 - height t ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (height_sq_le_one t))

/-- The latitude radius is nonnegative. -/
theorem SphereHomology.Latitude.radius_nonneg (t : unitInterval) : 0 ≤ radius t :=
  Real.sqrt_nonneg _

/-- The height at parameter `0` is `-1`. -/
@[simp]
theorem SphereHomology.Latitude.height_zero : height 0 = -1 := by norm_num [height]

/-- The height at parameter `1` is `1`. -/
@[simp]
theorem SphereHomology.Latitude.height_one : height 1 = 1 := by norm_num [height]

/-- The radius at parameter `0` is `0`. -/
@[simp]
theorem SphereHomology.Latitude.radius_zero : radius 0 = 0 := by simp [radius]

/-- The radius at parameter `1` is `0`. -/
@[simp]
theorem SphereHomology.Latitude.radius_one : radius 1 = 0 := by simp [radius]

/-- The height function is injective on the interval. -/
theorem SphereHomology.Latitude.height_injective : Function.Injective height := by
  intro t s h
  apply Subtype.ext
  dsimp [height] at h
  linarith

/-- Interior parameters have positive radius. -/
theorem SphereHomology.Latitude.radius_pos_of_interior (t : unitInterval) (h0 : t ≠ 0)
    (h1 : t ≠ 1) : 0 < radius t := by
  have ht0 : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.property.1
      (by
        intro h
        exact h0 (Subtype.ext h.symm))
  have ht1 : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.property.2
      (by
        intro h
        exact h1 (Subtype.ext h))
  apply Real.sqrt_pos.mpr
  dsimp [height]
  nlinarith

/-- The height function is continuous. -/
@[continuity, fun_prop]
theorem SphereHomology.Latitude.height_continuous : Continuous height := by
  unfold height
  fun_prop

/-- The radius function is continuous. -/
@[continuity, fun_prop]
theorem SphereHomology.Latitude.radius_continuous : Continuous radius := by
  unfold radius
  exact Real.continuous_sqrt.comp (continuous_const.sub (height_continuous.pow 2))

/-- The `n+2`-dimensional unit vector at latitude `t` over `x`. -/
def SphereHomology.Latitude.vector (n : ℕ) (t : unitInterval) (x : SphereHomology.UnitSphere n) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 (Fin.cons (height t) (fun i => radius t * x.val i))

/-- The first coordinate of the latitude vector is the height. -/
@[simp]
theorem SphereHomology.Latitude.vector_zero (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) : vector n t x 0 = height t :=
  rfl

/-- The remaining coordinates are the radius times the sphere coordinates. -/
@[simp]
theorem SphereHomology.Latitude.vector_succ (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) (i : Fin (n + 1)) :
    vector n t x i.succ = radius t * x.val i :=
  rfl

/-- The latitude vector has norm one. -/
theorem SphereHomology.Latitude.vector_norm_sq (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) : ‖vector n t x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ, mul_pow]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, SphereHomology.unitSphere_norm]
  rw [one_pow, mul_one, radius_sq]
  ring

/-- The latitude vector lies on the unit sphere. -/
theorem SphereHomology.Latitude.vector_mem_sphere (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) :
    vector n t x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
  have hn := vector_norm_sq n t x
  have hnorm : ‖vector n t x‖ = 1 := by nlinarith [norm_nonneg (vector n t x)]
  simpa only [Metric.mem_sphere, dist_zero_right] using hnorm

/-- The point of the `n+1`-sphere at latitude `t` over `x`. -/
def SphereHomology.Latitude.point (n : ℕ) (t : unitInterval) (x : SphereHomology.UnitSphere n) :
    SphereHomology.UnitSphere (n + 1) :=
  ⟨vector n t x, vector_mem_sphere n t x⟩

/-- The latitude vector is continuous in both parameters. -/
@[continuity, fun_prop]
theorem SphereHomology.Latitude.vector_continuous (n : ℕ) :
    Continuous (fun p : unitInterval × SphereHomology.UnitSphere n => vector n p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 2) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact height_continuous.comp continuous_fst
  · exact
      (radius_continuous.comp continuous_fst).mul
        ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) j).comp
          (continuous_subtype_val.comp continuous_snd))

/-- The latitude point is continuous in both parameters. -/
@[continuity, fun_prop]
theorem SphereHomology.Latitude.point_continuous (n : ℕ) :
    Continuous (fun p : unitInterval × SphereHomology.UnitSphere n => point n p.1 p.2) :=
  (vector_continuous n).subtype_mk _

/-- At parameter `0` all latitude points collapse. -/
theorem SphereHomology.Latitude.point_zero_eq (n : ℕ) (x y : SphereHomology.UnitSphere n) :
    point n 0 x = point n 0 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radius 0 * x.val j = radius 0 * y.val j
    rw [radius_zero, MulZeroClass.zero_mul, MulZeroClass.zero_mul]

/-- At parameter `1` all latitude points collapse. -/
theorem SphereHomology.Latitude.point_one_eq (n : ℕ) (x y : SphereHomology.UnitSphere n) :
    point n 1 x = point n 1 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radius 1 * x.val j = radius 1 * y.val j
    rw [radius_one, MulZeroClass.zero_mul, MulZeroClass.zero_mul]

/-- Two latitude points agree exactly when parameters coincide and, in the interior, base points do. -/
theorem SphereHomology.Latitude.point_eq_iff (n : ℕ) (t s : unitInterval)
    (x y : SphereHomology.UnitSphere n) :
    point n t x = point n s y ↔ t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) := by
  constructor
  · intro h
    have hh := congrArg (fun p : SphereHomology.UnitSphere (n + 1) => p.val 0) h
    change height t = height s at hh
    have ht : t = s := height_injective hh
    subst s
    refine ⟨rfl, ?_⟩
    by_cases h0 : t = 0
    · exact Or.inl h0
    by_cases h1 : t = 1
    · exact Or.inr (Or.inl h1)
    refine Or.inr (Or.inr ?_)
    ext i
    have hi := congrArg (fun p : SphereHomology.UnitSphere (n + 1) => p.val i.succ) h
    change radius t * x.val i = radius t * y.val i at hi
    exact mul_left_cancel₀ (ne_of_gt (radius_pos_of_interior t h0 h1)) hi
  · rintro ⟨rfl, h0 | h1 | rfl⟩
    · subst t
      exact point_zero_eq n x y
    · subst t
      exact point_one_eq n x y
    · rfl

/-! ### The latitude parametrization inverse -/

/-- The tail coordinates of a sphere point. -/
def SphereHomology.Latitude.tail (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => y.val i.succ)

/-- The tail extracts the shifted coordinates. -/
@[simp]
theorem SphereHomology.Latitude.tail_apply (n : ℕ) (y : SphereHomology.UnitSphere (n + 1))
    (i : Fin (n + 1)) : tail n y i = y.val i.succ :=
  rfl

/-- The head and tail split the unit norm. -/
theorem SphereHomology.Latitude.head_tail_norm_sq (n : ℕ)
    (y : SphereHomology.UnitSphere (n + 1)) : y.val 0 ^ 2 + ‖tail n y‖ ^ 2 = 1 := by
  have h : ‖y.val‖ ^ 2 = 1 := by rw [SphereHomology.unitSphere_norm, one_pow]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [tail_apply] using h

/-- The head coordinate lies between `-1` and `1`. -/
theorem SphereHomology.Latitude.head_bounds (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    -1 ≤ y.val 0 ∧ y.val 0 ≤ 1 := by
  have h := head_tail_norm_sq n y
  constructor
  · nlinarith [sq_nonneg ‖tail n y‖, sq_nonneg (y.val 0 + 1)]
  · nlinarith [sq_nonneg ‖tail n y‖, sq_nonneg (y.val 0 - 1)]

/-- The latitude parameter recovered from the head coordinate. -/
def SphereHomology.Latitude.parameter (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    unitInterval :=
  ⟨(y.val 0 + 1) / 2, by
    have h := head_bounds n y
    constructor <;> linarith [h.1, h.2]⟩

/-- The recovered parameter's height is the head coordinate. -/
@[simp]
theorem SphereHomology.Latitude.height_parameter (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    height (parameter n y) = y.val 0 := by
  change 2 * ((y.val 0 + 1) / 2) - 1 = y.val 0
  ring

/-- The recovered radius is the tail norm. -/
theorem SphereHomology.Latitude.radius_parameter_eq_norm_tail (n : ℕ)
    (y : SphereHomology.UnitSphere (n + 1)) : radius (parameter n y) = ‖tail n y‖ := by
  apply (sq_eq_sq₀ (radius_nonneg _) (norm_nonneg _)).mp
  rw [radius_sq, height_parameter]
  linarith [head_tail_norm_sq n y]

/-- Every sphere point is a latitude point. -/
theorem SphereHomology.Latitude.point_surjective (n : ℕ) :
    Function.Surjective (fun p : unitInterval × SphereHomology.UnitSphere n => point n p.1 p.2) :=
  by
  intro y
  let t := parameter n y
  have hr := radius_parameter_eq_norm_tail n y
  by_cases hzero : radius t = 0
  · have ht : tail n y = 0 := norm_eq_zero.mp (hr.symm.trans hzero)
    refine ⟨(t, SphereHomology.basePoint n), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact height_parameter n y
    · change radius t * (SphereHomology.basePoint n).val j = y.val j.succ
      rw [hzero, MulZeroClass.zero_mul]
      have hj := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v j) ht
      change y.val j.succ = 0 at hj
      exact hj.symm
  · let v : EuclideanSpace ℝ (Fin (n + 1)) := (radius t)⁻¹ • tail n y
    have hv : ‖v‖ = 1 := by
      calc
        ‖v‖ = |(radius t)⁻¹| * ‖tail n y‖ := norm_smul _ _
        _ = (radius t)⁻¹ * radius t := by rw [abs_inv, abs_of_nonneg (radius_nonneg t), ← hr]
        _ = 1 := inv_mul_cancel₀ hzero
    let x : SphereHomology.UnitSphere n :=
      ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
    refine ⟨(t, x), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact height_parameter n y
    · change radius t * ((radius t)⁻¹ * tail n y j) = y.val j.succ
      rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul, tail_apply]
