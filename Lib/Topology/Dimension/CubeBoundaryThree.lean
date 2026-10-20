module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# The boundary of the three-cube

The boundary of the cube `[-1,1]³`, presented as the level set `‖x‖_∞ = 1` in `ℝ³`, is compact
and is homeomorphic to the Euclidean unit sphere `S²` by radial projection.  The two explicit
radial maps, normalisation by the Euclidean norm and normalisation by the maximum norm, are
mutually inverse and continuous.

This is the standard fact that the frontiers of two convex bodies with `0` in the interior are
homeomorphic, specialised to the cube and the ball in dimension three.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
* Mathlib's `gaugeRescaleHomeomorph` (`Mathlib/Analysis/Convex/GaugeRescale.lean`) for the
  general convex-body form
-/

@[expose] public section

set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- Euclidean three-space. -/
abbrev Ambient := EuclideanSpace ℝ (Fin 3)

/-- The maximum of the absolute coordinate values. -/
def maxAbs (x : Ambient) : ℝ := max |x 0| (max |x 1| |x 2|)

/-- `‖x‖∞ ≤ |x|`. -/
theorem maxAbs_le_norm (x : Ambient) : maxAbs x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := (Real.norm_eq_abs (x 0)).symm ▸ PiLp.norm_apply_le x 0
  have h1 : |x 1| ≤ ‖x‖ := (Real.norm_eq_abs (x 1)).symm ▸ PiLp.norm_apply_le x 1
  have h2 : |x 2| ≤ ‖x‖ := (Real.norm_eq_abs (x 2)).symm ▸ PiLp.norm_apply_le x 2
  exact max_le h0 (max_le h1 h2)

/-- `|x| ≤ √3 ‖x‖∞`. -/
theorem norm_le_sqrt_three_mul_maxAbs (x : Ambient) :
    ‖x‖ ≤ Real.sqrt 3 * maxAbs x := by
  have hm : 0 ≤ maxAbs x :=
    le_trans (abs_nonneg (x 0)) (le_max_left _ _)
  have h0 : |x 0| ≤ maxAbs x := le_max_left _ _
  have h1 : |x 1| ≤ maxAbs x := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : |x 2| ≤ maxAbs x := le_trans (le_max_right _ _) (le_max_right _ _)
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hm)]
  apply Real.sqrt_le_sqrt
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0sq : |x 0| ^ 2 ≤ maxAbs x ^ 2 := (sq_le_sq₀ (abs_nonneg _) hm).2 h0
  have h1sq : |x 1| ^ 2 ≤ maxAbs x ^ 2 := (sq_le_sq₀ (abs_nonneg _) hm).2 h1
  have h2sq : |x 2| ^ 2 ≤ maxAbs x ^ 2 := (sq_le_sq₀ (abs_nonneg _) hm).2 h2
  simp only [Real.norm_eq_abs]
  nlinarith

/-- Continuity of the maximum norm. -/
theorem continuous_maxAbs : Continuous maxAbs := by
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) 0).abs).max
    (((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) 1).abs).max
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) 2).abs))

/-- Positive homogeneity of the maximum norm. -/
theorem maxAbs_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (x : Ambient) :
    maxAbs (c • x) = c * maxAbs x := by
  simp only [maxAbs, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  rw [show max (c * |x 1|) (c * |x 2|) = c * max |x 1| |x 2| by
    simpa [mul_comm] using (max_mul_of_nonneg |x 1| |x 2| hc).symm]
  simpa [mul_comm] using (max_mul_of_nonneg |x 0| (max |x 1| |x 2|) hc).symm

/-- The level-set model of the cube boundary. -/
def boundary : Set Ambient := {x | maxAbs x = 1}

/-- The cube boundary with its Euclidean subspace topology. -/
abbrev Boundary := boundary

/-- One of the six coordinate faces. -/
def face (i : Fin 3) (σ : {r : ℝ // r = -1 ∨ r = 1}) : Set Ambient :=
  {x | x ∈ boundary ∧ x i = σ.1}

/-- Membership in a face. -/
theorem mem_face_iff (x : Ambient) (i : Fin 3) (σ : {r : ℝ // r = -1 ∨ r = 1}) :
    x ∈ face i σ ↔ x ∈ boundary ∧ x i = σ.1 := Iff.rfl

/-- Every boundary point belongs to a face. -/
theorem exists_mem_face {x : Ambient} (hx : x ∈ boundary) :
    ∃ (i : Fin 3) (σ : {r : ℝ // r = -1 ∨ r = 1}), x ∈ face i σ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun j ↦ |x j|) Finset.univ_nonempty
  have h0 := hi 0 (Finset.mem_univ _)
  have h1 := hi 1 (Finset.mem_univ _)
  have h2 := hi 2 (Finset.mem_univ _)
  have himax : |x i| = 1 := by
    apply le_antisymm
    · rw [← hx]
      fin_cases i <;> simp [maxAbs]
    · rw [← hx]
      exact max_le h0 (max_le h1 h2)
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp himax with hpos | hneg
  · exact ⟨i, ⟨1, Or.inr rfl⟩, hx, hpos⟩
  · exact ⟨i, ⟨-1, Or.inl rfl⟩, hx, hneg⟩

/-- The first basis vector lies on the boundary. -/
theorem boundary_nonempty : boundary.Nonempty := by
  refine ⟨EuclideanSpace.single 0 1, ?_⟩
  change max |(EuclideanSpace.single 0 1 : Ambient) 0|
    (max |(EuclideanSpace.single 0 1 : Ambient) 1|
      |(EuclideanSpace.single 0 1 : Ambient) 2|) = 1
  simp

/-- Heine--Borel compactness of the boundary. -/
theorem isCompact_boundary : IsCompact boundary := by
  -- The boundary is the closed preimage of `{1}`.
  have isClosed_boundary : IsClosed boundary := by
    exact isClosed_singleton.preimage continuous_maxAbs
  -- The second norm inequality gives a bounding ball.
  have isBounded_boundary : Bornology.IsBounded boundary :=
    (Metric.isBounded_iff_subset_ball 0).2 ⟨Real.sqrt 3 + 1, by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      change maxAbs x = 1 at hx
      refine lt_of_le_of_lt (norm_le_sqrt_three_mul_maxAbs x) ?_
      rw [hx, mul_one]
      exact lt_add_one (Real.sqrt 3)⟩
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_boundary, isBounded_boundary⟩

/-- The boundary is inhabited. -/
noncomputable instance instNonemptyBoundary : Nonempty Boundary := boundary_nonempty.to_subtype

/-- The boundary subtype is compact. -/
noncomputable instance instCompactSpaceBoundary : CompactSpace Boundary :=
  isCompact_iff_compactSpace.mp isCompact_boundary

/-- Boundary points have positive Euclidean norm. -/
theorem norm_pos_of_mem_boundary (x : Boundary) : 0 < ‖(x : Ambient)‖ := by
  have h := maxAbs_le_norm (x : Ambient)
  rw [x.property] at h
  exact lt_of_lt_of_le zero_lt_one h

/-- Sphere points have positive maximum norm. -/
theorem maxAbs_pos_of_mem_sphere (y : Metric.sphere (0 : Ambient) 1) :
    0 < maxAbs (y : Ambient) := by
  have hy : ‖(y : Ambient)‖ = 1 := by
    rw [← dist_zero_right]
    exact y.property
  have h := norm_le_sqrt_three_mul_maxAbs (y : Ambient)
  rw [hy] at h
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

/-- Radial normalization onto the sphere. -/
noncomputable def toSphere (x : Boundary) : Metric.sphere (0 : Ambient) 1 := by
  -- Euclidean normalization lands on the unit sphere.
  have normalize_mem_sphere :
      ‖(x : Ambient)‖⁻¹ • (x : Ambient) ∈ Metric.sphere (0 : Ambient) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2
      (norm_pos_of_mem_boundary x)), inv_mul_cancel₀ (ne_of_gt (norm_pos_of_mem_boundary x))]
  exact ⟨‖(x : Ambient)‖⁻¹ • (x : Ambient), normalize_mem_sphere⟩

/-- Maximum-norm normalization onto the cube. -/
noncomputable def fromSphere (y : Metric.sphere (0 : Ambient) 1) : Boundary := by
  -- Maximum-norm normalization lands on the boundary.
  have normalizeMax_mem_boundary :
      (maxAbs (y : Ambient))⁻¹ • (y : Ambient) ∈ boundary := by
    change maxAbs ((maxAbs (y : Ambient))⁻¹ • (y : Ambient)) = 1
    rw [maxAbs_smul_of_nonneg _ (inv_nonneg.2 (le_of_lt (maxAbs_pos_of_mem_sphere y))),
      inv_mul_cancel₀ (ne_of_gt (maxAbs_pos_of_mem_sphere y))]
  exact ⟨(maxAbs (y : Ambient))⁻¹ • (y : Ambient), normalizeMax_mem_boundary⟩

/-- The defining formula for Euclidean normalization onto the sphere. -/
theorem toSphere_apply (x : Boundary) :
    ((toSphere x : Metric.sphere (0 : Ambient) 1) : Ambient) =
      ‖(x : Ambient)‖⁻¹ • (x : Ambient) := rfl

/-- The defining formula for maximum-norm normalization onto the cube. -/
theorem fromSphere_apply (y : Metric.sphere (0 : Ambient) 1) :
    ((fromSphere y : Boundary) : Ambient) =
      (maxAbs (y : Ambient))⁻¹ • (y : Ambient) := rfl

/-- Explicit continuity of Euclidean normalization. -/
theorem continuous_toSphere : Continuous toSphere := by
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀
    (fun x ↦ ne_of_gt (norm_pos_of_mem_boundary x))).smul continuous_subtype_val

/-- Explicit continuity of maximum-norm normalization. -/
theorem continuous_fromSphere : Continuous fromSphere := by
  apply Continuous.subtype_mk
  exact ((continuous_maxAbs.comp continuous_subtype_val).inv₀
    (fun y ↦ ne_of_gt (maxAbs_pos_of_mem_sphere y))).smul continuous_subtype_val

/-- Maximum normalization after Euclidean normalization. -/
theorem fromSphere_toSphere (x : Boundary) : fromSphere (toSphere x) = x := by
  apply Subtype.ext
  rw [fromSphere_apply, toSphere_apply,
    maxAbs_smul_of_nonneg _ (inv_nonneg.2 (le_of_lt (norm_pos_of_mem_boundary x))),
    x.property, mul_one, smul_smul, inv_inv,
    mul_inv_cancel₀ (ne_of_gt (norm_pos_of_mem_boundary x)), one_smul]

/-- Euclidean normalization after maximum normalization. -/
theorem toSphere_fromSphere (y : Metric.sphere (0 : Ambient) 1) : toSphere (fromSphere y) = y := by
  apply Subtype.ext
  rw [toSphere_apply, fromSphere_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 (maxAbs_pos_of_mem_sphere y))]
  have hy : ‖(y : Ambient)‖ = 1 := by
    rw [← dist_zero_right]
    exact y.property
  rw [hy, mul_one, smul_smul, inv_inv,
    mul_inv_cancel₀ (ne_of_gt (maxAbs_pos_of_mem_sphere y)), one_smul]

/-- The explicit radial homeomorphism `Q ≃ₜ S²`. -/
noncomputable def homeomorphSphere : Boundary ≃ₜ Metric.sphere (0 : Ambient) 1 where
  toFun := toSphere
  invFun := fromSphere
  left_inv := fromSphere_toSphere
  right_inv := toSphere_fromSphere
  continuous_toFun := continuous_toSphere
  continuous_invFun := continuous_fromSphere

end TopologicalSpace.CubeBoundaryThree
