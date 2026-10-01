module
public import Lib.Geometry.Hyperbolic.Models
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped Manifold Bundle
namespace Hyperbolic
local notation "I" => 𝓘(ℝ, ℂ)

/-- Actual upper-half-plane metric inner products are the positive conformal multiplier times ordinary coordinate inner products. Textbook G05.I, lines 146–149. -/
theorem upperHalfPlaneMetric_inner_coordinates (z : UpperHalfPlane)
    (v w : TangentSpace I z) :
    upperHalfPlaneMetric.inner z v w = (z.im^2)⁻¹ * inner ℝ
      (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v)
      (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w) := by
  let u : ℂ := mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v
  let u' : ℂ := mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w
  rw [upperHalfPlaneMetric_inner, upperHalfPlaneTangentTensor_apply]
  change upperHalfPlaneCoordinateTensor z u u' = (z.im^2)⁻¹ * inner ℝ u u'
  rw [upperHalfPlaneCoordinateTensor_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [div_eq_mul_inv]
  ring

/-- The actual tangent metric norm is the square-root conformal multiplier times the coordinate norm, including zero vectors. Textbook G05.I, lines 149–151. -/
theorem upperHalfPlaneMetric_norm_coordinates (z : UpperHalfPlane)
    (v : TangentSpace I z) :
    letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    ‖v‖ = Real.sqrt ((z.im^2)⁻¹) *
      ‖mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v‖ := by
  letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  have hinner : inner ℝ v v = upperHalfPlaneMetric.inner z v v := rfl
  rw [norm_eq_sqrt_real_inner v,hinner,upperHalfPlaneMetric_inner_coordinates]
  rw [Real.sqrt_mul (inv_pos.mpr (sq_pos_of_pos z.im_pos)).le,
    real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

/-- Positive conformal scaling cancels in the normalized inner product for two nonzero tangent directions. Textbook G05.I, lines 150–155. -/
theorem upperHalfPlaneMetric_normalized_coordinates (z : UpperHalfPlane)
    (v w : TangentSpace I z) (hv : v ≠ 0) (hw : w ≠ 0) :
    letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    inner ℝ v w / (‖v‖ * ‖w‖) =
      inner ℝ (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v)
        (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w) /
      (‖mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v‖ *
        ‖mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w‖) := by
  letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  have hinner : inner ℝ v w = upperHalfPlaneMetric.inner z v w := rfl
  have hlam : 0 < (z.im^2)⁻¹ := inv_pos.mpr (sq_pos_of_pos z.im_pos)
  rw [hinner,upperHalfPlaneMetric_inner_coordinates,
    upperHalfPlaneMetric_norm_coordinates,upperHalfPlaneMetric_norm_coordinates]
  rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt hlam.le]
  exact mul_div_mul_left _ _ (ne_of_gt hlam)

/-- The actual metric angle agrees with the ordinary coordinate angle for nonzero directions. Textbook G05.I, lines 155–161. -/
theorem upperHalfPlaneMetric_angle_coordinates (z : UpperHalfPlane)
    (v w : TangentSpace I z) (hv : v ≠ 0) (hw : w ≠ 0) :
    letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    InnerProductGeometry.angle v w = InnerProductGeometry.angle
      (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v)
      (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w) := by
  letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  exact congrArg Real.arccos (upperHalfPlaneMetric_normalized_coordinates z v w hv hw)

/-- The actual hyperboloid model differential carries the same coordinate angle, using the existing metric transport. Textbook G05.I, lines 162–163. -/
theorem toHyperboloid_angle_coordinates (z : UpperHalfPlane)
    (v w : TangentSpace I z) (hv : v ≠ 0) (hw : w ≠ 0) :
    letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
      ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
      ⟨hyperboloidMetric.toRiemannianMetric⟩
    InnerProductGeometry.angle (mfderiv I I toHyperboloid z v)
      (mfderiv I I toHyperboloid z w) = InnerProductGeometry.angle
      (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z v)
      (mfderiv I I (fun q : UpperHalfPlane => (q : ℂ)) z w) := by
  letI : Bundle.RiemannianBundle (fun q : UpperHalfPlane => TangentSpace I q) :=
    ⟨upperHalfPlaneMetric.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun p : Hyperboloid => TangentSpace I p) :=
    ⟨hyperboloidMetric.toRiemannianMetric⟩
  exact ((toHyperboloid_norm_angle z).2.2.2 v w hv hw).trans
    (upperHalfPlaneMetric_angle_coordinates z v w hv hw)

end Hyperbolic
