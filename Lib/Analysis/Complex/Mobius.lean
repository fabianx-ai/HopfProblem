/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Instances.RiemannSphere

/-!
# The Möbius dictionary of the Riemann sphere

The Möbius transformations of the Riemann sphere and their action data: reciprocal,
affine biholomorphisms, the disc/half-plane homeomorphisms, and the finite-image
parametrization — the three-point normalization toolkit of Ahlfors Ch. 3–4.

## Main definitions and results

* `RiemannSphere.reciprocal`, `RiemannSphere.affineBiholomorph_coe` : the basic sphere maps.
* `RiemannSphere.closedDiscHalfPlaneHomeomorph_sphere` : disc ↔ half-plane.
* `RiemannSphere.finiteImageHomeomorph` : the finite-image presentation.

## References

* [Lars Ahlfors, *Complex Analysis*][ahlfors], Ch. 3 §3 and Ch. 4

## Tags

Möbius transformation, Riemann sphere, disc half-plane
-/



open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Biholomorphisms of the Riemann sphere -/

/-- A holomorphic bijection of the Riemann sphere with holomorphic inverse. -/
abbrev RiemannSphere.Biholomorph :=
  Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) RiemannSphere RiemannSphere ω

/-- The reciprocal map `z ↦ 1/z` on the sphere. -/
def RiemannSphere.reciprocal (p : RiemannSphere) : RiemannSphere :=
  p.elim ((0 : ℂ) : RiemannSphere) infinityParametrization

/-- The reciprocal computes `1/z` on finite points. -/
@[simp]
theorem RiemannSphere.reciprocal_coe (z : ℂ) :
    reciprocal (z : RiemannSphere) = infinityParametrization z :=
  rfl

/-- The reciprocal swaps `0` and `∞`. -/
@[simp]
theorem RiemannSphere.reciprocal_infinityParametrization (z : ℂ) :
    reciprocal (infinityParametrization z) = (z : RiemannSphere) := by
  have hinfty : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  by_cases hz : z = 0
  · subst z
    simp [hinfty]
  · rw [infinityParametrization_of_ne hz, reciprocal_coe,
      infinityParametrization_of_ne (inv_ne_zero hz), inv_inv]

/-- The reciprocal is an involution. -/
theorem RiemannSphere.reciprocal_involutive : Function.Involutive reciprocal := by
  have hinfty : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  intro p
  induction p using OnePoint.rec with
  | infty => simp [hinfty]
  | coe z => simp []

/-- The reciprocal is holomorphic. -/
theorem RiemannSphere.reciprocal_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω reciprocal := by
  apply standardCharts.contMDiff_of_comp_affineMaps (modelWithCornersSelf ℂ ℂ)
  intro b
  have he : reciprocal ∘ standardCharts.affineMap b = standardCharts.affineMap (!b) := by
    funext z
    cases b
    · rfl
    · exact reciprocal_infinityParametrization z
  rw [he]
  exact standardCharts.affineMap_holomorphic (!b)

/-- The reciprocal as a biholomorphism. -/
def RiemannSphere.reciprocalBiholomorph : Biholomorph
    where
  toEquiv := reciprocal_involutive.toPerm reciprocal
  contMDiff_toFun := reciprocal_holomorphic
  contMDiff_invFun := reciprocal_holomorphic

/-- The reciprocal biholomorphism computes `1/z`. -/
@[simp]
theorem RiemannSphere.reciprocalBiholomorph_apply (p : RiemannSphere) :
    reciprocalBiholomorph p = reciprocal p :=
  rfl

/-- The complex affine homeomorphism `z ↦ az + b`. -/
def RiemannSphere.affineComplexHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)

/-- The affine map `z ↦ az + b` on the sphere. -/
def RiemannSphere.affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : RiemannSphere ≃ₜ RiemannSphere :=
  (affineComplexHomeomorph a b ha).onePointCongr

/-- The affine map computes `az + b` on finite points. -/
@[simp]
theorem RiemannSphere.affineHomeomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    RiemannSphere.affineHomeomorph a b ha (z : RiemannSphere) =
      ((a * z + b : ℂ) : RiemannSphere) :=
  rfl

/-- The affine map fixes `∞`. -/
theorem RiemannSphere.affineHomeomorph_infinityParametrization (a b z : ℂ) (ha : a ≠ 0)
    (hz : a + b * z ≠ 0) :
    RiemannSphere.affineHomeomorph a b ha (infinityParametrization z) =
      infinityParametrization (z / (a + b * z)) := by
  have hinfty :
    RiemannSphere.affineHomeomorph a b ha ((OnePoint.infty) : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) :=
    rfl
  by_cases hz0 : z = 0
  · subst z
    simp [hinfty]
  · rw [infinityParametrization_of_ne hz0, affineHomeomorph_coe,
      infinityParametrization_of_ne (div_ne_zero hz0 hz)]
    congr 1
    field_simp

/-- The affine map is holomorphic. -/
theorem RiemannSphere.affineHomeomorph_holomorphic (a b : ℂ) (ha : a ≠ 0) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (RiemannSphere.affineHomeomorph a b ha) := by
  apply standardCharts.contMDiff_of_comp_affineMaps (modelWithCornersSelf ℂ ℂ)
  intro chart
  cases chart
  · have hc : ContDiff ℂ ω (fun z : ℂ => a * z + b) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    exact (standardCharts.affineMap_holomorphic Bool.false).comp hc.contMDiff
  · intro z
    by_cases hz : z = 0
    · subst z
      have hd : ContDiffAt ℂ ω (fun w : ℂ => w / (a + b * w)) 0 :=
        contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
          (by simpa using ha)
      have hc :
        ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
          (fun w : ℂ => infinityParametrization (w / (a + b * w))) 0 :=
        (standardCharts.affineMap_holomorphic Bool.true).contMDiffAt.comp 0 hd.contMDiffAt
      apply hc.congr_of_eventuallyEq
      have hn : ∀ᶠ w : ℂ in 𝓝 0, a + b * w ≠ 0 :=
        (isOpen_ne_fun (continuous_const.add (continuous_const.mul continuous_id))
              continuous_const).mem_nhds
          (by simpa using ha)
      filter_upwards [hn] with w hw
      exact affineHomeomorph_infinityParametrization a b w ha hw
    · have hd : ContDiffAt ℂ ω (fun w : ℂ => a * w⁻¹ + b) z :=
        (contDiffAt_const.mul (contDiffAt_inv ℂ hz)).add contDiffAt_const
      have hc :
        ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
          (fun w : ℂ => ((a * w⁻¹ + b : ℂ) : RiemannSphere)) z :=
        (standardCharts.affineMap_holomorphic Bool.false).contMDiffAt.comp z hd.contMDiffAt
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
      change w ≠ 0 at hw
      change RiemannSphere.affineHomeomorph a b ha (infinityParametrization w) = _
      rw [infinityParametrization_of_ne hw, affineHomeomorph_coe]

/-- The inverse affine map is affine. -/
theorem RiemannSphere.affineHomeomorph_symm_eq (a b : ℂ) (ha : a ≠ 0) :
    ⇑(RiemannSphere.affineHomeomorph a b ha).symm =
      RiemannSphere.affineHomeomorph a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha) := by
  funext p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe
    z =>
    change ((a⁻¹ * (z - b) : ℂ) : RiemannSphere) = ((a⁻¹ * z + -a⁻¹ * b : ℂ) : RiemannSphere)
    congr 1
    ring

/-- The affine map as a biholomorphism. -/
def RiemannSphere.affineBiholomorph (a b : ℂ) (ha : a ≠ 0) : Biholomorph
    where
  toEquiv := (RiemannSphere.affineHomeomorph a b ha).toEquiv
  contMDiff_toFun := affineHomeomorph_holomorphic a b ha
  contMDiff_invFun := by
    change
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (RiemannSphere.affineHomeomorph a b ha).symm
    rw [affineHomeomorph_symm_eq]
    exact affineHomeomorph_holomorphic a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha)

/-- The affine biholomorphism computes `az + b`. -/
@[simp]
theorem RiemannSphere.affineBiholomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha (z : RiemannSphere) = ((a * z + b : ℂ) : RiemannSphere) :=
  rfl

/-- The cross-ratio scale factor is nonzero. -/
theorem RiemannSphere.crossRatioScale_ne_zero (a b c : ℂ) (hab : a ≠ b) (hbc : b ≠ c) :
    (b - c) / (b - a) ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hab.symm)

/-- The cross-ratio residue factor is nonzero. -/
theorem RiemannSphere.crossRatioResidue_ne_zero (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : (c - a) * ((b - c) / (b - a)) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hac.symm) (crossRatioScale_ne_zero a b c hab hbc)

/-- The biholomorphism sending three points to `0, 1, ∞`. -/
def RiemannSphere.threePointBiholomorph (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Biholomorph :=
  ((affineBiholomorph 1 (-c) one_ne_zero).trans reciprocalBiholomorph).trans
    (affineBiholomorph ((c - a) * ((b - c) / (b - a))) ((b - c) / (b - a))
      (crossRatioResidue_ne_zero a b c hab hac hbc))

/-- The three-point biholomorphism computes the cross ratio. -/
theorem RiemannSphere.threePointBiholomorph_coe (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (z : ℂ) (hz : z ≠ c) :
    threePointBiholomorph a b c hab hac hbc (z : RiemannSphere) =
      ((((z - a) * (b - c)) / ((z - c) * (b - a)) : ℂ) : RiemannSphere) := by
  change
    affineBiholomorph _ _ _
        (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (z : RiemannSphere))) =
      _
  simp only [affineBiholomorph_coe, one_mul, ← sub_eq_add_neg, reciprocalBiholomorph_apply,
    reciprocal_coe, infinityParametrization_of_ne (sub_ne_zero.mpr hz), affineBiholomorph_coe]
  congr 1
  field_simp
  ring

/-- The three-point map sends the third point to `1`. -/
@[simp]
theorem RiemannSphere.threePointBiholomorph_third (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    threePointBiholomorph a b c hab hac hbc (c : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) := by
  have hinfty (a b : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha ((OnePoint.infty) : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) :=
    rfl
  have hreciprocal : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  change
    affineBiholomorph _ _ _
        (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (c : RiemannSphere))) =
      _
  simp [hinfty]

/-- The three-point map sends its pole point to `∞`. -/
@[simp]
theorem RiemannSphere.threePointBiholomorph_infty (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    threePointBiholomorph a b c hab hac hbc ((OnePoint.infty) : RiemannSphere) =
      (((b - c) / (b - a) : ℂ) : RiemannSphere) := by
  have hinfty (a b : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha ((OnePoint.infty) : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) :=
    rfl
  have hreciprocal : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  change
    affineBiholomorph _ _ _
        (reciprocalBiholomorph
          (affineBiholomorph 1 (-c) one_ne_zero ((OnePoint.infty) : RiemannSphere))) =
      _
  simp [hinfty, hreciprocal]

/-! ### The cross ratio and the Möbius circle -/

/-- The cross ratio of four points. -/
def RiemannSphere.MobiusCircle.crossRatio (a b c z : ℂ) : ℂ :=
  ((z - a) * (b - c)) / ((z - c) * (b - a))

/-- The Möbius circle coefficient. -/
def RiemannSphere.MobiusCircle.coefficient (a b c : ℂ) : ℂ :=
  (b - c) / (b - a)

/-- The orientation factor of a Möbius circle. -/
def RiemannSphere.MobiusCircle.orientation (a b c : ℂ) : ℝ :=
  -(coefficient a b c).im

/-- The cross ratio equals the coefficient times the unit factor. -/
theorem RiemannSphere.MobiusCircle.crossRatio_eq_coefficient (a b c z : ℂ) :
    crossRatio a b c z = coefficient a b c * ((z - a) / (z - c)) := by
  simp only [crossRatio, coefficient, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The circle coefficient is nonzero. -/
theorem RiemannSphere.MobiusCircle.coefficient_ne_zero {a b c : ℂ} (hba : b ≠ a) (hbc : b ≠ c) :
    coefficient a b c ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hba)

/-- The unit factor is nonzero. -/
theorem RiemannSphere.MobiusCircle.unit_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

/-- The coefficient times the conjugate identity. -/
theorem RiemannSphere.MobiusCircle.coefficient_mul_eq_conj_mul {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) :
    coefficient a b c * a = conj (coefficient a b c) * c := by
  have ha0 := unit_ne_zero ha
  have hb0 := unit_ne_zero hb
  have hc0 := unit_ne_zero hc
  have hba0 := sub_ne_zero.mpr hba
  simp only [coefficient, map_div₀, map_sub, ← Complex.inv_eq_conj ha, ← Complex.inv_eq_conj hb,
    ← Complex.inv_eq_conj hc]
  field_simp
  ring

/-- The orientation factor is nonzero. -/
theorem RiemannSphere.MobiusCircle.orientation_ne_zero {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) : orientation a b c ≠ 0 := by
  intro h
  have him : (coefficient a b c).im = 0 := neg_eq_zero.mp h
  have hd := coefficient_mul_eq_conj_mul ha hb hc hba
  rw [Complex.conj_eq_iff_im.mpr him] at hd
  exact hac (mul_left_cancel₀ (coefficient_ne_zero hba hbc) hd)

/-- The imaginary part of the circle numerator. -/
theorem RiemannSphere.MobiusCircle.numerator_im {a c d : ℂ} (hc : ‖c‖ = 1)
    (hd : d * a = conj d * c) (z : ℂ) :
    (d * (z - a) * conj (z - c)).im = d.im * (Complex.normSq z - 1) := by
  have hcross : conj (d * z * conj c) = conj d * c * conj z := by
    simp only [map_mul, starRingEnd_self_apply]
    ring
  have hconst : conj d * c * conj c = conj d := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  have heq :
    d * (z - a) * conj (z - c) =
      d * (Complex.normSq z : ℂ) - (d * z * conj c + conj (d * z * conj c)) + conj d := by
    calc
      d * (z - a) * conj (z - c) =
          d * (z * conj z) - (d * z * conj c + d * a * conj z) + d * a * conj c := by
        rw [map_sub]
        ring
      _ = _ := by rw [Complex.mul_conj, hd, hconst, hcross]
  rw [heq]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_im]
  ring

/-- The imaginary part of the cross ratio. -/
theorem RiemannSphere.MobiusCircle.crossRatio_im {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hba : b ≠ a) (z : ℂ) :
    (crossRatio a b c z).im = orientation a b c * (1 - ‖z‖ ^ 2) / Complex.normSq (z - c) := by
  have heq :
    crossRatio a b c z =
      (coefficient a b c * (z - a) * conj (z - c)) / (Complex.normSq (z - c) : ℂ) := by
    rw [crossRatio_eq_coefficient, div_eq_mul_inv, Complex.inv_def]
    simp only [div_eq_mul_inv, Complex.ofReal_inv]
    ring
  rw [heq, Complex.div_ofReal_im, numerator_im hc (coefficient_mul_eq_conj_mul ha hb hc hba),
    Complex.normSq_eq_norm_sq]
  unfold orientation
  ring

/-- The oriented imaginary part of the cross ratio. -/
theorem RiemannSphere.MobiusCircle.orientation_mul_crossRatio_im {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (z : ℂ) :
    orientation a b c * (crossRatio a b c z).im =
      orientation a b c ^ 2 * (1 - ‖z‖ ^ 2) / Complex.normSq (z - c) := by
  rw [crossRatio_im ha hb hc hba]
  ring

/-- Positivity of the oriented imaginary part. -/
theorem RiemannSphere.MobiusCircle.orientation_mul_crossRatio_im_pos_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hzc : z ≠ c) : 0 < orientation a b c * (crossRatio a b c z).im ↔ ‖z‖ < 1 := by
  have hK := sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac)
  have hd : 0 < Complex.normSq (z - c) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzc)
  rw [orientation_mul_crossRatio_im ha hb hc hba, div_pos_iff_of_pos_right hd,
    mul_pos_iff_of_pos_left hK, sub_pos, sq_lt_one_iff₀ (norm_nonneg z)]

/-- Negativity of the oriented imaginary part. -/
theorem RiemannSphere.MobiusCircle.orientation_mul_crossRatio_im_neg_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hzc : z ≠ c) : orientation a b c * (crossRatio a b c z).im < 0 ↔ 1 < ‖z‖ := by
  have hK := sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac)
  have hd : 0 < Complex.normSq (z - c) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzc)
  have heq :
    -(orientation a b c * (crossRatio a b c z).im) =
      orientation a b c ^ 2 * (‖z‖ ^ 2 - 1) / Complex.normSq (z - c) := by
    rw [orientation_mul_crossRatio_im ha hb hc hba]
    ring
  rw [← neg_pos, heq, div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_left hK, sub_pos,
    one_lt_sq_iff₀ (norm_nonneg z)]

/-- The oriented imaginary part of the coefficient. -/
theorem RiemannSphere.MobiusCircle.orientation_mul_coefficient_im (a b c : ℂ) :
    orientation a b c * (coefficient a b c).im = -(orientation a b c ^ 2) := by
  unfold orientation
  ring

/-- The oriented coefficient's imaginary part is negative. -/
theorem RiemannSphere.MobiusCircle.orientation_mul_coefficient_im_neg {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    orientation a b c * (coefficient a b c).im < 0 := by
  rw [orientation_mul_coefficient_im]
  exact neg_neg_of_pos (sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac))

/-- The cross ratio at zero. -/
theorem RiemannSphere.MobiusCircle.crossRatio_at_zero (a b c : ℂ) : crossRatio a b c a = 0 := by
  simp [crossRatio]

/-- The cross ratio at one. -/
theorem RiemannSphere.MobiusCircle.crossRatio_at_one {a b c : ℂ} (hba : b ≠ a) (hbc : b ≠ c) :
    crossRatio a b c b = 1 := by
  unfold crossRatio
  rw [mul_comm (b - c) (b - a)]
  exact div_self (mul_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hbc))

/-! ### The finite image and the disc-to-half-plane map -/

/-- The finite image of a sphere subset. -/
def RiemannSphere.finiteImage (s : Set ℂ) : Set RiemannSphere :=
  ((↑) : ℂ → RiemannSphere) '' s

/-- A finite point lies in the finite image. -/
@[simp]
theorem RiemannSphere.coe_mem_finiteImage_iff (s : Set ℂ) (z : ℂ) :
    (z : RiemannSphere) ∈ finiteImage s ↔ z ∈ s := by simp [finiteImage]

/-- `∞` is not in the finite image. -/
@[simp]
theorem RiemannSphere.infty_not_mem_finiteImage (s : Set ℂ) :
    ((OnePoint.infty) : RiemannSphere) ∉ finiteImage s := by simp [finiteImage]

/-- The cross ratio is holomorphic on the disc. -/
theorem RiemannSphere.crossRatio_holomorphicOn_disc {a b c : ℂ} (hab : a ≠ b) (hc : ‖c‖ = 1) :
    ContDiffOn ℂ ω (MobiusCircle.crossRatio a b c) {z : ℂ | ‖z‖ < 1} := by
  intro z hz
  have hzc : z ≠ c := by
    intro he
    subst z
    exact (not_lt_of_ge hc.ge) hz
  have hden : (z - c) * (b - a) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hab.symm)
  have hn : ContDiffAt ℂ ω (fun w : ℂ => (w - a) * (b - c)) z :=
    (contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const
  have hd : ContDiffAt ℂ ω (fun w : ℂ => (w - c) * (b - a)) z :=
    (contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const
  exact (hn.div hd hden).contDiffWithinAt

/-- The closed disc with the pole removed. -/
def RiemannSphere.closedDiscWithoutPole (c : ℂ) : Set ℂ :=
  {z | ‖z‖ ≤ 1 ∧ z ≠ c}

/-- The closed oriented half-plane of the Möbius circle. -/
def RiemannSphere.closedOrientedHalfPlane (k : ℝ) : Set ℂ :=
  {w | 0 ≤ k * w.im}

/-- The finite image of a sphere set is homeomorphic to it. -/
def RiemannSphere.finiteImageHomeomorph (s : Set ℂ) : s ≃ₜ finiteImage s :=
  (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.homeomorphImage s

/-- The finite-image homeomorphism inverse computes the coercion. -/
@[simp]
theorem RiemannSphere.finiteImageHomeomorph_symm_apply_coe (s : Set ℂ) (p : finiteImage s) :
    (((finiteImageHomeomorph s).symm p : ℂ) : RiemannSphere) = (p : RiemannSphere) := by
  exact congrArg Subtype.val ((finiteImageHomeomorph s).apply_symm_apply p)

/-- Nonnegativity of the oriented imaginary part. -/
theorem RiemannSphere.orientation_mul_crossRatio_im_nonneg_iff {a b c : ℂ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) {z : ℂ}
    (hzc : z ≠ c) :
    0 ≤ MobiusCircle.orientation a b c * (MobiusCircle.crossRatio a b c z).im ↔ ‖z‖ ≤ 1 := by
  have h :=
    not_congr (MobiusCircle.orientation_mul_crossRatio_im_neg_iff ha hb hc hab.symm hbc hac hzc)
  simpa only [not_lt] using h

/-- The three-point map lands in the closed half-plane exactly on the circle side. -/
theorem RiemannSphere.threePointBiholomorph_mem_closedHalfPlane_iff {a b c : ℂ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (p : RiemannSphere) :
    threePointBiholomorph a b c hab hac hbc p ∈
        finiteImage (closedOrientedHalfPlane (MobiusCircle.orientation a b c)) ↔
      p ∈ finiteImage (closedDiscWithoutPole c) := by
  induction p using OnePoint.rec with
  | infty =>
    rw [threePointBiholomorph_infty]
    simp only [coe_mem_finiteImage_iff, infty_not_mem_finiteImage, iff_false,
      closedOrientedHalfPlane, Set.mem_ofPred_eq]
    exact not_le_of_gt (MobiusCircle.orientation_mul_coefficient_im_neg ha hb hc hab.symm hbc hac)
  | coe z =>
    by_cases hzc : z = c
    · subst z
      simp [closedDiscWithoutPole]
    · rw [threePointBiholomorph_coe a b c hab hac hbc z hzc]
      simp only [coe_mem_finiteImage_iff, closedOrientedHalfPlane, closedDiscWithoutPole,
        Set.mem_ofPred_eq, and_iff_left hzc]
      exact orientation_mul_crossRatio_im_nonneg_iff hab hac hbc ha hb hc hzc

/-- The closed disc is sphere-homeomorphic to the closed half-plane. -/
def RiemannSphere.closedDiscHalfPlaneSphereHomeomorph {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    finiteImage (closedDiscWithoutPole c) ≃ₜ
      finiteImage (closedOrientedHalfPlane (MobiusCircle.orientation a b c)) :=
  (threePointBiholomorph a b c hab hac hbc).toHomeomorph.subtype
    (fun p => (threePointBiholomorph_mem_closedHalfPlane_iff hab hac hbc ha hb hc p).symm)

/-- The closed disc is homeomorphic to the closed half-plane. -/
def RiemannSphere.closedDiscHalfPlaneHomeomorph {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    closedDiscWithoutPole c ≃ₜ closedOrientedHalfPlane (MobiusCircle.orientation a b c) :=
  ((finiteImageHomeomorph (closedDiscWithoutPole c)).trans
        (closedDiscHalfPlaneSphereHomeomorph hab hac hbc ha hb hc)).trans
    (finiteImageHomeomorph (closedOrientedHalfPlane (MobiusCircle.orientation a b c))).symm

/-- The disc–half-plane homeomorphism computes through the sphere map. -/
theorem RiemannSphere.closedDiscHalfPlaneHomeomorph_sphere {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (z : closedDiscWithoutPole c) :
    (((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z :
            closedOrientedHalfPlane (MobiusCircle.orientation a b c)) :
          ℂ) :
        RiemannSphere) =
      threePointBiholomorph a b c hab hac hbc ((z : ℂ) : RiemannSphere) := by
  exact
    finiteImageHomeomorph_symm_apply_coe
      (closedOrientedHalfPlane (MobiusCircle.orientation a b c))
      (closedDiscHalfPlaneSphereHomeomorph hab hac hbc ha hb hc
        (finiteImageHomeomorph (closedDiscWithoutPole c) z))

/-- The disc–half-plane homeomorphism computes the cross ratio. -/
@[simp]
theorem RiemannSphere.closedDiscHalfPlaneHomeomorph_apply {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (z : closedDiscWithoutPole c) :
    (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ) =
      MobiusCircle.crossRatio a b c z := by
  apply OnePoint.coe_injective
  rw [closedDiscHalfPlaneHomeomorph_sphere,
    threePointBiholomorph_coe a b c hab hac hbc z z.property.2]
  rfl

/-- The strict half-plane corresponds to the open disc. -/
theorem RiemannSphere.closedDiscHalfPlaneHomeomorph_strict_iff {a b c : ℂ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (z : closedDiscWithoutPole c) :
    0 <
        MobiusCircle.orientation a b c *
          (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ).im ↔
      ‖(z : ℂ)‖ < 1 := by
  rw [closedDiscHalfPlaneHomeomorph_apply]
  exact MobiusCircle.orientation_mul_crossRatio_im_pos_iff ha hb hc hab.symm hbc hac z.property.2
