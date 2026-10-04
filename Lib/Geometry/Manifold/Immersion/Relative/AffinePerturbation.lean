/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension

/-!
# Affine perturbations of maps of the plane

For a smooth map `f : Plane → F` of the plane `PlaneImmersion.Plane := ℝ × ℝ` into a normed space
`F`, `PlaneImmersion.perturb f A = f + PlaneImmersion.linearMap A` adds the linear map whose two
columns are `A : F × F`. The parameters `A` for which the perturbed map identifies two distinct
points are the images of the open sets `PlaneImmersion.firstCollisionDomain`,
`PlaneImmersion.secondCollisionDomain` of `Plane × (Plane × F)` under the smooth maps
`PlaneImmersion.firstCollision`, `PlaneImmersion.secondCollision`, hence a set of Hausdorff dimension at
most `4 + dim F` (`PlaneImmersion.dimH_collision_parameters_le`); those for which the perturbed
derivative has a kernel vector are the ranges of `PlaneImmersion.badFirst`, `PlaneImmersion.badSecond`
on `Plane × (ℝ × F)`, of dimension at most `3 + dim F` (`PlaneImmersion.dimH_bad_parameters_le`).
When `dim F ≥ 5` both bounds lie below `dim (F × F) = 2 dim F`, so the good parameters are dense
(`PlaneImmersion.dense_injective_immersive_parameters`) and arbitrarily small affine perturbations
are injective immersions (`PlaneImmersion.exists_small_affine_injective_immersion`): the weak
Whitney embedding theorem for the plane in affine form.

The cutoff-weighted displacement `PlaneImmersion.displacement β A x = β x • linearMap A x` and its
uniform smallness for small `A` (`PlaneImmersion.exists_radius_displacement_lt`) are what the
chart-by-chart patching of `Lib.Geometry.Manifold.Immersion.Relative.Plane` uses.

## References

* Whitney, *Differentiable manifolds*, Thm 5.
* Hirsch, *Differential Topology*, Ch. 3 §2 (general position by a Sard-type count).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- The two-dimensional source of the plane-immersion chain, `ℝ × ℝ`. -/
abbrev PlaneImmersion.Plane :=
  ℝ × ℝ

/-- The linear map `Plane →L[ℝ] F` with the two given columns. -/
def PlaneImmersion.linearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F × F) : Plane →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A.1 + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight A.2

/-- `linearMap A` sends `v` to `v.1 • A.1 + v.2 • A.2`. -/
theorem PlaneImmersion.linearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F × F) (v : Plane) : linearMap A v = v.1 • A.1 + v.2 • A.2 :=
  rfl

/-- Perturbation of a map on the plane by an affine term with matrix `A`. -/
def PlaneImmersion.perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (A : F × F) (x : Plane) : F :=
  f x + linearMap A x

/-- The perturbation is smooth jointly in the parameter and the point. -/
theorem PlaneImmersion.contDiff_perturb_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => perturb f q.1 q.2) :=
  (hf.comp contDiff_snd).add
    (((contDiff_fst.comp contDiff_snd).smul (contDiff_fst.comp contDiff_fst)).add
      ((contDiff_snd.comp contDiff_snd).smul (contDiff_snd.comp contDiff_fst)))

/-- The derivative of the perturbed map is the derivative of the original plus the constant linear
map `linearMap A`. -/
theorem PlaneImmersion.fderiv_perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (A : F × F) (x : Plane) :
    fderiv ℝ (perturb f A) x = fderiv ℝ f x + linearMap A :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add (linearMap A).hasFDerivAt).fderiv

/-- The parameters of pairs of distinct points whose first coordinates differ; the domain on which
the first collision map is defined. -/
def PlaneImmersion.firstCollisionDomain {F : Type*} : Set (Plane × (Plane × F)) :=
  {q | q.1.1 - q.2.1.1 ≠ 0}

/-- The parameters of pairs of distinct points whose second coordinates differ. -/
def PlaneImmersion.secondCollisionDomain {F : Type*} : Set (Plane × (Plane × F)) :=
  {q | q.1.2 - q.2.1.2 ≠ 0}

/-- The perturbation matrix that would identify the two points of a pair, solved through its first
coordinate. -/
def PlaneImmersion.firstCollision {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  ((q.1.1 - q.2.1.1)⁻¹ • (f q.2.1 - f q.1 - (q.1.2 - q.2.1.2) • q.2.2), q.2.2)

/-- The perturbation matrix that would identify the two points of a pair, solved through its second
coordinate. -/
def PlaneImmersion.secondCollision {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  (q.2.2, (q.1.2 - q.2.1.2)⁻¹ • (f q.2.1 - f q.1 - (q.1.1 - q.2.1.1) • q.2.2))

/-- The first collision domain is open. -/
theorem PlaneImmersion.isOpen_firstCollisionDomain {F : Type*} [NormedAddCommGroup F] :
    IsOpen (firstCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.fst.sub continuous_snd.fst.fst)

/-- The second collision domain is open. -/
theorem PlaneImmersion.isOpen_secondCollisionDomain {F : Type*} [NormedAddCommGroup F] :
    IsOpen (secondCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.snd.sub continuous_snd.fst.snd)

/-- The first collision map is smooth on its domain. -/
theorem PlaneImmersion.contDiffOn_firstCollision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (firstCollision f) firstCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact
    ((h₁.contDiffOn.inv (fun _ h => h)).smul
          (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
              (h₂.smul contDiff_snd.snd)).contDiffOn).prodMk
      contDiff_snd.snd.contDiffOn

/-- The second collision map is smooth on its domain. -/
theorem PlaneImmersion.contDiffOn_secondCollision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (secondCollision f) secondCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact
    contDiff_snd.snd.contDiffOn.prodMk
      ((h₂.contDiffOn.inv (fun _ h => h)).smul
        (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
            (h₁.smul contDiff_snd.snd)).contDiffOn)

/-- If the perturbed map identifies two distinct points, the parameter lies in the image of one of
the two collision maps. -/
theorem PlaneImmersion.mem_collision_of_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) (A : F × F) {x y : Plane} (hxy : x ≠ y)
    (heq : perturb f A x = perturb f A y) :
    A ∈ firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain := by
  have hlinear : linearMap A (x - y) = f y - f x := by
    rw [map_sub]
    change f x + linearMap A x = f y + linearMap A y at heq
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using heq)
  change (x.1 - y.1) • A.1 + (x.2 - y.2) • A.2 = f y - f x at hlinear
  by_cases hfirst : x.1 - y.1 = 0
  · have hsecond : x.2 - y.2 ≠ 0 := by
      intro h
      exact hxy (Prod.ext (sub_eq_zero.mp hfirst) (sub_eq_zero.mp h))
    apply Or.inr
    refine ⟨(x, (y, A.1)), hsecond, Prod.ext rfl ?_⟩
    change (x.2 - y.2)⁻¹ • (f y - f x - (x.1 - y.1) • A.1) = A.2
    rw [← eq_sub_of_add_eq' hlinear, inv_smul_smul₀ hsecond]
  · apply Or.inl
    refine ⟨(x, (y, A.2)), hfirst, Prod.ext ?_ rfl⟩
    change (x.1 - y.1)⁻¹ • (f y - f x - (x.2 - y.2) • A.2) = A.1
    rw [← eq_sub_of_add_eq hlinear, inv_smul_smul₀ hfirst]

/-- Conversely, a parameter outside both collision images gives an injective perturbation. -/
theorem PlaneImmersion.injective_perturb_of_not_collision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) {A : F × F}
    (hA :
      A ∉ firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain) :
    Function.Injective (perturb f A) := by
  intro x y heq
  by_contra hxy
  exact hA (mem_collision_of_eq f A hxy heq)

/-- The perturbation matrix that would put a vector with nonzero first coordinate in the kernel of
the perturbed derivative. -/
def PlaneImmersion.badFirst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (-fderiv ℝ f q.1 (1, q.2.1) - q.2.1 • q.2.2, q.2.2)

/-- The perturbation matrix that would put a vector with nonzero second coordinate in the kernel of
the perturbed derivative. -/
def PlaneImmersion.badSecond {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (q.2.2, -fderiv ℝ f q.1 (q.2.1, 1) - q.2.1 • q.2.2)

/-- The first bad-parameter map is smooth. -/
theorem PlaneImmersion.contDiff_badFirst {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (badFirst f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (1, q.2.1)) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd))
  exact
    (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd))).prodMk
      (contDiff_snd.comp contDiff_snd)

/-- The second bad-parameter map is smooth. -/
theorem PlaneImmersion.contDiff_badSecond {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (badSecond f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (q.2.1, 1)) :=
    (hd.comp contDiff_fst).clm_apply ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const)
  exact
    (contDiff_snd.comp contDiff_snd).prodMk
      (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd)))

/-- If the perturbed derivative has a nonzero kernel vector, the parameter is in the range of one of
the two bad-parameter maps. -/
theorem PlaneImmersion.mem_bad_of_nonzero_kernel {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) (A : F × F) (x v : Plane) (hv : v ≠ 0)
    (hker : (fderiv ℝ f x + linearMap A) v = 0) :
    A ∈ Set.range (badFirst f) ∪ Set.range (badSecond f) := by
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hfirst h)
    let r := v.1 / v.2
    have hvec : (r, (1 : ℝ)) = v.2⁻¹ • v := by
      apply Prod.ext
      · change v.1 / v.2 = v.2⁻¹ * v.1
        rw [div_eq_mul_inv, mul_comm]
      · change (1 : ℝ) = v.2⁻¹ * v.2
        rw [inv_mul_cancel₀ hsecond]
    have hz : (fderiv ℝ f x + linearMap A) (r, 1) = 0 := by rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (r, 1) + (r • A.1 + (1 : ℝ) • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : A.2 = -(fderiv ℝ f x (r, 1) + r • A.1) := eq_neg_of_add_eq_zero_right hz
    apply Or.inr
    refine ⟨(x, (r, A.1)), Prod.ext rfl ?_⟩
    change -fderiv ℝ f x (r, 1) - r • A.1 = A.2
    simpa only [neg_add, sub_eq_add_neg] using hsolve.symm
  · let r := v.2 / v.1
    have hvec : ((1 : ℝ), r) = v.1⁻¹ • v := by
      apply Prod.ext
      · change (1 : ℝ) = v.1⁻¹ * v.1
        rw [inv_mul_cancel₀ hfirst]
      · change v.2 / v.1 = v.1⁻¹ * v.2
        rw [div_eq_mul_inv, mul_comm]
    have hz : (fderiv ℝ f x + linearMap A) (1, r) = 0 := by rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (1, r) + ((1 : ℝ) • A.1 + r • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : fderiv ℝ f x (1, r) + A.1 = -(r • A.2) := eq_neg_of_add_eq_zero_left hz
    apply Or.inl
    refine ⟨(x, (r, A.2)), Prod.ext ?_ rfl⟩
    change -fderiv ℝ f x (1, r) - r • A.2 = A.1
    rw [sub_eq_add_neg, ← hsolve, neg_add_cancel_left]

/-- Conversely, a parameter outside both bad ranges makes the perturbed derivative injective at
every point. -/
theorem PlaneImmersion.injective_add_linearMap_of_not_bad {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) {A : F × F}
    (hA : A ∉ Set.range (badFirst f) ∪ Set.range (badSecond f)) (x : Plane) :
    Function.Injective (fderiv ℝ f x + linearMap A) := by
  intro v w hvw
  have hz : (fderiv ℝ f x + linearMap A) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have heq : v - w = 0 := by
    by_contra hne
    exact hA (mem_bad_of_nonzero_kernel f A x (v - w) hne hz)
  exact sub_eq_zero.mp heq

/-- The set of bad parameters has Hausdorff dimension at most `dim (Plane × (ℝ × F)) = 3 + dim F`,
being the image of that space under a smooth map. -/
theorem PlaneImmersion.dimH_bad_parameters_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (Set.range (badFirst f) ∪ Set.range (badSecond f)) ≤
      (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
  have hfirst : dimH (Set.range (badFirst f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← Set.image_univ]
    exact
      GeneralPosition.dimH_image_manifold_le isOpen_univ
        (contDiff_badFirst hf).contMDiff.contMDiffOn
  have hsecond : dimH (Set.range (badSecond f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← Set.image_univ]
    exact
      GeneralPosition.dimH_image_manifold_le isOpen_univ
        (contDiff_badSecond hf).contMDiff.contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

/-- The set of collision parameters has Hausdorff dimension at most `dim (Plane × (Plane × F)) = 4 +
dim F`. -/
theorem PlaneImmersion.dimH_collision_parameters_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain) ≤
      (Module.finrank ℝ (Plane × (Plane × F)) : ℝ≥0∞) := by
  have hfirst :=
    GeneralPosition.dimH_image_manifold_le (isOpen_firstCollisionDomain (F := F))
      (contDiffOn_firstCollision hf).contMDiffOn
  have hsecond :=
    GeneralPosition.dimH_image_manifold_le (isOpen_secondCollisionDomain (F := F))
      (contDiffOn_secondCollision hf).contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

/-- Sard/Whitney counting argument: when `dim F ≥ 5`, the bad and collision parameters together have
Hausdorff dimension less than `2 dim F`, so their complement in `F × F` is dense (Whitney,
*Differentiable manifolds*, Thm 5; Hirsch, *Differential Topology*, Ch. 3). -/
theorem PlaneImmersion.dense_injective_immersive_parameters {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (hdim : 5 ≤ Module.finrank ℝ F) :
    Dense
      ((Set.range (badFirst f) ∪ Set.range (badSecond f)) ∪
          (firstCollision f '' firstCollisionDomain ∪
            secondCollision f '' secondCollisionDomain))ᶜ := by
  have hd₁ : Module.finrank ℝ (Plane × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × (ℝ × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hd₂ : Module.finrank ℝ (Plane × (Plane × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × ((ℝ × ℝ) × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  apply dense_compl_of_dimH_lt_finrank
  rw [dimH_union]
  exact
    max_lt ((dimH_bad_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₁))
      ((dimH_collision_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₂))

/-- Weak Whitney embedding theorem for the plane, affine form: when `dim F ≥ 5`, arbitrarily small
affine perturbations of a smooth map `Plane → F` are injective immersions. -/
theorem PlaneImmersion.exists_small_affine_injective_immersion {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (hdim : 5 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F,
      ‖A‖ < ε ∧
        ContDiff ℝ ∞ (perturb f A) ∧
          Function.Injective (perturb f A) ∧ ∀ x, Function.Injective (fderiv ℝ (perturb f A) x) :=
  by
  obtain ⟨A, hA, hnorm⟩ := (dense_injective_immersive_parameters hf hdim).exists_dist_lt 0 hε
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa only [dist_zero_left] using hnorm
  · exact (contDiff_perturb_family hf).comp (contDiff_const.prodMk contDiff_id)
  · exact injective_perturb_of_not_collision f (fun h => hA (Or.inr h))
  · intro x
    rw [fderiv_perturb hf]
    exact injective_add_linearMap_of_not_bad f (fun h => hA (Or.inl h)) x

/-- The displacement `β x • (linearMap A x)` by which a cutoff-weighted affine perturbation moves
the point `x`. -/
def PlaneImmersion.displacement {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : Plane → ℝ) (A : F × F) (x : Plane) : F :=
  β x • linearMap A x

/-- The displacement is smooth jointly in the parameter and the point. -/
theorem PlaneImmersion.contDiff_displacement_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => displacement β q.1 q.2) :=
  (hβ.comp contDiff_snd).smul
    ((contDiff_snd.fst.smul contDiff_fst.fst).add (contDiff_snd.snd.smul contDiff_fst.snd))

/-- The zero parameter displaces nothing. -/
theorem PlaneImmersion.displacement_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (β : Plane → ℝ) (x : Plane) : displacement β (0 : F × F) x = 0 := by
  simp only [displacement, linearMap_apply, Prod.fst_zero, Prod.snd_zero, smul_zero, add_zero]

/-- Where the cutoff vanishes, the displacement vanishes. -/
theorem PlaneImmersion.displacement_of_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (A : F × F) {x : Plane} (hx : β x = 0) :
    displacement β A x = 0 := by simp only [displacement, hx, zero_smul]

/-- For a compactly supported cutoff, small parameters give uniformly small displacements. -/
theorem PlaneImmersion.eventually_displacement_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ A : F × F in 𝓝 0, ∀ x, ‖displacement β A x‖ < ε := by
  have hsupport : ∀ᶠ A : F × F in 𝓝 0, ∀ x ∈ tsupport β, ‖displacement β A x‖ < ε := by
    apply hcompact.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have hc :=
      (contDiff_displacement_family (F := F) hβ).continuous.norm.continuousAt (x :=
        ((0 : F × F), x))
    have hval : ‖displacement β (0 : F × F) x‖ < ε := by
      simpa only [displacement_zero, norm_zero] using hε
    exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hval)
  filter_upwards [hsupport] with A hA x
  by_cases hx : x ∈ tsupport β
  · exact hA x hx
  · have hzero : β x = 0 := by
      by_contra hne
      exact hx (subset_tsupport β hne)
    simpa only [displacement_of_zero A hzero, norm_zero] using hε

/-- Quantitative form of the previous lemma: there is a radius below which all parameters give
displacements smaller than `ε`. -/
theorem PlaneImmersion.exists_radius_displacement_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > (0 : ℝ), ∀ A : F × F, ‖A‖ < δ → ∀ x, ‖displacement β A x‖ < ε := by
  have hn : {A : F × F | ∀ x, ‖displacement β A x‖ < ε} ∈ 𝓝 0 :=
    eventually_displacement_lt hβ hcompact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, fun A hA => hball (by simpa only [Metric.mem_ball, dist_zero_right] using hA)⟩
