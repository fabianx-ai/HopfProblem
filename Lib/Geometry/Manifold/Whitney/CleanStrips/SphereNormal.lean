/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.CircleGluing

/-!
# Normal coordinates along the unit sphere

For the unit sphere `Sⁿ` of an inner product space `V` of dimension `n + 1`:

* `SphereBoundary.definingFunction` is `x ↦ ‖x‖² - 1`, whose zero set is the sphere and whose
  derivative `2 ⟪x, ·⟫` has as kernel the tangent space of the sphere; a smooth map restricting to
  an immersion of the sphere is injective on the common kernel
  (`SphereBoundary.common_kernel_of_immersive_sphere_extension`).
* `SphereNormalCoordinates.normalFrame x A` is the linear isomorphism `ℝ × N → V` adapted to the
  orthogonal splitting `V = ℝ x ⊕ TₓSⁿ`, the tangent factor identified with `N` through an
  invertible `A`; `SphereNormalCoordinates.normalJacobian` is its determinant relative to a
  reference isomorphism. Its sign is the local intersection sign of the sphere with a transverse
  submanifold (Milnor, *Lectures on the h-cobordism theorem*, §6); it is nonzero, and invariant
  under a change of model of the normal factor.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section


/-- The defining function `x ↦ ‖x‖² - 1` of the unit sphere. -/
def SphereBoundary.definingFunction {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  ‖x‖ ^ 2 - 1

/-- The defining function of the unit sphere is smooth on an inner product space. -/
theorem SphereBoundary.contDiff_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ContDiff ℝ ∞ (definingFunction (E := E)) :=
  (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const

/-- The defining function vanishes exactly on the unit sphere. -/
theorem SphereBoundary.definingFunction_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    (x : E) : definingFunction x = 0 ↔ x ∈ Metric.sphere (0 : E) 1 := by
  simp only [definingFunction, Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]
    norm_num

/-- The derivative of the defining function at `x` is `2 ⟪x, ·⟫`. -/
theorem SphereBoundary.fderiv_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) : fderiv ℝ (definingFunction (E := E)) x = 2 • innerSL ℝ x :=
  ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).fderiv

/-- A vector is annihilated by the derivative of the defining function at `x` exactly when it is
orthogonal to `x`; so the kernel of that derivative is the tangent space of the sphere.
-/
theorem SphereBoundary.fderiv_definingFunction_eq_zero_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x v : E) :
    fderiv ℝ (definingFunction (E := E)) x v = 0 ↔ Inner.inner ℝ x v = 0 := by
  rw [fderiv_definingFunction]
  rw [two_smul, add_apply]
  change Inner.inner ℝ x v + Inner.inner ℝ x v = 0 ↔ Inner.inner ℝ x v = 0
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

/-- If a smooth map on `E` restricts on the unit sphere to an immersion, then at every point of the
sphere the only vector killed both by the derivative of the map and by the derivative of the
defining function is zero; that is, the map is transverse to the sphere in the sense that its
kernel meets the tangent space of the sphere trivially.
-/
theorem SphereBoundary.common_kernel_of_immersive_sphere_extension {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x)) :
    ∀ y,
      definingFunction y = 0 →
        ∀ v : E,
          mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ (definingFunction (E := E)) y v = 0 → v = 0 := by
  intro y hy v hfv hρv
  let x : Metric.sphere (0 : E) 1 := ⟨y, (definingFunction_eq_zero_iff y).mp hy⟩
  have hinner : Inner.inner ℝ y v = 0 := (fderiv_definingFunction_eq_zero_iff y v).mp hρv
  have hrange : v ∈ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : E) 1 → E) x).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hinner
  obtain ⟨w, hw⟩ := hrange
  change (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w = v at hw
  have hextfun : (f ∘ (Subtype.val : Metric.sphere (0 : E) 1 → E)) = γ := funext hext
  have hchain :
    mfderiv (𝓡 n) J γ x =
      (mfderiv 𝓘(ℝ, E) J f y).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) := by
    rw [← hextfun,
      mfderiv_comp x (hf.mdifferentiableAt (by simp))
        ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))]
  have hγzero : mfderiv (𝓡 n) J γ x w = 0 := by
    rw [hchain]
    change
      (mfderiv 𝓘(ℝ, E) J f y)
          ((mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w) =
        0
    rw [hw]
    exact hfv
  have hwzero : w = 0 := (hγ x) (by simpa only [map_zero] using hγzero)
  rw [hwzero, map_zero] at hw
  exact hw.symm

/-- The derivative of the inclusion of the unit sphere into the ambient space, read in the standard
chart of `Sⁿ`; it identifies `ℝⁿ` with the tangent space of the sphere at `x`.
-/
def SphereNormalCoordinates.inclusionDerivative {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : EuclideanSpace ℝ (Fin n) →L[ℝ] V :=
  mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x

/-- Tangent vectors of the sphere at `x` are orthogonal to `x`. -/
theorem SphereNormalCoordinates.inner_inclusionDerivative_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) (u : EuclideanSpace ℝ (Fin n)) :
    Inner.inner ℝ (x : V) (inclusionDerivative x u) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) x]
  exact ⟨u, rfl⟩

/-- A point of the unit sphere has inner square one. -/
theorem SphereNormalCoordinates.inner_self_eq_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x : Metric.sphere (0 : V) 1) : Inner.inner ℝ (x : V) x = 1 := by
  have hx : ‖(x : V)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [real_inner_self_eq_norm_sq, hx, one_pow]

/-- The frame of the ambient space at a point `x` of the unit sphere adapted to the splitting into
the radial line `ℝ x` and the tangent space: it sends `(s, w)` to `s • x` plus the tangent
vector corresponding to `w` under `A`.
-/
def SphereNormalCoordinates.normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp A.inverse)

/-- The value of the adapted frame: `(s, w) ↦ s • x + inclusionDerivative x (A⁻¹ w)`. -/
theorem SphereNormalCoordinates.normalFrame_apply {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    normalFrame x A z = z.1 • (x : V) + inclusionDerivative x (A.inverse z.2) :=
  rfl

/-- The radial component of the adapted frame is its first argument. -/
theorem SphereNormalCoordinates.inner_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    Inner.inner ℝ (x : V) (normalFrame x A z) = z.1 := by
  rw [normalFrame_apply, inner_add_right, inner_smul_right, inner_self_eq_one,
    inner_inclusionDerivative_zero, mul_one, add_zero]

/-- For an invertible `A` the adapted frame is a linear isomorphism, since the ambient space is the
orthogonal sum of the radial line and the tangent space.
-/
theorem SphereNormalCoordinates.bijective_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    Function.Bijective (normalFrame x A) := by
  constructor
  · intro z w hzw
    have hfst : z.1 = w.1 := by
      simpa only [inner_normalFrame] using congrArg (fun v : V => Inner.inner ℝ (x : V) v) hzw
    have ht : inclusionDerivative x (A.inverse z.2) = inclusionDerivative x (A.inverse w.2) := by
      rw [normalFrame_apply, normalFrame_apply, hfst] at hzw
      exact add_left_cancel hzw
    have hJ : Function.Injective (inclusionDerivative (n := n) x) :=
      injective_mvfderiv_subtypeVal_sphere x
    exact Prod.ext hfst (hA.inverse.injective (hJ ht))
  · intro v
    have ht : v - Inner.inner ℝ (x : V) v • (x : V) ∈ (inclusionDerivative (n := n) x).range := by
      change
        v - Inner.inner ℝ (x : V) v • (x : V) ∈
          (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x).range
      rw [range_mvfderiv_subtypeVal]
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, inner_self_eq_one, mul_one, sub_self]
    obtain ⟨u, hu⟩ := ht
    change inclusionDerivative x u = v - Inner.inner ℝ (x : V) v • (x : V) at hu
    refine ⟨(Inner.inner ℝ (x : V) v, A u), ?_⟩
    rw [normalFrame_apply, hA.inverse_apply_self, hu]
    abel

/-- The determinant of the adapted frame relative to a reference isomorphism `j`; its sign is the
local intersection sign of the sphere with a transverse submanifold.
-/
def SphereNormalCoordinates.normalJacobian {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : ℝ :=
  ((normalFrame x A).comp j.symm.toContinuousLinearMap).det

/-- The normal Jacobian is nonzero when `A` is invertible, since the adapted frame is then an
isomorphism.
-/
theorem SphereNormalCoordinates.normalJacobian_ne_zero {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian j x A ≠ 0 := by
  apply (RegularValues.bijective_iff_det_ne_zero _).mp
  exact (bijective_normalFrame x A hA).comp j.symm.bijective

/-- The normal Jacobian is unchanged when the model of the normal factor is replaced by an
isomorphic one, the reference isomorphism being transported along.
-/
theorem SphereNormalCoordinates.normalJacobian_change_normal_model {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] {N' : Type*} [NormedAddCommGroup N']
    [NormedSpace ℝ N'] (r : (ℝ × N) ≃L[ℝ] V) (j : N' ≃L[ℝ] N) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r)
        x (j.symm.toContinuousLinearMap.comp A) =
      normalJacobian r x A := by
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] N' := j.symm.toContinuousLinearMap.comp A
  have hj : j.symm.toContinuousLinearMap.IsInvertible := ⟨j.symm, rfl⟩
  have hB : B.IsInvertible := hj.comp hA
  have hinv (z : N) : B.inverse (j.symm z) = A.inverse z := by
    apply hB.injective
    rw [hB.self_apply_inverse]
    change j.symm z = j.symm (A (A.inverse z))
    rw [hA.self_apply_inverse]
  unfold normalJacobian
  apply congrArg ContinuousLinearMap.det
  apply ContinuousLinearMap.ext
  intro v
  change
    (r.symm v).1 • (x : V) + inclusionDerivative x (B.inverse (j.symm (r.symm v).2)) =
      (r.symm v).1 • (x : V) + inclusionDerivative x (A.inverse (r.symm v).2)
  rw [hinv]


end
