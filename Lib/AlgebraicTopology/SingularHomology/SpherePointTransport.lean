/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction

/-!
# Transporting points of a unit sphere by positive-determinant isometries

The special orthogonal group acts transitively on the unit sphere of a finite-dimensional real
inner product space: any two points are exchanged by a linear isometry of determinant one
(`SpherePoint.exists_positive_transport`, a chosen such isometry being
`SpherePoint.positiveTransport`).  Such an isometry restricts to a diffeomorphism of the sphere
(`SpherePoint.sphereDiffeomorph`) which, having positive determinant, acts as the identity on
singular homology (`SpherePoint.positiveTransport_homology`).

## Main definitions and results

* `SpherePoint.exists_positive_transport`: transitivity by determinant-one isometries.
* `SpherePoint.positiveTransport`, `SpherePoint.positiveTransport_apply`,
  `SpherePoint.positiveTransport_det`: the chosen transport and its two properties.
* `SpherePoint.sphereHomeomorph`, `SpherePoint.sphereDiffeomorph`: the restriction of a linear
  isometry to the unit sphere.
* `SpherePoint.positiveTransport_homology`: the transport is the identity on singular homology.

## References

* [hatcher02] A. Hatcher, *Algebraic Topology*, §2.2 (degree and reflections).

## Tags

sphere, orthogonal group, transitive action, reflection, singular homology
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The reflection in the hyperplane orthogonal to a nonzero vector has determinant `-1`. -/
theorem SpherePoint.hyperplaneReflection_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (u : V) (hu : u ≠ 0) :
    ((ℝ ∙ u)ᗮ.reflection).toLinearMap.det = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hu,
    pow_one]

/-- Two distinct points of the unit sphere are carried onto one another by a linear isometry of
determinant `1`: compose the reflection exchanging them with the reflection in a hyperplane
containing the target. -/
theorem SpherePoint.positive_transport_of_normal {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (v w : Metric.sphere (0 : V) 1) (u : V)
    (hu : u ≠ 0) (huw : Inner.inner ℝ u w.val = 0) (hvw : v ≠ w) :
    ∃ R : V ≃ₗᵢ[ℝ] V, R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  have hvw' : (v : V) - (w : V) ≠ 0 := by
    intro h
    exact hvw (Subtype.ext (sub_eq_zero.mp h))
  let R₁ := (ℝ ∙ ((v : V) - (w : V)))ᗮ.reflection
  let R₂ := (ℝ ∙ u)ᗮ.reflection
  have h₁ : R₁ v.val = w.val :=
    Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp v.property).trans
        (mem_sphere_zero_iff_norm.mp w.property).symm)
  have h₂ : R₂ w.val = w.val :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huw)
  refine ⟨R₁.trans R₂, ?_, ?_⟩
  · change R₂ (R₁ v.val) = w.val
    rw [h₁, h₂]
  · change (R₂.toLinearMap.comp R₁.toLinearMap).det = 1
    rw [LinearMap.det_comp, hyperplaneReflection_det u hu,
      hyperplaneReflection_det ((v : V) - (w : V)) hvw']
    norm_num

/-- The special orthogonal group acts transitively on the unit sphere of `EuclideanSpace ℝ
(Fin (n + 2))`: any two points are exchanged by a linear isometry of determinant `1`. -/
theorem SpherePoint.exists_positive_transport (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    ∃ R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)),
      R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  by_cases hvw : v = w
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_, ?_⟩
    · exact congrArg Subtype.val hvw
    · exact LinearMap.det_id
  · let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) := ⟨by simp⟩
    let b :=
      OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1) (ne_zero_of_mem_unit_sphere w)
    let u : EuclideanSpace ℝ (Fin (n + 2)) :=
      (b (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)))
    have hun : ‖u‖ = 1 := b.norm_eq_one 0
    have hu : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hun
      exact zero_ne_one hun
    have huw : Inner.inner ℝ u w.val = 0 := by
      have h := (b (0 : Fin (n + 1))).property
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp h
    exact positive_transport_of_normal v w u hu huw hvw

/-- A chosen linear isometry of determinant `1` carrying `v` to `w` on the unit sphere. -/
def SpherePoint.positiveTransport (n : ℕ) (v w : SphereHomology.UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Classical.choose (exists_positive_transport n v w)

/-- `SpherePoint.positiveTransport` carries `v` to `w`. -/
theorem SpherePoint.positiveTransport_apply (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : positiveTransport n v w v.val = w.val :=
  (Classical.choose_spec (exists_positive_transport n v w)).1

/-- `SpherePoint.positiveTransport` has determinant `1`. -/
theorem SpherePoint.positiveTransport_det (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : (positiveTransport n v w).toLinearMap.det = 1 :=
  (Classical.choose_spec (exists_positive_transport n v w)).2

/-- A linear isometry of an inner product space restricts to a homeomorphism of its unit
sphere. -/
def SpherePoint.sphereHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : V ≃ₗᵢ[ℝ] V) : Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 :=
  R.toContinuousLinearEquiv.toHomeomorph.subtype
    (fun x => by
      simp only [mem_sphere_zero_iff_norm]
      change ‖x‖ = 1 ↔ ‖R x‖ = 1
      rw [R.norm_map])

/-- On the unit sphere, the restriction of a linear isometry agrees with the normalized linear
sphere map `LinearSphereAction.sphereMap`. -/
theorem SpherePoint.sphereHomeomorph_eq_normalized {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : V ≃ₗᵢ[ℝ] V) :
    (sphereHomeomorph R).toHomotopyEquiv.toFun =
      LinearSphereAction.sphereMap R.toContinuousLinearEquiv.toContinuousLinearMap
        R.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change R x.val = ‖R x.val‖⁻¹ • R x.val
  rw [R.norm_map, mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

/-- The restriction of a linear isometry to the unit sphere is smooth for the sphere's standard
manifold structure. -/
theorem SpherePoint.contMDiff_sphereHomeomorph {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereHomeomorph R) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞ (fun x : Metric.sphere (0 : V) 1 => R x.val) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
      (contMDiff_coe_sphere (m := ∞))
  exact h.codRestrict_sphere (n := n) (fun x => (sphereHomeomorph R x).property)

/-- A linear isometry of an inner product space restricts to a diffeomorphism of its unit
sphere. -/
def SpherePoint.sphereDiffeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : V) 1) (Metric.sphere (0 : V) 1) ∞
    where
  toEquiv := (sphereHomeomorph R).toEquiv
  contMDiff_toFun := contMDiff_sphereHomeomorph R
  contMDiff_invFun := contMDiff_sphereHomeomorph R.symm

/-- A linear isometry of positive determinant acts as the identity on the singular homology of
the unit sphere. -/
theorem SpherePoint.sphereHomeomorph_homology_of_det_pos (n : ℕ)
    (R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (hR : 0 < R.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereHomeomorph R).toHomotopyEquiv.toFun k a =
      a := by
  rw [sphereHomeomorph_eq_normalized]
  exact LinearSphereAction.homology_of_det_pos n R.toContinuousLinearEquiv hR k a

/-- The sphere homeomorphism of `SpherePoint.positiveTransport n v w` sends `v` to `w`. -/
theorem SpherePoint.positiveTransport_moves (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    sphereHomeomorph (positiveTransport n v w) v = w :=
  Subtype.ext (positiveTransport_apply n v w)

/-- Transporting a sphere point by `SpherePoint.positiveTransport` acts as the identity on
singular homology in every degree. -/
theorem SpherePoint.positiveTransport_homology (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap
        (sphereHomeomorph (positiveTransport n v w)).toHomotopyEquiv.toFun k a =
      a := by
  apply sphereHomeomorph_homology_of_det_pos n _ _ k a
  rw [positiveTransport_det]
  norm_num
