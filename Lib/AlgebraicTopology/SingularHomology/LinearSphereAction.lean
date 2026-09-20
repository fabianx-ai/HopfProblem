/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.Geometry.Manifold.Immersion.Relative

/-!
# Linear actions on sphere homology

`LinearSphereAction.homology_eq_sign_smul` states that the normalized sphere
map of an invertible real linear operator acts on positive-degree singular
homology by the sign of its determinant. In the declaration, an operator on
`EuclideanSpace ℝ (Fin (n + 2))` acts on
`H_(k+1)(SphereHomology.UnitSphere (n + 1))`.

## Outline of the proof

1. Normalize a nonzero vector to define the sphere map of an injective
   continuous linear map (`PuncturedRadial.toSphere`, `LinearSphereAction.sphereMap`).
2. Paths in a determinant-sign component give homotopic sphere maps
   (`LinearSphereAction.homotopic_of_det_mul_pos`).
3. Reflect the interval coordinate of a suspension. Its overlap-band map
   fixes the base projection, and reversing Mayer–Vietoris naturality makes
   the reflection act by negation in positive homological degrees.
4. The suspension-to-sphere homeomorphism identifies this reflection with
   first-coordinate reflection (`SphereReflection.sphereMap_suspension`).
5. Positive-determinant operators are compared with the identity; negative-
   determinant operators are compared with that reflection.

The positive-degree restriction matters: the negation statement is not
asserted for degree-zero homology.

## Main definitions and results

* `LinearSphereAction.sphereMap`: the normalized linear sphere map.
* `SuspensionReflection.reflect_homology`: negation on positive suspension homology.
* `LinearSphereAction.homology_eq_sign_smul`: the determinant-sign formula.
* `LinearSphereAction.sphereMap_comp`, `LinearSphereAction.sphereMap_trans`,
  `LinearSphereAction.sphereMap_relative`: functoriality of the normalized sphere map.
* `LinearSphereAction.homology_relative_sign`: the determinant-sign formula for two normalized
  sphere maps of a common source.

## References

* [hatcher02] A. Hatcher, *Algebraic Topology*, §2.2 (degree and reflections).

## Tags

singular-homology, spheres, degree, determinant, reflection
-/

open Set Function Filter Manifold Topology

open scoped ContinuousMap

noncomputable section

/-! ### Normalizing linear maps -/

/-- Normalize a nonzero vector to obtain a continuous map from the punctured space to its unit sphere. -/
def PuncturedRadial.toSphere {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    C(Space N, Metric.sphere (0 : N) 1) :=
  ⟨fun u => RadialExtension.direction u.val u.property,
    ((continuous_subtype_val.norm.inv₀ (fun u => norm_ne_zero_iff.mpr u.property)).smul
          continuous_subtype_val).subtype_mk
      _⟩


/-- An injective continuous linear map sends the unit sphere into the punctured target space. -/
def LinearSphereAction.puncturedMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hi : Function.Injective A) :
    C(Metric.sphere (0 : E) 1, PuncturedRadial.Space F) :=
  ⟨fun x => ⟨A x.val, fun h => ne_zero_of_mem_unit_sphere x (hi (h.trans (map_zero A).symm))⟩,
    (A.continuous.comp continuous_subtype_val).subtype_mk _⟩


/-- The map of unit spheres obtained by applying an injective continuous linear map and normalizing its output. -/
def LinearSphereAction.sphereMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hi : Function.Injective A) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp (puncturedMap A hi)


/-- Normalizing the identity linear map gives the identity map of the unit sphere. -/
theorem LinearSphereAction.sphereMap_id {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    sphereMap (ContinuousLinearMap.id ℝ E) Function.injective_id =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  ext x
  change ‖(x : E)‖⁻¹ • (x : E) = (x : E)
  rw [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]


/-- An operator in a prescribed nonzero determinant-sign component is injective. -/
theorem LinearSphereAction.component_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {signWeight : ℝ}
    (A : LinearFramePaths.operatorComponent (D := E) signWeight) :
    Function.Injective A.val := by
  have hd : A.val.toLinearMap.det ≠ 0 := by
    intro hz
    have hp : 0 < signWeight * A.val.toLinearMap.det := A.property
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)


/-- A path in a determinant-sign component induces a homotopy between the associated normalized sphere maps. -/
def LinearSphereAction.componentHomotopy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {signWeight : ℝ}
    {A B : LinearFramePaths.operatorComponent (D := E) signWeight} (γ : Path A B) :
    (sphereMap A.val (component_injective A)).Homotopy (sphereMap B.val (component_injective B))
    where
  toFun q := sphereMap (γ q.1).val (component_injective (γ q.1)) q.2
  continuous_toFun := by
    have hA : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => (γ q.1).val) :=
      continuous_subtype_val.comp (γ.continuous.comp continuous_fst)
    have hx : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact PuncturedRadial.toSphere.continuous.comp ((hA.clm_apply hx).subtype_mk _)
  map_zero_left
    x := by
    change sphereMap (γ 0).val (component_injective (γ 0)) x = _
    rw [γ.source]
  map_one_left
    x := by
    change sphereMap (γ 1).val (component_injective (γ 1)) x = _
    rw [γ.target]


/-- In a finite-dimensional real space with a basis of at least two vectors, automorphisms with determinants of the same sign induce homotopic normalized sphere maps. -/
theorem LinearSphereAction.homotopic_of_det_mul_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] [Nontrivial ι]
    (b : Module.Basis ι ℝ E) (A B : E ≃L[ℝ] E)
    (h : 0 < A.toLinearEquiv.toLinearMap.det * B.toLinearEquiv.toLinearMap.det) :
    (sphereMap A.toContinuousLinearMap A.injective).Homotopic
      (sphereMap B.toContinuousLinearMap B.injective) := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at h
    exact lt_irrefl _ h
  let A' : LinearFramePaths.operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨A.toContinuousLinearMap, mul_self_pos.mpr hd⟩
  let B' : LinearFramePaths.operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨B.toContinuousLinearMap, h⟩
  exact ⟨componentHomotopy (LinearFramePaths.joined_operatorComponent b A' B').somePath⟩


/-! ### Reflection of a suspension -/

/-- Reflect the suspension by reversing its interval coordinate and retaining the base point. -/
def SuspensionReflection.reflect {X : Type} [TopologicalSpace X] :
    C(Suspension X, Suspension X)
    where
  toFun :=
    Quotient.lift (fun q => Suspension.mk (unitInterval.symm q.1) q.2)
      (by
        rintro a b ⟨ht, h0 | h1 | hx⟩
        · apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
          refine ⟨congrArg unitInterval.symm ht, Or.inr (Or.inl ?_)⟩
          simp [h0]
        · apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
          refine ⟨congrArg unitInterval.symm ht, Or.inl ?_⟩
          simp [h1]
        · exact
            (Suspension.mk_eq_mk_iff _ _ _ _).mpr
              ⟨congrArg unitInterval.symm ht, Or.inr (Or.inr hx)⟩)
  continuous_toFun :=
    Suspension.isQuotientMap_mk.continuous_iff.mpr
      (Suspension.continuous_mk.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))


/-- Suspension reflection sends the class of `(t, x)` to the class of `(1 - t, x)`. -/
theorem SuspensionReflection.reflect_mk {X : Type} [TopologicalSpace X] (t : (unitInterval))
    (x : X) :
    reflect (Suspension.mk t x) =
      Suspension.mk (unitInterval.symm t) x :=
  rfl


/-- Suspension reflection reverses the interval-valued height. -/
theorem SuspensionReflection.reflect_height {X : Type} [TopologicalSpace X]
    (x : Suspension X) :
    Suspension.height (reflect x) =
      unitInterval.symm (Suspension.height x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.mk_surjective x
  rfl


/-- Reflection sends the northern open part of the suspension into its southern open part. -/
theorem SuspensionReflection.reflect_north {X : Type} [TopologicalSpace X] :
    Set.MapsTo (reflect (X := X)) Suspension.northOpen
      Suspension.southOpen := by
  intro x hx
  change (Suspension.height x : ℝ) < 3 / 4 at hx
  change 1 / 4 < (Suspension.height (reflect x) : ℝ)
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith


/-- Reflection sends the southern open part of the suspension into its northern open part. -/
theorem SuspensionReflection.reflect_south {X : Type} [TopologicalSpace X] :
    Set.MapsTo (reflect (X := X)) Suspension.southOpen
      Suspension.northOpen := by
  intro x hx
  change 1 / 4 < (Suspension.height x : ℝ) at hx
  change (Suspension.height (reflect x) : ℝ) < 3 / 4
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith


/-- The self-map of the overlap band induced by suspension reflection. -/
def SuspensionReflection.middleMap {X : Type} [TopologicalSpace X] :
    C(Suspension.middleBand X, Suspension.middleBand X) :=
  CoverNaturality.reversingIntersectionMap _ _ _ _ reflect reflect_north reflect_south


/-- Reflection on the overlap band leaves its projected base point unchanged. -/
theorem SuspensionReflection.middle_projection {X : Type} [TopologicalSpace X]
    (x : Suspension.middleBand X) :
    Suspension.middleBandHomotopyEquiv (middleMap x) =
      Suspension.middleBandHomotopyEquiv x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.middleBandHomeomorph.symm.surjective x
  let q : Set.Ioo (1 / 4 : ℝ) (3 / 4) × X :=
    (⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩, u)
  have hpoint :
    middleMap (Suspension.middleBandHomeomorph.symm (t, u)) =
      Suspension.middleBandHomeomorph.symm q := by
    apply Subtype.ext
    change reflect (Suspension.mk _ u) = Suspension.mk _ u
    rw [reflect_mk]
    congr 1
  rw [hpoint, Suspension.middleBandHomotopyEquiv_apply,
    Suspension.middleBandHomotopyEquiv_apply, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]


/-- The projection from the overlap band to the base is unchanged by precomposition with reflection. -/
theorem SuspensionReflection.middle_projection_comp {X : Type} [TopologicalSpace X] :
    (Suspension.middleBandHomotopyEquiv (X := X)).toFun.comp middleMap =
      (Suspension.middleBandHomotopyEquiv (X := X)).toFun :=
  ContinuousMap.ext middle_projection


/-! ### Euclidean coordinate reflection -/

/-- The continuous linear reflection in the orthogonal complement of the span of `v`. -/
noncomputable def hyperplaneReflectionOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) : E →L[ℝ] E :=
  ((ℝ ∙ v)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap


/-- Reflection orthogonal to `v` subtracts twice the component of the vector in the direction of `v`. -/
theorem hyperplaneReflectionOperator_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    hyperplaneReflectionOperator v w = w - (2 * (‖v‖ ^ 2)⁻¹ * Inner.inner ℝ v w) • v := by
  change (ℝ ∙ v)ᗮ.reflection w = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [← add_smul]
  apply congrArg (fun r : ℝ ↦ w - r • v)
  simp only [div_eq_mul_inv]
  ring


/-- The Euclidean linear isometry reflecting the first coordinate and fixing the others. -/
def SphereReflection.linearReflection (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  (ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection


/-- The coordinate reflection subtracts twice the first coordinate times the first basis vector. -/
theorem SphereReflection.linearReflection_apply (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 2))) :
    linearReflection n y = y - (2 * y 0) • EuclideanSpace.single 0 (1 : ℝ) := by
  change hyperplaneReflectionOperator (EuclideanSpace.single 0 (1 : ℝ)) y = _
  rw [hyperplaneReflectionOperator_apply]
  simp only [PiLp.norm_single, NormOneClass.norm_one, one_pow, inv_one, mul_one,
    EuclideanSpace.inner_single_left, map_one, one_mul]


/-- The first coordinate changes sign under the coordinate reflection. -/
theorem SphereReflection.linearReflection_zero (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 2))) : linearReflection n y 0 = -y 0 := by
  rw [linearReflection_apply]
  change y 0 - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) 0 = _
  simp
  ring


/-- Every coordinate after the first is fixed by the coordinate reflection. -/
theorem SphereReflection.linearReflection_succ (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) : linearReflection n y i.succ = y i.succ := by
  rw [linearReflection_apply]
  change y i.succ - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) i.succ = _
  simp


/-- The determinant of the first-coordinate reflection is `-1`. -/
theorem SphereReflection.linearReflection_det (n : ℕ) :
    (linearReflection n).toLinearMap.det = -1 := by
  have hv : (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) ≠ 0 := by simp
  change
    LinearMap.det
        ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection).toLinearMap =
      _
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv,
    pow_one]


/-- Restrict the first-coordinate reflection to the Euclidean unit sphere. -/
def SphereReflection.sphereMap (n : ℕ) :
    C(SphereHomology.UnitSphere (n + 1), SphereHomology.UnitSphere (n + 1))
    where
  toFun
    x :=
    ⟨linearReflection n x.val, by
      rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map,
        SphereHomology.unitSphere_norm]⟩
  continuous_toFun := ((linearReflection n).continuous.comp continuous_subtype_val).subtype_mk _


/-- Reversing the latitude parameter negates the signed height. -/
theorem SphereReflection.height_symm (t : (unitInterval)) :
    SphereHomology.Latitude.height (unitInterval.symm t) = -SphereHomology.Latitude.height t := by
  simp only [SphereHomology.Latitude.height, unitInterval.coe_symm_eq]
  ring


/-- Reversing the latitude parameter preserves the transverse radius. -/
theorem SphereReflection.radius_symm (t : (unitInterval)) :
    SphereHomology.Latitude.radius (unitInterval.symm t) = SphereHomology.Latitude.radius t := by
  simp only [SphereHomology.Latitude.radius, height_symm, neg_sq]


/-- Coordinate reflection reverses the latitude parameter while preserving the point of the lower-dimensional sphere. -/
theorem SphereReflection.sphereMap_latitude (n : ℕ) (t : (unitInterval))
    (x : SphereHomology.UnitSphere n) :
    sphereMap n (SphereHomology.Latitude.point n t x) =
      SphereHomology.Latitude.point n (unitInterval.symm t) x := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change
      linearReflection n (SphereHomology.Latitude.vector n t x) 0 =
        SphereHomology.Latitude.vector n (unitInterval.symm t) x 0
    rw [linearReflection_zero, SphereHomology.Latitude.vector_zero,
      SphereHomology.Latitude.vector_zero, height_symm]
  · change
      linearReflection n (SphereHomology.Latitude.vector n t x) j.succ =
        SphereHomology.Latitude.vector n (unitInterval.symm t) x j.succ
    rw [linearReflection_succ, SphereHomology.Latitude.vector_succ,
      SphereHomology.Latitude.vector_succ, radius_symm]


/-- The suspension-to-sphere homeomorphism intertwines interval reflection with first-coordinate reflection. -/
theorem SphereReflection.sphereMap_suspension (n : ℕ)
    (x : Suspension (SphereHomology.UnitSphere n)) :
    sphereMap n (SphereHomology.suspensionSphereHomeomorph n x) =
      SphereHomology.suspensionSphereHomeomorph n (SuspensionReflection.reflect x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.mk_surjective x
  rw [SphereHomology.suspensionSphereHomeomorph_mk, sphereMap_latitude,
    SuspensionReflection.reflect_mk, SphereHomology.suspensionSphereHomeomorph_mk]


/-- The suspension homeomorphism commutes with reflection in the corresponding square of continuous maps. -/
theorem SphereReflection.sphereMap_comp_suspension (n : ℕ) :
    (sphereMap n).comp (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun =
      (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun.comp
        SuspensionReflection.reflect :=
  ContinuousMap.ext (sphereMap_suspension n)


/-! ### The induced homology action -/

/-- Reflection on the overlap band induces the identity on its singular homology. -/
theorem SuspensionReflection.middle_homology {X : Type} [TopologicalSpace X] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Suspension.middleBand X) k) :
    SingularMayerVietoris.singularHomologyMap middleMap k a = a := by
  apply
    (SingularHomology.homotopyEquivHomologyEquiv
        Suspension.middleBandHomotopyEquiv k).injective
  change
    SingularMayerVietoris.singularHomologyMap
        Suspension.middleBandHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap middleMap k a) =
      SingularMayerVietoris.singularHomologyMap
        Suspension.middleBandHomotopyEquiv.toFun k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    middle_projection_comp]


/-- Interval reflection acts by negation on positive-degree homology of the suspension of a nonempty space. -/
theorem SuspensionReflection.reflect_homology {X : Type} [TopologicalSpace X] [Nonempty X]
    (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Suspension X) (n + 1)) :
    SingularMayerVietoris.singularHomologyMap reflect (n + 1) a = -a := by
  apply
    Suspension.contractibleCoverConnecting_injective
      Suspension.northOpen Suspension.southOpen
      Suspension.northOpen_isOpen
      Suspension.southOpen_isOpen Suspension.open_cover n
  rw [CoverNaturality.connecting_reversing_naturality
      Suspension.northOpen Suspension.southOpen
      Suspension.northOpen Suspension.southOpen reflect
      reflect_north reflect_south Suspension.northOpen_isOpen
      Suspension.southOpen_isOpen Suspension.open_cover
      Suspension.northOpen_isOpen
      Suspension.southOpen_isOpen Suspension.open_cover n
      a]
  change
    -SingularMayerVietoris.singularHomologyMap middleMap n
          (SingularMayerVietoris.connectingHomomorphism _ _ _ _ _ n a) =
      _
  rw [middle_homology, map_neg]


/-- First-coordinate reflection acts by negation on positive-degree homology of the Euclidean sphere. -/
theorem SphereReflection.sphereMap_homology (n k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap n) (k + 1) a = -a := by
  obtain ⟨b, rfl⟩ :=
    (SingularHomology.homotopyEquivHomologyEquiv
          (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv (k + 1)).surjective
      a
  change
    SingularMayerVietoris.singularHomologyMap (sphereMap n) (k + 1)
        (SingularMayerVietoris.singularHomologyMap
          (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun (k + 1) b) =
      _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    sphereMap_comp_suspension, SingularHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, SuspensionReflection.reflect_homology, map_neg]
  rfl


/-- Normalizing the coordinate-reflection isometry gives its direct restriction to the unit sphere. -/
theorem LinearSphereAction.sphereMap_reflection (n : ℕ) :
    sphereMap
        (SphereReflection.linearReflection n).toContinuousLinearEquiv.toContinuousLinearMap
        (SphereReflection.linearReflection n).injective =
      SphereReflection.sphereMap n := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    ‖SphereReflection.linearReflection n x.val‖⁻¹ •
        SphereReflection.linearReflection n x.val =
      SphereReflection.linearReflection n x.val
  rw [LinearIsometryEquiv.norm_map, SphereHomology.unitSphere_norm, inv_one, one_smul]


/-- A real linear automorphism with positive determinant induces the identity on homology through its normalized sphere map. -/
theorem LinearSphereAction.homology_of_det_pos (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : 0 < A.toLinearEquiv.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) k
        a =
      a := by
  have hh :=
    homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis A
      (ContinuousLinearEquiv.refl ℝ _)
      (by
        change 0 < A.toLinearEquiv.toLinearMap.det * (LinearMap.id : _ →ₗ[ℝ] _).det
        rwa [LinearMap.det_id, mul_one])
  rw [SingularHomology.homotopic_homologyMap hh k]
  change
    SingularMayerVietoris.singularHomologyMap
        (sphereMap (ContinuousLinearMap.id ℝ _) Function.injective_id) k a =
      a
  rw [sphereMap_id, SingularHomology.singularHomologyMap_id]
  rfl


/-- A real linear automorphism with negative determinant acts by negation on positive-degree sphere homology. -/
theorem LinearSphereAction.homology_of_det_neg (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : A.toLinearEquiv.toLinearMap.det < 0) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      -a := by
  have hh :=
    homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis A
      (SphereReflection.linearReflection n).toContinuousLinearEquiv
      (by
        change
          0 <
            A.toLinearEquiv.toLinearMap.det *
              (SphereReflection.linearReflection n).toLinearMap.det
        rw [SphereReflection.linearReflection_det, mul_neg_one]
        exact neg_pos.mpr h)
  rw [SingularHomology.homotopic_homologyMap hh (k + 1), sphereMap_reflection,
    SphereReflection.sphereMap_homology]


/-- On positive-degree sphere homology, the normalized map of a real linear automorphism acts by the sign of its determinant. -/
theorem LinearSphereAction.homology_eq_sign_smul (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2))) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign A.toLinearEquiv.toLinearMap.det : ℤ) • a := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  obtain hn | hp := lt_or_gt_of_ne hd
  · rw [homology_of_det_neg n A hn, sign_eq_neg_one_iff.mpr hn]
    simp
  · rw [homology_of_det_pos n A hp, sign_eq_one_iff.mpr hp]
    simp

/-- The normalized sphere map of a composite of injective continuous linear maps is the
composite of their normalized sphere maps. -/
theorem LinearSphereAction.sphereMap_comp {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E →L[ℝ] F) (B : F →L[ℝ] G) (hA : Function.Injective A)
    (hB : Function.Injective B) :
    (sphereMap B hB).comp (sphereMap A hA) = sphereMap (B.comp A) (hB.comp hA) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (B (‖A x.val‖⁻¹ • A x.val)) = NormedSpace.normalize (B (A x.val))
  rw [map_smul]
  exact
    NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (puncturedMap A hA x).property)) _

/-- The normalized sphere map of a composite of continuous linear equivalences, read through
`ContinuousLinearEquiv.trans`. -/
theorem LinearSphereAction.sphereMap_trans {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E ≃L[ℝ] F) (B : F ≃L[ℝ] G) :
    sphereMap (A.trans B).toContinuousLinearMap (A.trans B).injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap A.toContinuousLinearMap A.injective) :=
  (sphereMap_comp A.toContinuousLinearMap B.toContinuousLinearMap A.injective B.injective).symm

/-- Radially normalizing the local-degree sphere map of a continuous linear equivalence at radius
`r` gives back the normalized linear sphere map. -/
theorem LinearSphereAction.normalized_linearSphereMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) (r : ℝ)
    (hr : 0 < r) :
    PuncturedRadial.toSphere.comp (LocalDegree.linearSphereMap A r hr) =
      sphereMap A.toContinuousLinearMap A.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (A (r • x.val)) = NormedSpace.normalize (A x.val)
  rw [map_smul, NormedSpace.normalize_smul_of_pos hr]

/-- Any normalized linear sphere map factors through a second one, through the sphere map of the
relative automorphism `A.trans B.symm`. -/
theorem LinearSphereAction.sphereMap_relative {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A B : E ≃L[ℝ] F) :
    sphereMap A.toContinuousLinearMap A.injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap (A.trans B.symm).toContinuousLinearMap (A.trans B.symm).injective) := by
  rw [← sphereMap_trans]
  have heq : (A.trans B.symm).trans B = A := by
    ext x
    exact B.apply_symm_apply (A x)
  rw [heq]

/-- On positive-degree sphere homology, two normalized linear sphere maps differ by the sign of
the determinant of the relative automorphism.  This is
`LinearSphereAction.homology_eq_sign_smul` transported along
`LinearSphereAction.sphereMap_relative`. -/
theorem LinearSphereAction.homology_relative_sign {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (A B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign (A.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) a := by
  rw [sphereMap_relative A B, SingularHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, homology_eq_sign_smul]
  exact map_zsmul _ _ _

/-- Radially rescaling a unit vector to norm `r` and normalising again returns the vector. -/
theorem PuncturedRadial.toSphere_fromSphere {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : N) 1) :
    toSphere (fromSphere r hr u) = u := by
  apply Subtype.ext
  change ‖r • (u : N)‖⁻¹ • (r • (u : N)) = (u : N)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one,
    inv_smul_smul₀ hr.ne']

/-- The radial deformation of the punctured space `N \ {0}` onto the sphere of radius `r`:
a homotopy from the identity to `fromSphere r ∘ toSphere`. -/
def PuncturedRadial.deformation {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (hr : 0 < r) : (ContinuousMap.id (Space N)).Homotopy ((fromSphere r hr).comp toSphere)
    where
  toFun q := ⟨blendVector r q, blendVector_ne_zero r hr q⟩
  continuous_toFun := (continuous_blendVector r).subtype_mk _
  map_zero_left
    u := by
    apply Subtype.ext
    simp [blendVector]
  map_one_left
    u := by
    apply Subtype.ext
    simp [blendVector, fromSphere, toSphere, RadialExtension.direction, div_eq_mul_inv,
      smul_smul]

/-- `N \ {0}` is homotopy equivalent to the unit sphere of `N`, by radial deformation. -/
def PuncturedRadial.sphereHomotopyEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ Space N
    where
  toFun := fromSphere r hr
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp (fromSphere r hr) = ContinuousMap.id (Metric.sphere (0 : N) 1) :=
      ContinuousMap.ext (toSphere_fromSphere r hr)
    rw [heq]
  right_inv := ⟨(deformation r hr).symm⟩

/-- A continuous linear equivalence `E ≃L[ℝ] F` makes the unit sphere of `E` homotopy
equivalent to the punctured space `F \ {0}`. -/
def LocalDegree.linearSphereEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    Metric.sphere (0 : E) 1 ≃ₕ PuncturedRadial.Space F :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans
    (puncturedLinearHomeomorph L).toHomotopyEquiv

/-- The boundary map of local-degree boundary data, normalised to a map of unit spheres. -/
def LocalDegree.BoundaryData.normalizedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : LocalDegree.BoundaryData f L s) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp b.map
