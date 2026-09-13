/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Degree
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.Hurewicz.Straightening
import Lib.Topology.OnePointCollapse

/-!
# The Hurewicz theorem and the cube–sphere quotient

`Hurewicz.hurewiczLinearEquiv x hpi : Additive (π_ (m + 3) X x) ≃ₗ[ℤ]
SingularMayerVietoris.SingularHomology X (m + 3)` is the Hurewicz isomorphism in degree
`m + 3` for a simply connected space `X` with `Subsingleton (π_ j X x)` for
`2 ≤ j < m + 3`; `Hurewicz.hurewiczLinearEquivOfTwoLE x n hn hpi` repackages it for every
degree `n ≥ 2`.

## Outline of the construction

1. The sphere is realized as the one-point collapse of the cube boundary:
   `SphereCube.quotient : C(Fin n → unitInterval, Sphere n)` sends
   `Cube.boundary (Fin n)` to `SphereCube.point n`
   (`SphereCube.quotient_boundary`).
2. A based cube map factors through the quotient as `SphereCube.factorMap`, and
   homotopies descend through the quotient cylinder `SphereCube.cylinder`
   (`SphereCube.factorMap_homotopy`).
3. Additivity of the cube class under `transAt` concatenation is proved by
   `Hurewicz.cubeHomologyClass_transAt_zero` and `Hurewicz.cubeHomologyClass_transAt`.
4. `Hurewicz.hurewiczMap` is the induced `ℤ`-linear map on homotopy classes.
5. Normalization (`normalizedCube`, `normalizationCubeHomotopy`) gives the inverse
   `hurewiczInverse`, and the round trips `hurewiczInverse_comp_hurewiczMap` and
   `hurewiczMap_comp_hurewiczInverse` assemble the linear equivalence.

## Main definitions and results

* `SphereCube.quotient`, `SphereCube.factorMap`: the cube–sphere quotient
  and the factorization of based cube maps.
* `Hurewicz.hurewiczMap`, `Hurewicz.hurewiczInverse`: the two directions.
* `Hurewicz.hurewiczLinearEquiv`, `Hurewicz.hurewiczLinearEquivOfTwoLE`: the Hurewicz
  isomorphisms.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 4.32; the argument is
  recorded in `Lib/docs/C.md`, §§11–13 and 16.

## Tags

Hurewicz theorem, cube, sphere, quotient, singular homology
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973
/-! ### Collapsing the boundary: the cube–sphere quotient -/


/-- The map on the one-point collapse `OnePoint ↥Fᶜ` induced by `f : C(K, X)`, when `f`
sends all of the closed nonempty set `F` to `x`. -/
def OnePointCollapse.collapseLift {K X : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty) (f : C(K, X)) (x : X)
    (hf : ∀ a ∈ F, f a = x) : C(OnePoint ↥Fᶜ, X) :=
  Topology.IsQuotientMap.lift (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f
    (by
      intro a b h
      rcases (collapse_eq_iff F a b).mp h with rfl | ⟨ha, hb⟩
      · rfl
      · exact (hf a ha).trans (hf b hb).symm)

/-- `collapseLift` composed with the collapse map `collapseMap F hF` recovers `f`. -/
@[simp]
theorem OnePointCollapse.collapseLift_comp {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
    (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x) :
    (collapseLift F hF hne f x hf).comp (collapseMap F hF) = f :=
  Topology.IsQuotientMap.lift_comp (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f _

/-- The value of `collapseLift` at `collapse F a` is `f a`. -/
@[simp]
theorem OnePointCollapse.collapseLift_apply {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
    (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x) (a : K) :
    collapseLift F hF hne f x hf (collapse F a) = f a :=
  ContinuousMap.congr_fun (collapseLift_comp F hF hne f x hf) a

/-- The open unit interval `(0, 1)` as a subset of `ℝ`. -/
abbrev Hurewicz.CubeSphere.OpenUnitInterval :=
  Set.Ioo (0 : ℝ) 1

/-- The affine order isomorphism between the open unit interval `(0, 1)` and `(-1, 1)`. -/
def Hurewicz.CubeSphere.openUnitIntervalAffineOrderIso : OpenUnitInterval ≃o Set.Ioo (-1 : ℝ) 1
    where
  toFun t := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv
    t := by
    apply Subtype.ext
    change (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ)
    ring
  right_inv
    t := by
    apply Subtype.ext
    change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ)
    ring
  map_rel_iff' := by
    intro t s
    change 2 * (t : ℝ) - 1 ≤ 2 * (s : ℝ) - 1 ↔ (t : ℝ) ≤ (s : ℝ)
    constructor <;> intro h <;> linarith

/-- A homeomorphism between the open unit interval `(0, 1)` and `ℝ`. -/
def Hurewicz.CubeSphere.openUnitIntervalHomeomorph : OpenUnitInterval ≃ₜ ℝ :=
  openUnitIntervalAffineOrderIso.toHomeomorph.trans (orderIsoIooNegOneOne ℝ).toHomeomorph.symm

/-- The interior of the unit `n`-cube: the subtype of cube points not on
`Cube.boundary (Fin n)`. -/
abbrev Hurewicz.CubeSphere.CubeInteriorN (n : ℕ) :=
  { u : Fin n → (unitInterval) // u ∉ Cube.boundary (Fin n) }

/-- A cube point lies off the boundary iff every coordinate is strictly between `0`
and `1`. -/
theorem Hurewicz.CubeSphere.not_mem_cubeBoundary_iff {n : ℕ} (u : Fin n → (unitInterval)) :
    u ∉ Cube.boundary (Fin n) ↔ ∀ i, 0 < (u i : ℝ) ∧ (u i : ℝ) < 1 := by
  simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or, unitInterval.coe_pos,
    unitInterval.coe_lt_one, unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]

/-- The cube boundary is the union of the faces `u i = 0` and `u i = 1` for
`i : Fin n`. -/
theorem Hurewicz.CubeSphere.cubeBoundary_eq_iUnion (n : ℕ) :
    Cube.boundary (Fin n) =
      ⋃ i : Fin n,
        {u : Fin n → (unitInterval) | u i = 0} ∪ {u : Fin n → (unitInterval) | u i = 1} := by
  ext u
  simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]

/-- The cube boundary `Cube.boundary (Fin n)` is closed. -/
theorem Hurewicz.CubeSphere.isClosed_cubeBoundaryN (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  rw [cubeBoundary_eq_iUnion]
  exact
    isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const)

/-- The cube interior is homeomorphic to `Fin n → OpenUnitInterval` by restricting the
coordinates. -/
def Hurewicz.CubeSphere.cubeInteriorCoordinates (n : ℕ) : CubeInteriorN n ≃ₜ (Fin n → OpenUnitInterval)
    where
  toFun u i := ⟨(u.val i : ℝ), (not_mem_cubeBoundary_iff u.val).mp u.property i⟩
  invFun
    v :=
    ⟨fun i => ⟨(v i : ℝ), ⟨(v i).property.1.le, (v i).property.2.le⟩⟩,
      (not_mem_cubeBoundary_iff _).mpr fun i => (v i).property⟩
  left_inv
    u := by
    apply Subtype.ext
    funext i
    exact Subtype.ext rfl
  right_inv
    v := by
    funext i
    exact Subtype.ext rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun u : CubeInteriorN n => u.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (continuous_subtype_val.comp hi).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun v : Fin n → OpenUnitInterval => v i) := continuous_apply i
    exact (continuous_subtype_val.comp hi).subtype_mk _

/-- The cube interior is homeomorphic to `EuclideanSpace ℝ (Fin n)`, coordinatewise via
`openUnitIntervalHomeomorph`. -/
def Hurewicz.CubeSphere.cubeInteriorEuclideanHomeomorph (n : ℕ) :
    CubeInteriorN n ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (cubeInteriorCoordinates n).trans
    ((Homeomorph.piCongrRight fun _ : Fin n => openUnitIntervalHomeomorph).trans
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm)

/-- The `n`-sphere as the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`. -/
abbrev SphereCube.Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The one-point compactification of the cube interior is homeomorphic to the
`n`-sphere. -/
def SphereCube.compactification (n : ℕ) :
    OnePoint (Hurewicz.CubeSphere.CubeInteriorN n) ≃ₜ Sphere n :=
  (Hurewicz.CubeSphere.cubeInteriorEuclideanHomeomorph n).onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n)) (ι := Fin (n + 1)) (by simp))

/-- The basepoint of `Sphere n`: the image of the point at infinity of the cube
interior's compactification. -/
def SphereCube.point (n : ℕ) : Sphere n :=
  compactification n (OnePoint.infty)

/-- The quotient map from the unit `n`-cube to the `n`-sphere, collapsing
`Cube.boundary (Fin n)` to `point n`. -/
def SphereCube.quotient (n : ℕ) : C(Fin n → (unitInterval), Sphere n) :=
  (compactification n : C(OnePoint (Hurewicz.CubeSphere.CubeInteriorN n), Sphere n)).comp
    (OnePointCollapse.collapseMap (Cube.boundary (Fin n)) (Hurewicz.CubeSphere.isClosed_cubeBoundaryN n))

/-- Every boundary point of the cube is sent by `quotient n` to the sphere basepoint. -/
theorem SphereCube.quotient_boundary (n : ℕ) (z : Fin n → (unitInterval))
    (hz : z ∈ Cube.boundary (Fin n)) : quotient n z = point n := by
  change
    compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) z) =
      compactification n (OnePoint.infty)
  rw [OnePointCollapse.collapse_of_mem _ hz]

/-- The all-zero corner of the cube lies on the boundary when `0 < n`. -/
theorem SphereCube.zero_boundary {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → (unitInterval)) ∈ Cube.boundary (Fin n) :=
  ⟨⟨0, hn⟩, Or.inl rfl⟩

/-- The cube-to-sphere quotient map is surjective when `0 < n`. -/
theorem SphereCube.quotient_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (quotient n) :=
  (compactification n).surjective.comp
    (OnePointCollapse.collapse_surjective (Cube.boundary (Fin n)) ⟨0, zero_boundary hn⟩)

/-- Two cube points have the same image under `quotient n` iff they are equal or both
lie on the cube boundary. -/
theorem SphereCube.quotient_eq_iff (n : ℕ) (z w : Fin n → (unitInterval)) :
    quotient n z = quotient n w ↔ z = w ∨ z ∈ Cube.boundary (Fin n) ∧ w ∈ Cube.boundary (Fin n) :=
  by
  change
    compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) z) =
        compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) w) ↔
      _
  rw [(compactification n).injective.eq_iff, OnePointCollapse.collapse_eq_iff]

/-- The product of the identity on `unitInterval` with the cube-to-sphere quotient:
the cylinder over the quotient. -/
def SphereCube.cylinder (n : ℕ) :
    C((unitInterval) × (Fin n → (unitInterval)), (unitInterval) × Sphere n) :=
  (ContinuousMap.id (unitInterval)).prodMap (quotient n)

/-- The cylinder over the quotient is surjective when `0 < n`. -/
theorem SphereCube.cylinder_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (cylinder n) := by
  rintro ⟨t, z⟩
  obtain ⟨w, rfl⟩ := quotient_surjective hn z
  exact ⟨(t, w), rfl⟩

/-- The cylinder over the quotient is a quotient map when `0 < n`. -/
theorem SphereCube.cylinder_isQuotientMap {n : ℕ} (hn : 0 < n) :
    Topology.IsQuotientMap (cylinder n) :=
  .of_surjective_continuous (cylinder_surjective hn) (cylinder n).continuous

/-- The based cube map `GenLoop (Fin n) X (u (point n))` obtained by precomposing a
sphere map `u` with the quotient; it is constant `u (point n)` on the boundary. -/
def SphereCube.basedCube {n : ℕ} {X : Type*} [TopologicalSpace X] (u : C(Sphere n, X)) :
    GenLoop (Fin n) X (u (point n)) :=
  ⟨u.comp (quotient n), fun z hz => congrArg u (quotient_boundary n z hz)⟩

/-- If `π_ n X (u (point n))` is a subsingleton, the sphere map `u` is homotopic
relative to the basepoint to the constant map at `u (point n)`. -/
theorem SphereCube.homotopicRel_const_of_subsingleton {n : ℕ} {X : Type*}
    [TopologicalSpace X] (hn : 0 < n) (u : C(Sphere n, X)) [Subsingleton (π_ n X (u (point n)))] :
    u.HomotopicRel (ContinuousMap.const (Sphere n) (u (point n))) {point n} := by
  let H := Hurewicz.nativeCubeNullHomotopy (basedCube u)
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact
        ((H.eq_fst t hz).trans ((basedCube u).property z hz)).trans
          ((H.eq_fst t hw).trans ((basedCube u).property w hw)).symm
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : (unitInterval)) (z : Fin n → (unitInterval)) : G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun
      ((cylinder_isQuotientMap hn).lift_comp H.toHomotopy.toContinuousMap hfib) (t, z)
  refine
    ⟨{  toContinuousMap := G
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans (H.apply_zero w)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans (H.apply_one w)
  · intro t z hz
    have hz' : z = point n := hz
    subst z
    change G (t, point n) = u (point n)
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact H.eq_fst t (zero_boundary hn)

/-- The quotient map from the cube to the sphere, as a based loop. -/
def SphereCube.quotientLoop (n : ℕ) : GenLoop (Fin n) (Sphere n) (point n) :=
  ⟨quotient n, quotient_boundary n⟩

/-- The underlying map of `quotientLoop n` is the quotient map `quotient n`. -/
@[simp]
theorem SphereCube.quotientLoop_val (n : ℕ) : (quotientLoop n).val = quotient n :=
  rfl

/-! ### Factor maps through the quotient -/

/-- The factor map of a based loop through the sphere quotient: the loop pushed to the sphere
is the identity on the cube class. -/
def SphereCube.factorMap {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin n) X x) : C(Sphere n, X) :=
  (OnePointCollapse.collapseLift (Cube.boundary (Fin n)) (Hurewicz.CubeSphere.isClosed_cubeBoundaryN n)
        ⟨0, zero_boundary hn⟩ p.val x (fun u hu => p.property u hu)).comp
    ((compactification n).symm : C(Sphere n, OnePoint (Hurewicz.CubeSphere.CubeInteriorN n)))

/-- The factor map on the quotient image of a cube point is the loop's value. -/
@[simp]
theorem SphereCube.factorMap_quotient {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) (u : Fin n → (unitInterval)) :
    factorMap hn p (quotient n u) = p u := by
  change
    OnePointCollapse.collapseLift (Cube.boundary (Fin n)) (Hurewicz.CubeSphere.isClosed_cubeBoundaryN n)
        ⟨0, zero_boundary hn⟩ p.val x (fun v hv => p.property v hv)
        ((compactification n).symm (compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) u))) =
      p u
  rw [(compactification n).symm_apply_apply]
  exact OnePointCollapse.collapseLift_apply (Cube.boundary (Fin n))
    (Hurewicz.CubeSphere.isClosed_cubeBoundaryN n) ⟨0, zero_boundary hn⟩ p.val x
    (fun v hv => p.property v hv) u

/-- The factor map composed with the quotient is the loop. -/
@[simp]
theorem SphereCube.factorMap_comp_quotient {n : ℕ} (hn : 0 < n) {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) :
    (factorMap hn p).comp (quotient n) = p.val := by
  ext u
  exact factorMap_quotient hn p u

/-- The factor map is the unique continuous map factoring the loop through the quotient. -/
theorem SphereCube.factorMap_unique {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) (f : C(Sphere n, X))
    (hf : f.comp (quotient n) = p.val) : f = factorMap hn p := by
  ext z
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  exact (ContinuousMap.congr_fun hf u).trans (factorMap_quotient hn p u).symm

/-- The factor map on the cube chain: pushing the sphere's cube chain along the factor map
recovers the loop's cube chain. -/
theorem SphereCube.factor_cubeChain {n : ℕ} (hn : 0 < n) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) :
    SingularChains.inducedChain (factorMap hn p) n
        (Hurewicz.cubeChain (quotientLoop n)) =
      Hurewicz.cubeChain p := by
  simp only [Hurewicz.cubeChain]
  rw [quotientLoop_val, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
    factorMap_comp_quotient]

/-- The factor map on the cube cycle: the sphere's cube cycle maps to the loop's cube cycle. -/
theorem SphereCube.factor_cubeCycle {n : ℕ} (hn : 0 < n) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x)
    (hσ : Hurewicz.cubeChain (quotientLoop n) ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (Sphere n)) n)
    (hp : Hurewicz.cubeChain p ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (factorMap hn p)) n
        ⟨Hurewicz.cubeChain (quotientLoop n), hσ⟩ =
      ⟨Hurewicz.cubeChain p, hp⟩ := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact factor_cubeChain hn p

/-- The factor map on the cube homology class: the sphere's cube class maps to the loop's
cube class. -/
theorem SphereCube.factor_cubeHomologyClass {n : ℕ} (hn : 0 < n) {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hσ : Hurewicz.cubeChain (quotientLoop n) ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (Sphere n)) n)
    (hp : Hurewicz.cubeChain p ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.singularHomologyMap (factorMap hn p) n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex (Sphere n)) n
          ⟨Hurewicz.cubeChain (quotientLoop n), hσ⟩) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex X) n ⟨Hurewicz.cubeChain p, hp⟩ := by
  rw [SingularMayerVietoris.singularHomologyMap]
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  exact congrArg _ (factor_cubeCycle hn p hσ hp)

/-- The factor map on the cube homology class, using the general cube cycle. -/
theorem SphereCube.factor_cubeHomologyClass_cycle {m : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.singularHomologyMap (factorMap (Nat.succ_pos (m + 1)) p) (m + 2)
        (Hurewicz.cubeHomologyClass (quotientLoop (m + 2))) =
      Hurewicz.cubeHomologyClass p := by
  unfold Hurewicz.cubeHomologyClass
  rw [SingularMayerVietoris.singularHomologyMap,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply congrArg
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, Hurewicz.cubeCycle_val,
    Hurewicz.cubeCycle_val]
  exact factor_cubeChain (Nat.succ_pos (m + 1)) p

/-- A homotopy of based cubes relative to the boundary descends to a homotopy of
factor maps on the sphere. -/
def SphereCube.factorMap_homotopy {n : ℕ} (hn : 0 < n) {X : Type*}
    [TopologicalSpace X] {x : X} {p q : GenLoop (Fin n) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (factorMap hn p).Homotopy (factorMap hn q) := by
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact
        ((H.eq_fst t hz).trans (p.property z hz)).trans
          ((H.eq_fst t hw).trans (p.property w hw)).symm
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : (unitInterval)) (z : Fin n → (unitInterval)) :
      G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun
      ((cylinder_isQuotientMap hn).lift_comp H.toHomotopy.toContinuousMap hfib) (t, z)
  refine
    { toContinuousMap := G
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans ((H.apply_zero w).trans (factorMap_quotient hn p w).symm)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans ((H.apply_one w).trans (factorMap_quotient hn q w).symm)

/-! ### Additivity of the cube class -/

/-- Homotopic based cubes have the same cube homology class. -/
theorem Hurewicz.cubeHomologyClass_homotopic {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} {p q : GenLoop (Fin (m + 2)) X x} (h : GenLoop.Homotopic p q) :
    Hurewicz.cubeHomologyClass p = Hurewicz.cubeHomologyClass q := by
  obtain ⟨H⟩ := h
  have Hf : (SphereCube.factorMap (Nat.succ_pos (m + 1)) p).Homotopic
      (SphereCube.factorMap (Nat.succ_pos (m + 1)) q) :=
    ⟨SphereCube.factorMap_homotopy (Nat.succ_pos (m + 1)) H⟩
  rw [← SphereCube.factor_cubeHomologyClass_cycle p,
    ← SphereCube.factor_cubeHomologyClass_cycle q]
  exact congrArg (fun F => F (Hurewicz.cubeHomologyClass
      (SphereCube.quotientLoop (m + 2))))
    (SingularHomology.homotopic_homologyMap Hf (m + 2))

/-- In degree `2` the cube homology class is the square homology class. -/
theorem Hurewicz.cubeHomologyClass_eq_squareHomologyClass {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    Hurewicz.cubeHomologyClass (m := 0) p = SecondHurewicz.squareHomologyClass p := by
  unfold Hurewicz.cubeHomologyClass SecondHurewicz.squareHomologyClass
  apply congrArg
  apply Subtype.ext
  change Hurewicz.cubeChain p = SecondHurewicz.squareChain p
  exact Hurewicz.cubeChain_eq_squareChain p

/-- Concatenation along the first coordinate adds cube classes in degree `2`. -/
theorem Hurewicz.cubeHomologyClass_transAt_two {X : Type} [TopologicalSpace X]
    {x : X} (p q : GenLoop (Fin 2) X x) :
    Hurewicz.cubeHomologyClass (m := 0) (GenLoop.transAt (0 : Fin 2) p q) =
      Hurewicz.cubeHomologyClass (m := 0) p +
        Hurewicz.cubeHomologyClass (m := 0) q := by
  simpa only [Hurewicz.cubeHomologyClass_eq_squareHomologyClass] using
    SecondHurewicz.squareHomologyClass_transAt p q


/-- Concatenation along any coordinate adds cube classes in degree `2`. -/
theorem Hurewicz.cubeHomologyClass_transAt_two_coord {X : Type} [TopologicalSpace X]
    {x : X} (i : Fin 2) (p q : GenLoop (Fin 2) X x) :
    Hurewicz.cubeHomologyClass (m := 0) (GenLoop.transAt i p q) =
      Hurewicz.cubeHomologyClass (m := 0) p +
        Hurewicz.cubeHomologyClass (m := 0) q := by
  have h : GenLoop.Homotopic (GenLoop.transAt i p q)
      (GenLoop.transAt (0 : Fin 2) p q) :=
    Quotient.eq.mp (HomotopyGroup.transAt_indep (0 : Fin 2) p q)
  rw [Hurewicz.cubeHomologyClass_homotopic h]
  exact Hurewicz.cubeHomologyClass_transAt_two p q

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The extra term of the `transAt 0` cube-chain difference is a boundary at every
degree. -/
theorem Hurewicz.cubeChain_transAt_zero_extra_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    ∃ W : SingularChains.Chains X (n + 3),
      ((SingularChains.singularComplex X).d (n + 3) (n + 2)).hom W =
        SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
          (SingularHomology.crossProductTriangle (unitInterval)
            (Fin (n + 1) → (unitInterval)) n
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight)
            (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
              (Hurewicz.fundamentalCubeChain (n + 1)))) := by
  obtain ⟨k, hk⟩ := Hurewicz.cubeChain_transAt_zero_extra_eq_smul p q
  by_cases hEven : Even (n + 2)
  · have hdiff := Hurewicz.cubeChain_transAt_zero_diff_boundary p q
    have hp := Hurewicz.cubeChain_boundary p
    have hq := Hurewicz.cubeChain_boundary q
    have ht := Hurewicz.cubeChain_boundary (GenLoop.transAt (0 : Fin (n + 2)) p q)
    have hdd :
        ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
            (((SingularChains.singularComplex X).d (n + 3) (n + 2)).hom
              (SingularChains.inducedChain
                ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
                  (Hurewicz.cubeCoordinates (n + 1))) (n + 3)
                (SingularHomology.crossProductTriangle (unitInterval)
                  (Fin (n + 1) → (unitInterval)) (n + 1)
                  (SingularChains.concatChain Hurewicz.intervalPathLeft
                    Hurewicz.intervalPathRight)
                  (Hurewicz.fundamentalCubeChain (n + 1))))) = 0 :=
      congrArg (fun f : SingularChains.Chains X (n + 3) ⟶ SingularChains.Chains X (n + 1) =>
          f.hom _) ((SingularChains.singularComplex X).d_comp_d (n + 3) (n + 2) (n + 1))
    have hextra0 :
        ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
            (SingularChains.inducedChain
              ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
                (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
              (SingularHomology.crossProductTriangle (unitInterval)
                (Fin (n + 1) → (unitInterval)) n
                (SingularChains.concatChain Hurewicz.intervalPathLeft
                  Hurewicz.intervalPathRight)
                (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
                  (Hurewicz.fundamentalCubeChain (n + 1))))) = 0 := by
      have h := congrArg ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom hdiff
      simp only [map_sub, map_add, hp, hq, ht, hdd, add_zero, sub_zero, zero_sub] at h
      exact neg_eq_zero.mp h.symm
    have hk0 : k = 0 := by
      have hbound := congrArg ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom hk
      rw [hextra0, map_zsmul, Hurewicz.boundary_const_simplex, Fin.sum_neg_one_pow] at hbound
      have hodd : ¬Even (n + 3) := Nat.not_even_iff_odd.mpr hEven.add_one
      simp only [if_neg hodd, one_smul] at hbound
      have haug :=
        congrArg (SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1)) hbound
      simpa [map_zero, map_zsmul, SecondHurewicz.SimplyConnected.chainAugmentation_simplex]
        using haug.symm
    refine ⟨0, ?_⟩
    rw [hk, hk0, zero_smul, map_zero]
  · refine ⟨k • SingularChains.simplexChain X (n + 3)
        (ContinuousMap.const (SingularChains.Simplex (n + 3)) x), ?_⟩
    rw [hk, map_zsmul, Hurewicz.boundary_const_simplex, Fin.sum_neg_one_pow]
    have hodd : ¬Even (n + 4) := by
      simpa [show n + 4 = n + 2 + 2 from rfl, Nat.even_add] using hEven
    simp [if_neg hodd]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Concatenation along coordinate `0` adds cube homology classes at every degree `n ≥ 2`. -/
theorem Hurewicz.cubeHomologyClass_transAt_zero {m : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (m + 2)) X x) :
    Hurewicz.cubeHomologyClass (GenLoop.transAt (0 : Fin (m + 2)) p q) =
      Hurewicz.cubeHomologyClass p + Hurewicz.cubeHomologyClass q := by
  obtain ⟨Wextra, hWextra⟩ := Hurewicz.cubeChain_transAt_zero_extra_boundary p q
  have hdiff := Hurewicz.cubeChain_transAt_zero_diff_boundary p q
  unfold Hurewicz.cubeHomologyClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (SingularChains.singularComplex X) (m + 2)
        (Hurewicz.cubeCycle (GenLoop.transAt (0 : Fin (m + 2)) p q))
        (Hurewicz.cubeCycle p + Hurewicz.cubeCycle q)).mpr
  refine ⟨Wextra -
      SingularChains.inducedChain
        ((GenLoop.transAt (0 : Fin (m + 2)) p q).val.comp
          (Hurewicz.cubeCoordinates (m + 1))) (m + 3)
        (SingularHomology.crossProductTriangle (unitInterval)
          (Fin (m + 1) → (unitInterval)) (m + 1)
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight)
          (Hurewicz.fundamentalCubeChain (m + 1))), ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sub, Hurewicz.cubeCycle_val, map_sub, hWextra]
  rw [show Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (m + 2)) p q) -
        (Hurewicz.cubeChain p + Hurewicz.cubeChain q) =
      - (Hurewicz.cubeChain p + Hurewicz.cubeChain q -
          Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (m + 2)) p q)) by abel,
    hdiff]
  abel

/-- Concatenation along any coordinate adds cube homology classes at every degree `n ≥ 2`. -/
theorem Hurewicz.cubeHomologyClass_transAt {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (i : Fin (m + 2)) (p q : GenLoop (Fin (m + 2)) X x) :
    Hurewicz.cubeHomologyClass (GenLoop.transAt i p q) =
      Hurewicz.cubeHomologyClass p + Hurewicz.cubeHomologyClass q := by
  have h : GenLoop.Homotopic (GenLoop.transAt i p q)
      (GenLoop.transAt (0 : Fin (m + 2)) p q) :=
    Quotient.eq.mp (HomotopyGroup.transAt_indep (0 : Fin (m + 2)) p q)
  rw [Hurewicz.cubeHomologyClass_homotopic h]
  exact Hurewicz.cubeHomologyClass_transAt_zero p q


/-! ### The Hurewicz linear map -/

/-- The Hurewicz function at degree `n ≥ 2`: the cube homology class of a representative. -/
def Hurewicz.hurewiczFunction {m : ℕ} {X : Type} [TopologicalSpace X] (x : X) :
    π_ (m + 2) X x → SingularMayerVietoris.SingularHomology X (m + 2) :=
  Quotient.lift Hurewicz.cubeHomologyClass fun _ _ h =>
    Hurewicz.cubeHomologyClass_homotopic h

/-- The Hurewicz function as a group homomorphism `π_n →+ (H_n, +)` written multiplicatively. -/
def Hurewicz.hurewiczPi {m : ℕ} {X : Type} [TopologicalSpace X] (x : X) :
    π_ (m + 2) X x →* Multiplicative (SingularMayerVietoris.SingularHomology X (m + 2))
    where
  toFun a := Multiplicative.ofAdd (Hurewicz.hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (Hurewicz.cubeHomologyClass_const (x := x))
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ (m + 2) X x =>
            Multiplicative.ofAdd (Hurewicz.hurewiczFunction x c))
          (HomotopyGroup.mul_spec (i := (0 : Fin (m + 2))) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd
          (Hurewicz.cubeHomologyClass (GenLoop.transAt (0 : Fin (m + 2)) q p)) =
        Multiplicative.ofAdd
          (Hurewicz.cubeHomologyClass p + Hurewicz.cubeHomologyClass q)
    apply congrArg Multiplicative.ofAdd
    rw [Hurewicz.cubeHomologyClass_transAt_zero q p]
    exact add_comm _ _

/-- The Hurewicz map in degree `n ≥ 2`, as a `ℤ`-linear map on the additive homotopy group. -/
def Hurewicz.hurewiczMap {m : ℕ} {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ (m + 2) X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X (m + 2)
    where
  toFun := (Hurewicz.hurewiczPi (m := m) x).toAdditiveLeft
  map_add' := (Hurewicz.hurewiczPi (m := m) x).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using
      map_intCast_smul (Hurewicz.hurewiczPi (m := m) x).toAdditiveLeft ℤ ℤ n a

/-- The cube chain of a based simplex loop is the corrected simplex chain (the identity
permutation cell is the simplex itself; every other Kuhn cell is constant, and the total
orientation of the constants vanishes). -/
theorem Hurewicz.cubeChain_basedSimplexLoop {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (τ : Hurewicz.SimplexGeometry.BasedSimplex (n + 2) x) :
    Hurewicz.cubeChain (Hurewicz.SimplexGeometry.basedSimplexLoop τ) =
      Hurewicz.correctedSimplexChain (n + 2) x τ.val := by
  rw [Hurewicz.cubeChain_eq_sum_simplices]
  exact Hurewicz.SimplexGeometry.basedSimplex_simplexChain_sum τ

/-- The Hurewicz map on a representative is the cube homology class. -/
theorem Hurewicz.hurewiczMap_representative {m : ℕ} {X : Type} [TopologicalSpace X]
    (x : X) (p : GenLoop (Fin (m + 2)) X x) :
    Hurewicz.hurewiczMap (m := m) x (Additive.ofMul (⟦p⟧ : π_ (m + 2) X x)) =
      Hurewicz.cubeHomologyClass p :=
  rfl

/-- The Hurewicz image of a based simplex class is the class of its corrected simplex cycle. -/
theorem Hurewicz.hurewicz_basedSimplexClass {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (τ : Hurewicz.SimplexGeometry.BasedSimplex (n + 2) x) :
    Hurewicz.hurewiczMap (m := n) x
        (Hurewicz.SimplexGeometry.basedSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 2)
        (Hurewicz.correctedSimplexCycle (n + 1) x τ.val
          (Hurewicz.SimplexGeometry.basedSimplex_face (n := n + 1) τ)) := by
  rw [Hurewicz.SimplexGeometry.basedSimplexClass,
    Hurewicz.hurewiczMap_representative]
  unfold Hurewicz.cubeHomologyClass
  congr 1
  apply Subtype.ext
  exact Hurewicz.cubeChain_basedSimplexLoop τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a cycle, the Hurewicz map of the class operator recovers the cycle class. -/
theorem Hurewicz.hurewiczMap_classOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (m + 3)) :
    Hurewicz.hurewiczMap (m := m + 1) x
        (Hurewicz.classOperator x (m + 3) hpi c.1) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X)
        (m + 3) c := by
  let S := Hurewicz.normalizationTower x m fun j hj hj' => hpi j hj (by omega)
  let f := Hurewicz.normalizedSimplex x (m + 3) hpi
  have hcomp :
      (Hurewicz.hurewiczMap (m := m + 1) x).comp
          (Hurewicz.classOperator x (m + 3) hpi) =
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X)
            (m + 3)).comp
          (Hurewicz.normalizedCycleAssignment (m + 2) x f) := by
    apply SingularChains.chainMap_ext X (m + 3)
    intro smp
    simp only [LinearMap.comp_apply, Hurewicz.classOperator_simplex,
      Hurewicz.normalizedCycleAssignment_simplex]
    exact Hurewicz.hurewicz_basedSimplexClass (f smp)
  have h := LinearMap.congr_fun hcomp c.1
  simp only [LinearMap.comp_apply] at h
  rw [h]
  exact Hurewicz.normalizedCycleAssignment_class (m + 2) x f S.aug S.nxt S.compat
    (fun smp => by
      apply ContinuousMap.ext
      intro s
      exact S.nxt_zero smp s)
    (fun smp => rfl) c

/-- `hurewiczMap ∘ hurewiczInverse = id` at degree `n ≥ 3`. -/
theorem Hurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x)) :
    (Hurewicz.hurewiczMap (m := m + 1) x).comp (Hurewicz.hurewiczInverse x hpi) =
      LinearMap.id :=
  Hurewicz.comp_singularHomologyDesc_eq_id (m + 3)
    (Hurewicz.classOperator x (m + 3) hpi)
    (Hurewicz.classOperator_boundary x hpi)
    (Hurewicz.hurewiczMap (m := m + 1) x)
    (Hurewicz.hurewiczMap_classOperator_cycle x hpi)

/-- The composite `hurewiczMap ∘ hurewiczInverse` is the identity on degree-`m + 3`
singular homology classes. -/
@[simp]
theorem Hurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (c : SingularMayerVietoris.SingularHomology X (m + 3)) :
    Hurewicz.hurewiczMap (m := m + 1) x (Hurewicz.hurewiczInverse x hpi c) = c :=
  LinearMap.congr_fun (Hurewicz.hurewiczMap_comp_hurewiczInverse x hpi) c


attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class operator on a cube chain is the signed sum of normalized cell classes. -/
theorem Hurewicz.classOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) :
    Hurewicz.classOperator x (m + 3) hpi (Hurewicz.cubeChain p) =
      ∑ e : Equiv.Perm (Fin (m + 3)),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          Hurewicz.SimplexGeometry.basedSimplexClass
            (Hurewicz.normalizedSimplex x (m + 3) hpi
              (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [Hurewicz.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, Hurewicz.classOperator_simplex]

/-! ### Normalization and the inverse -/

namespace Hurewicz

open SecondHurewicz.SimplyConnected

/-- The edge tower's high storey is stationary on the constant simplex. -/
theorem edgeTower_high_const {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (k : ℕ) :
    (edgeTower x k).high (ContinuousMap.const (SingularChains.Simplex (k + 1)) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex (k + 1)) x := by
  induction k with
  | zero => exact edgeStraighteningHomotopy_const x
  | succ k ih =>
    exact Hurewicz.extendCoherentSimplexHomotopy_const _ _ _ (edgeTower x k).high_zero x ih

/-- The edge tower's low storey is stationary on the constant simplex. -/
theorem edgeTower_low_const {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (k : ℕ) :
    (edgeTower x k).low (ContinuousMap.const (SingularChains.Simplex k) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex k) x := by
  cases k with
  | zero => rfl
  | succ k => exact edgeTower_high_const x k

/-- The vertex-then-edge normalization is stationary on the constant simplex. -/
theorem vertexEdgeHomotopy_const {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (k : ℕ) :
    vertexEdgeHomotopy x k (ContinuousMap.const (SingularChains.Simplex k) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex k) x :=
  Hurewicz.composeSimplexHomotopies_const _ _ _ _ x (vertexStraighteningHomotopy_const x k)
    (edgeTower_low_const x k)

/-- Every storey of the normalization tower is stationary on the constant simplex. -/
theorem normalizationTower_const {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (k : ℕ) (hpi : ∀ j, 2 ≤ j → j ≤ k + 2 → Subsingleton (π_ j X x)) :
    (normalizationTower x k hpi).aug (ContinuousMap.const (SingularChains.Simplex (k + 2)) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex (k + 2)) x ∧
      (normalizationTower x k hpi).nxt (ContinuousMap.const (SingularChains.Simplex (k + 3)) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex (k + 3)) x := by
  induction k with
  | zero =>
    letI := hpi 2 (by omega) (by omega)
    constructor
    · exact Hurewicz.composeSimplexHomotopies_const _ _ _ _ x (vertexEdgeHomotopy_const x 2)
        (simplexStraighteningHomotopy_const 2 x)
    · exact Hurewicz.composeSimplexHomotopies_const _ _ _ _ x (vertexEdgeHomotopy_const x 3)
        (Hurewicz.extendCoherentSimplexHomotopy_const _ _ _ _ x
          (simplexStraighteningHomotopy_const 2 x))
  | succ k ih =>
    letI := hpi (k + 3) (by omega) (by omega)
    have hc := ih fun j hj hjk => hpi j hj (by omega)
    constructor
    · exact Hurewicz.composeSimplexHomotopies_const _ _ _ _ x hc.2
        (simplexStraighteningHomotopy_const (k + 3) x)
    · exact Hurewicz.composeSimplexHomotopies_const _ _ _ _ x
        (Hurewicz.extendCoherentSimplexHomotopy_const _ _ _ _ x hc.2)
        (Hurewicz.extendCoherentSimplexHomotopy_const _ _ _ _ x
          (simplexStraighteningHomotopy_const (k + 3) x))

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The normalized form of a based `(m + 3)`-cube map: the endpoint of the coherent
cube homotopy assembled from the normalization tower. -/
def normalizedCube (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) : GenLoop (Fin (m + 3)) X x :=
  let S := normalizationTower x m (fun j hj hj' => hpi j hj (by omega))
  CubeGluing.coherentCubeEndpoint S.aug S.nxt S.compat
    (normalizationTower_const x m _).1 p

/-- On each Freudenthal–Kuhn cell `e`, the normalized cube agrees with the normalized
simplex of the corresponding simplex restriction of `p`. -/
theorem normalizedCube_cell (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) (e : Equiv.Perm (Fin (m + 3))) :
    (normalizedCube x hpi p).val.comp (CubeTriangulation.cubeSimplex e) =
      (normalizedSimplex x (m + 3) hpi (p.val.comp (CubeTriangulation.cubeSimplex e))).val := by
  let S := normalizationTower x m (fun j hj hj' => hpi j hj (by omega))
  exact CubeGluing.coherentCubeEndpoint_cell S.aug S.nxt S.compat
    (normalizationTower_const x m _).1 p e

/-- The homotopy from a based cube map `p` to its normalization `normalizedCube x hpi p`. -/
def normalizationCubeHomotopy (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) :
    p.val.HomotopyRel (normalizedCube x hpi p).val (Cube.boundary (Fin (m + 3))) :=
  let S := normalizationTower x m (fun j hj hj' => hpi j hj (by omega))
  CubeGluing.coherentCubeHomotopy S.aug S.nxt S.compat
    (normalizationTower_const x m _).1 S.nxt_zero p

/-- The normalized cube is internally based in the sense of
`NativeSubdivision.NativeCubeInternalBased`. -/
theorem normalizedCube_internalBased (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) :
    NativeSubdivision.NativeCubeInternalBased (normalizedCube x hpi p) := by
  let S := normalizationTower x m (fun j hj hj' => hpi j hj (by omega))
  exact coherentCubeEndpoint_internalBased S.aug S.nxt S.compat
    (normalizationTower_const x m _).1 S.aug_one p

/-- The `e`-th based simplex of the normalized cube's subdivision is the normalized
simplex of `p` restricted to the cell `cubeSimplex e`. -/
theorem normalizedCube_simplex (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) (e : Equiv.Perm (Fin (m + 3))) :
    NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x hpi p)
      (normalizedCube_internalBased x hpi p) e =
      normalizedSimplex x (m + 3) hpi (p.val.comp (CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x hpi p e

/-- The class operator sends the cube chain of `p` to the additive form of its
homotopy class `⟦p⟧`. -/
theorem classOperator_cubeChain (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) :
    classOperator x (m + 3) hpi (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ (m + 3) X x) := by
  have h := (NativeSubdivision.nativeClass_homotopic
    (p := p) (q := normalizedCube x hpi p) ⟨normalizationCubeHomotopy x hpi p⟩).trans
    (NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x hpi p)
      (normalizedCube_internalBased x hpi p))
  simp only [normalizedCube_simplex] at h
  exact (classOperator_cubeChain_sum x hpi p).trans h.symm

/-- The inverse Hurewicz map recovers `⟦p⟧` from the image of `p`'s class under
`hurewiczMap`. -/
@[simp]
theorem hurewiczInverse_hurewiczMap_mk (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (p : GenLoop (Fin (m + 3)) X x) :
    hurewiczInverse x hpi (hurewiczMap (m := m + 1) x (Additive.ofMul (⟦p⟧ : π_ (m + 3) X x))) =
      Additive.ofMul (⟦p⟧ : π_ (m + 3) X x) := by
  rw [hurewiczMap_representative]
  change hurewiczInverse x hpi (SingularMayerVietoris.ModuleHomology.cycleClass
    (SingularChains.singularComplex X) (m + 3) (cubeCycle p)) = _
  rw [hurewiczInverse_cycleClass]
  exact classOperator_cubeChain x hpi p

/-- `hurewiczInverse` is a left inverse of `hurewiczMap` on `Additive (π_ (m+3) X x)`. -/
@[simp]
theorem hurewiczInverse_hurewiczMap (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (a : Additive (π_ (m + 3) X x)) :
    hurewiczInverse x hpi (hurewiczMap (m := m + 1) x a) = a := by
  change hurewiczInverse x hpi (hurewiczMap (m := m + 1) x
    (Additive.ofMul (Additive.toMul a))) = Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x hpi p

/-- The composite `hurewiczInverse ∘ hurewiczMap` is the identity linear map. -/
theorem hurewiczInverse_comp_hurewiczMap (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x)) :
    (hurewiczInverse x hpi).comp (hurewiczMap (m := m + 1) x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x hpi a

/-- **The Hurewicz theorem.** For a simply connected space `X` with
`Subsingleton (π_ j X x)` for `2 ≤ j < m + 3`, the Hurewicz map is a `ℤ`-linear
equivalence `Additive (π_ (m + 3) X x) ≃ₗ[ℤ] SingularHomology X (m + 3)`. -/
def hurewiczLinearEquiv (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x)) :
    Additive (π_ (m + 3) X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X (m + 3) :=
  LinearEquiv.ofLinearMap (hurewiczMap (m := m + 1) x) (hurewiczInverse x hpi)
    (hurewiczMap_comp_hurewiczInverse x hpi) (hurewiczInverse_comp_hurewiczMap x hpi)

/-- **The Hurewicz theorem.** For a simply connected space `X`, every degree `n ≥ 2`
with `Subsingleton (π_ j X x)` for `2 ≤ j < n`, the Hurewicz map is a `ℤ`-linear
equivalence `Additive (π_ n X x) ≃ₗ[ℤ] SingularHomology X n`. -/
def hurewiczLinearEquivOfTwoLE (x : X) (n : ℕ) (hn : 2 ≤ n)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    Additive (π_ n X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X n := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rcases n with _ | n'
  · exact absurd hn (by omega)
  rcases n' with _ | n''
  · exact absurd hn (by omega)
  rcases n'' with _ | m
  · exact Hurewicz.degreeTwoLinearEquiv x
  · exact hurewiczLinearEquiv x hpi

end Hurewicz

end Mathoverflow1973
