/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.Torus
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.AlgebraicTopology.SingularHomology.CirclePaths

/-!
# Coordinate classes on the product torus

The coordinate projection `(Fin n → ℝ) → ProductTorus n`, the coordinate period loops it induces,
the tail map `ProductTorus n → ProductTorus (n + 1)`, and the coordinate torus maps
`ProductTorus n → ProductTorus r` indexed by `Fin (r.choose n)` whose top classes form a basis of
`H_n(ProductTorus r)` (`coordinateTorusBasis`), transported along any homeomorphism with a torus
(`coordinateTorusBasisAlong`). Also the right translations of a topological group, which act
trivially on singular homology once the group is path connected, and the degree-one coordinate
map `coordinateH1`.

## References

Hatcher, *Algebraic Topology*, §3.B: the basis of `H_n(T^r)` given by the coordinate
sub-tori.

## Tags

torus, singular homology, coordinate basis, right translation
-/

open Set Function Filter Manifold Topology

noncomputable section

open SingularHomology

/-- The universal covering projection `ℝⁿ → (ℝ/ℤ)ⁿ = (S¹)^n`, as a group homomorphism. -/
def PeriodTorusHigherHomology.coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ ProductTorus n
    where
  toFun x i := (x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; exact AddCircle.coe_add (1 : ℝ) (x i) (y i)

/-- The covering projection acts coordinatewise by `ℝ → ℝ/ℤ`. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateProjection_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateProjection n x i = (x i : AddCircle (1 : ℝ)) :=
  rfl

/-- The covering projection `ℝⁿ → (S¹)^n` is continuous. -/
theorem PeriodTorusHigherHomology.coordinateProjection_continuous (n : ℕ) :
    Continuous (coordinateProjection n) := by
  exact continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))

/-- The kernel of `ℝⁿ → (S¹)^n` is the integer lattice `ℤⁿ`. -/
theorem PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff (n : ℕ) (x : Fin n → ℝ) :
    coordinateProjection n x = 0 ↔ ∃ v : Fin n → ℤ, x = fun i => (v i : ℝ) := by
  constructor
  · intro h
    have hi : ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
      intro i
      have hz := congrFun h i
      change (x i : AddCircle (1 : ℝ)) = 0 at hz
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    choose v hv using hi
    exact ⟨v, funext fun i => (hv i).symm⟩
  · rintro ⟨v, rfl⟩
    ext i
    change ((v i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨v i, by simp⟩

/-- The covering projection `ℝⁿ → (S¹)^n` is surjective. -/
theorem PeriodTorusHigherHomology.coordinateProjection_surjective (n : ℕ) :
    Function.Surjective (coordinateProjection n) := by
  intro t
  have h : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = t i := by
    intro i
    exact QuotientAddGroup.mk_surjective (t i)
  choose x hx using h
  exact ⟨x, funext hx⟩

/-- The loop at the origin of `(S¹)^n` obtained by projecting the straight segment from `0`
to an integer vector `v`; its class in `H₁` is the lattice element `v`. -/
def PeriodTorusHigherHomology.coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    Path (0 : ProductTorus n) 0 :=
  ((Path.segment (0 : Fin n → ℝ) (fun i => (v i : ℝ))).map
        (coordinateProjection_continuous n)).cast
    (map_zero (coordinateProjection n)).symm
    ((coordinateProjection_eq_zero_iff n _).mpr ⟨v, rfl⟩).symm

/-- The period loop of `v` traverses `t ↦ (t·vᵢ mod 1)` in each coordinate. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinatePeriodLoop_apply (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) (i : Fin n) :
    coordinatePeriodLoop n v t i = ((t : ℝ) * (v i : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [coordinatePeriodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add,
    coordinateProjection_apply, Pi.smul_apply, smul_eq_mul]

/-- Right translation `x ↦ x + a` on a topological group, as a continuous map. -/
def PeriodTorusHigherHomology.rightTranslation {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (a : G) : C(G, G) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

/-- Right translation by `a` sends `x` to `x + a`. -/
@[simp]
theorem PeriodTorusHigherHomology.rightTranslation_apply {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] (a x : G) : rightTranslation a x = x + a :=
  rfl

/-- A path from `0` to `a` in a topological group gives a homotopy from the identity to
right translation by `a`. -/
def PeriodTorusHigherHomology.rightTranslationHomotopyAlong {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a) :
    (ContinuousMap.id G).Homotopy (rightTranslation a)
    where
  toFun z := z.2 + p z.1
  continuous_toFun := continuous_snd.add (p.continuous.comp continuous_fst)
  map_zero_left x := by simp
  map_one_left x := by simp

/-- If `0` and `a` are joined by a path, right translation by `a` induces the identity on
singular homology. -/
theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap_of_path {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_homologyMap (rightTranslationHomotopyAlong p) n, singularHomologyMap_id]

/-- On a path-connected topological group, every right translation induces the identity on
singular homology. -/
@[simp]
theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] (a : G)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (PathConnectedSpace.somePath 0 a) n

/-- The period loop of `v` is the projection of the linear path `t ↦ t • v` in `ℝⁿ`. -/
theorem PeriodTorusHigherHomology.coordinatePeriodLoop_eq_projection (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinatePeriodLoop n v t = coordinateProjection n ((t : ℝ) • (fun i => (v i : ℝ))) := by
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

/-- The inclusion `(S¹)^n → (S¹)^{n+1}`, `x ↦ (0, x)`, as the last `n` coordinates. -/
def PeriodTorusHigherHomology.torusTailMap (n : ℕ) : C(ProductTorus n, ProductTorus (n + 1)) :=
  ((productTorusSuccHomeomorph n).symm : C(_, _)).comp
    (CircleTopology.productSection (ProductTorus n))

/-- The tail inclusion sends `x` to `(0, x)`. -/
@[simp]
theorem PeriodTorusHigherHomology.torusTailMap_apply (n : ℕ) (x : ProductTorus n) :
    torusTailMap n x = Fin.cons 0 x :=
  rfl

/-- The tail inclusion is additive. -/
theorem PeriodTorusHigherHomology.torusTailMap_add (n : ℕ) (x y : ProductTorus n) :
    torusTailMap n (x + y) = torusTailMap n x + torusTailMap n y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

/-- The tail inclusion sends the origin to the origin. -/
@[simp]
theorem PeriodTorusHigherHomology.torusTailMap_zero (n : ℕ) : torusTailMap n 0 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

/-- The tail inclusion carries the period loop of `v` to the period loop of `(0, v)`. -/
theorem PeriodTorusHigherHomology.torusTailMap_coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusTailMap n).continuous =
      (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)).cast (torusTailMap_zero n)
        (torusTailMap_zero n) := by
  apply Path.ext
  funext t
  apply funext
  intro i
  change
    torusTailMap n (coordinatePeriodLoop n v t) i =
      coordinatePeriodLoop (n + 1) (Fin.cons 0 v) t i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]

/-- On `H₁`, the tail inclusion carries the class of the period loop of `v` to the class of
the period loop of `(0, v)`. -/
theorem PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology (n : ℕ) (v : Fin n → ℤ) :
    SingularMayerVietoris.singularHomologyMap (torusTailMap n) 1
        (SingularChains.loopHomologyClass (coordinatePeriodLoop n v)) =
      SingularChains.loopHomologyClass (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)) := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    SingularChains.inducedHomology_loopHomologyClass, torusTailMap_coordinatePeriodLoop]
  rfl

/-- Add a zero first row to a matrix: the coordinate sub-torus that omits the first
circle factor of the target. -/
def PeriodTorusHigherHomology.omitHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin n) ℤ :=
  Fin.cons 0 A

/-- Add a first row and first column mapping the new source circle isomorphically onto the
new target circle: the coordinate sub-torus that uses the first circle factor. -/
def PeriodTorusHigherHomology.takeHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i))

/-- For each `n`-element subset of the `r` circle factors, indexed by `Fin (C(r,n))`, the
inclusion `(S¹)^n → (S¹)^r` of the corresponding coordinate sub-torus, defined by recursion
through Pascal's rule (Hatcher, *Algebraic Topology*, §3.B: the basis of `H_n(T^r)` by
coordinate sub-tori). -/
def PeriodTorusHigherHomology.coordinateTorusMap :
    (r n : ℕ) → Fin (r.choose n) → C(ProductTorus n, ProductTorus r)
  | 0, 0, _ => ContinuousMap.const _ 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => ContinuousMap.const _ 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j =>
      ((productTorusSuccHomeomorph r).symm :
            C((SingularHomology.CircleTopology.Circle) × ProductTorus r,
              ProductTorus (r + 1))).comp
        ((CircleTopology.productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j))
    | Sum.inr j =>
      ((productTorusSuccHomeomorph r).symm :
            C((SingularHomology.CircleTopology.Circle) × ProductTorus r,
              ProductTorus (r + 1))).comp
        ((circleProductMap (coordinateTorusMap r n j)).comp
          (productTorusSuccHomeomorph n :
            C(ProductTorus (n + 1),
              (SingularHomology.CircleTopology.Circle) × ProductTorus n)))

/-- The unique coordinate sub-torus of dimension `0` is the origin. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_degree_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusMap r 0 i = ContinuousMap.const _ 0 := by cases r <;> rfl

/-- On a left-indexed (first factor omitted) coordinate sub-torus, the inclusion is the
lower-rank one preceded by `0` in the first coordinate. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_omit_apply (r n : ℕ)
    (j : Fin (r.choose (n + 1))) (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x =
      Fin.cons 0 (coordinateTorusMap r (n + 1) j x) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

/-- On a right-indexed (first factor used) coordinate sub-torus, the inclusion keeps the
first coordinate and applies the lower-rank inclusion to the tail. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_take_apply (r n : ℕ) (j : Fin (r.choose n))
    (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x =
      Fin.cons (x 0) (coordinateTorusMap r n j (fun k => x k.succ)) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

/-- The left-indexed coordinate inclusion, read through the splitting `(S¹)^{r+1} ≃ S¹ ×
(S¹)^r`, is the zero section of the first circle composed with the lower-rank inclusion. -/
theorem PeriodTorusHigherHomology.coordinateTorusMap_omit (r n : ℕ) (j : Fin (r.choose (n + 1))) :
    (productTorusSuccHomeomorph r :
            C(ProductTorus (r + 1),
              (SingularHomology.CircleTopology.Circle) × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j))) =
      (CircleTopology.productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j) := by
  apply ContinuousMap.ext
  intro x
  change
    productTorusSuccHomeomorph r
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x) =
      _
  rw [coordinateTorusMap_omit_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- The right-indexed coordinate inclusion, read through the splittings of source and
target, is the identity on the first circle times the lower-rank inclusion. -/
theorem PeriodTorusHigherHomology.coordinateTorusMap_take (r n : ℕ) (j : Fin (r.choose n)) :
    (productTorusSuccHomeomorph r :
            C(ProductTorus (r + 1),
              (SingularHomology.CircleTopology.Circle) × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j))) =
      (circleProductMap (coordinateTorusMap r n j)).comp
        (productTorusSuccHomeomorph n :
          C(ProductTorus (n + 1),
            (SingularHomology.CircleTopology.Circle) × ProductTorus n)) := by
  apply ContinuousMap.ext
  intro x
  change
    productTorusSuccHomeomorph r
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x) =
      _
  rw [coordinateTorusMap_take_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- The integer matrix of the coordinate sub-torus inclusion `(S¹)^n → (S¹)^r` indexed by
`i : Fin (C(r,n))`: the `0`/`1` matrix of the corresponding `n`-element subset. -/
def PeriodTorusHigherHomology.coordinateTorusMatrix :
    (r n : ℕ) → Fin (r.choose n) → Matrix (Fin r) (Fin n) ℤ
  | 0, 0, _ => 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j => omitHeadMatrix (coordinateTorusMatrix r (n + 1) j)
    | Sum.inr j => takeHeadMatrix (coordinateTorusMatrix r n j)

/-- The matrix of a left-indexed coordinate sub-torus adds a zero first row. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMatrix_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) =
      omitHeadMatrix (coordinateTorusMatrix r (n + 1) j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

/-- The matrix of a right-indexed coordinate sub-torus adds a new first row and column. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMatrix_take (r n : ℕ) (j : Fin (r.choose n)) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) =
      takeHeadMatrix (coordinateTorusMatrix r n j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

/-- The homology class in `H_n((S¹)^r)` of the `i`-th coordinate sub-torus: the pushforward
of the top class of `(S¹)^n`. -/
def PeriodTorusHigherHomology.coordinateTorusClass (r n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n (productTorusTopClass n)

/-- In degree `0` the coordinate class is the class of the origin. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusClass_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusClass r 0 i = pointClass (0 : ProductTorus r) := by
  rw [coordinateTorusClass, productTorusTopClass_zero, singularHomologyMap_pointClass,
    coordinateTorusMap_degree_zero]
  rfl

/-- Compatibility of a left-indexed coordinate inclusion with the circle splitting on
homology: it becomes the circle zero-section map. -/
theorem PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1)))
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))
          (n + 1) a) =
      circleSectionHomology (ProductTorus r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r (n + 1) j) (n + 1) a) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (productTorusSuccHomeomorph r :
                C(ProductTorus (r + 1),
                  (SingularHomology.CircleTopology.Circle) × ProductTorus r))
              (n + 1)).comp
          (SingularMayerVietoris.singularHomologyMap
            (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))
            (n + 1)))
        a =
      _
  rw [← singularHomologyMap_comp, coordinateTorusMap_omit, singularHomologyMap_comp]
  rfl

/-- Compatibility of a right-indexed coordinate inclusion with the circle splitting on
homology: it becomes the identity on the circle times the lower-rank inclusion. -/
theorem PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_take (r n : ℕ)
    (j : Fin (r.choose n))
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))
          (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap (circleProductMap (coordinateTorusMap r n j))
        (n + 1) (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1) a) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (productTorusSuccHomeomorph r :
                C(ProductTorus (r + 1),
                  (SingularHomology.CircleTopology.Circle) × ProductTorus r))
              (n + 1)).comp
          (SingularMayerVietoris.singularHomologyMap
            (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))
            (n + 1)))
        a =
      _
  rw [← singularHomologyMap_comp, coordinateTorusMap_take, singularHomologyMap_comp]
  rfl

/-- Under the circle Künneth splitting, a left-indexed coordinate class has components
`(lower-rank coordinate class, 0)`. -/
theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))) =
      (coordinateTorusClass r (n + 1) j, 0) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_omit, circleProductHomologyEquiv_section]

/-- Under the circle Künneth splitting, a right-indexed coordinate class has components
`(0, lower-rank coordinate class)`. -/
theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_take (r n : ℕ)
    (j : Fin (r.choose n)) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))) =
      (0, coordinateTorusClass r n j) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_take, circleProductHomologyEquiv_naturality,
    productTorusTopClass_succ_coordinates, map_zero]

/-- The recursive step of the torus homology isomorphism, written as a pair of components
through the circle splitting. -/
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_pair (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      ((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
          (productTorusHomologyEquiv r n).toAddEquiv)
        (circleProductHomologyEquiv (ProductTorus r) n
          (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)) :=
  productTorusHomologyEquiv_succ_apply r n a

/-- In degree `0` the coordinate class has coordinate vector `Pi.single i 1`. -/
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass_zero (r : ℕ)
    (i : Fin (r.choose 0)) :
    productTorusHomologyEquiv r 0 (coordinateTorusClass r 0 i) = Pi.single i 1 := by
  rw [coordinateTorusClass_zero, productTorusHomologyEquiv_zero]
  change
    integerBinomialZeroEquiv r
        (connectedHomologyZeroEquiv (ProductTorus r) (pointClass (0 : ProductTorus r))) =
      _
  rw [connectedHomologyZeroEquiv_pointClass]
  exact integerBinomialZeroEquiv_one_single r i

/-- The `i`-th coordinate sub-torus class has coordinate vector `Pi.single i 1` under
`H_n((S¹)^r) ≅ ℤ^{C(r,n)}`; so the coordinate classes are the standard basis. -/
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass (r n : ℕ)
    (i : Fin (r.choose n)) :
    productTorusHomologyEquiv r n (coordinateTorusClass r n i) = Pi.single i 1 := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero 0 i
    | succ n => exact Fin.elim0 i
  | succ r ih =>
    cases n with
    | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero (r + 1) i
    | succ n =>
      obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
      cases j with
      | inl j =>
        apply (binomialModuleSuccEquiv r n).injective
        rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_omit,
          binomialModuleSuccEquiv_single_inl]
        change
          (productTorusHomologyEquiv r (n + 1) (coordinateTorusClass r (n + 1) j),
              productTorusHomologyEquiv r n 0) =
            (Pi.single j 1, 0)
        rw [ih (n + 1) j, map_zero]
      | inr j =>
        apply (binomialModuleSuccEquiv r n).injective
        rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_take,
          binomialModuleSuccEquiv_single_inr]
        change
          (productTorusHomologyEquiv r (n + 1) 0,
              productTorusHomologyEquiv r n (coordinateTorusClass r n j)) =
            (0, Pi.single j 1)
        rw [map_zero, ih n j]

/-- The basis of `H_n((S¹)^r)` indexed by `Fin (C(r,n))` (Hatcher §3.B). -/
def PeriodTorusHigherHomology.coordinateTorusBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ
      (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  (binomialCoordinateBasis r n).map (productTorusHomologyEquiv r n).symm

/-- The `i`-th basis vector of `H_n((S¹)^r)` is the `i`-th coordinate sub-torus class. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasis r n i = coordinateTorusClass r n i := by
  apply (productTorusHomologyEquiv r n).injective
  rw [coordinateTorusBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    binomialCoordinateBasis_apply, productTorusHomologyEquiv_coordinateTorusClass]

/-- The coordinate sub-torus inclusion transported along a homeomorphism `e : X ≃ₜ (S¹)^r`. -/
def PeriodTorusHigherHomology.coordinateTorusMapAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) : C(ProductTorus n, X) :=
  (e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)

/-- The coordinate sub-torus class in `H_n(X)` for a space `X` homeomorphic to `(S¹)^r`. -/
def PeriodTorusHigherHomology.coordinateTorusClassAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMapAlong e n i) n
    (productTorusTopClass n)

/-- The basis of `H_n(X)` for a space `X` homeomorphic to `(S¹)^r`. -/
def PeriodTorusHigherHomology.coordinateTorusBasisAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularMayerVietoris.SingularHomology X n) :=
  (coordinateTorusBasis r n).map (homeomorphHomologyEquiv e n).symm

/-- The transported basis vectors are the transported coordinate sub-torus classes. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_apply {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasisAlong e n i = coordinateTorusClassAlong e n i := by
  rw [coordinateTorusBasisAlong, Module.Basis.map_apply, coordinateTorusBasis_apply,
    homeomorphHomologyEquiv_symm_apply]
  change
    SingularMayerVietoris.singularHomologyMap (e.symm : C(ProductTorus r, X)) n
        (SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n
          (productTorusTopClass n)) =
      SingularMayerVietoris.singularHomologyMap
        ((e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)) n
        (productTorusTopClass n)
  rw [singularHomologyMap_comp]
  rfl

/-- The transported basis, as a function, is the transported coordinate class family. -/
theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_coe {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    ⇑(coordinateTorusBasisAlong e n) = coordinateTorusClassAlong e n :=
  funext (coordinateTorusBasisAlong_apply e n)

/-- The transported coordinate classes span `H_n(X)`. -/
theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_span {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClassAlong e n)) = ⊤ := by
  simpa only [coordinateTorusBasisAlong_coe] using (coordinateTorusBasisAlong e n).span_eq

/-- A linear map into `H_n(X)` whose range contains every transported coordinate class is
surjective. -/
theorem PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range {X : Type}
    [TopologicalSpace X] {r : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (f : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hf : ∀ i : Fin (r.choose n), coordinateTorusClassAlong e n i ∈ LinearMap.range f) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← coordinateTorusClassAlong_span e n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hf i

/-- The inverse of an additive homeomorphism is additive. -/
theorem PeriodTorusHigherHomology.homeomorph_symm_add_of_add {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Add X] [Add Y] (e : X ≃ₜ Y) (he : ∀ x y, e (x + y) = e x + e y)
    (x y : Y) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- The homomorphism `ℤⁿ → H₁((S¹)^n)` sending `v` to `∑ᵢ vᵢ · [period loop of eᵢ]`. -/
def PeriodTorusHigherHomology.coordinateH1Add (n : ℕ) :
    (Fin n → ℤ) →+ SingularChains.SingularH1 (ProductTorus n)
    where
  toFun v := ∑ i, v i • SingularChains.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))
  map_zero' := by simp only [Pi.zero_apply, zero_zsmul, Finset.sum_const_zero]
  map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

/-- The `ℤ`-linear map `ℤⁿ → H₁((S¹)^n)` sending the standard basis to the classes of the
coordinate period loops; it is the degree-one case of `coordinateTorusBasis`. -/
def PeriodTorusHigherHomology.coordinateH1 (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] SingularChains.SingularH1 (ProductTorus n) :=
  { toFun := coordinateH1Add n
    map_add' := (coordinateH1Add n).map_add
    map_smul' r
      a := by
      convert! (coordinateH1Add n).map_zsmul r a using 1
      exact int_smul_eq_zsmul .. }

/-- `coordinateH1` sends the `i`-th standard basis vector to the class of the `i`-th
coordinate period loop. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_basis (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.basisFun ℤ (Fin n) i) =
      SingularChains.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simp [coordinateH1, coordinateH1Add, Pi.basisFun_apply, Pi.single_apply]

/-- `coordinateH1` sends `Pi.single i 1` to the class of the `i`-th coordinate period
loop. -/
@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_single (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.single i 1) =
      SingularChains.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simpa only [Pi.basisFun_apply] using coordinateH1_basis n i

/-- The cross product of the circle generator with the class of a point is the circle
generator, transported along `S¹ × Unit ≃ₜ S¹`. -/
theorem PeriodTorusHigherHomology.positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv
        (Homeomorph.prodUnique (SingularHomology.CircleTopology.Circle) Unit).symm 1
        (SingularChains.loopHomologyClass CirclePaths.positiveLoop) :=
  crossProductHomology_pointClass_right (SingularHomology.CircleTopology.Circle) Unit
    (SingularChains.loopHomologyClass CirclePaths.positiveLoop) ()

end
