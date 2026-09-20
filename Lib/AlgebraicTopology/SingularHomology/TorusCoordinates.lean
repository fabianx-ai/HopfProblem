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

The declarations keep the `PeriodTorusHigherHomology` namespace of the source; the only
changes are qualifier retargets to the `Lib` spellings (`SingularHomology.*`, `SingularChains.*`).

## Tags

torus, singular homology, coordinate basis, right translation
-/

open Set Function Filter Manifold Topology

noncomputable section

open SingularHomology

def PeriodTorusHigherHomology.coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ ProductTorus n
    where
  toFun x i := (x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; exact AddCircle.coe_add (1 : ℝ) (x i) (y i)

@[simp]
theorem PeriodTorusHigherHomology.coordinateProjection_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateProjection n x i = (x i : AddCircle (1 : ℝ)) :=
  rfl

theorem PeriodTorusHigherHomology.coordinateProjection_continuous (n : ℕ) :
    Continuous (coordinateProjection n) := by
  exact continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))

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

theorem PeriodTorusHigherHomology.coordinateProjection_surjective (n : ℕ) :
    Function.Surjective (coordinateProjection n) := by
  intro t
  have h : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = t i := by
    intro i
    exact QuotientAddGroup.mk_surjective (t i)
  choose x hx using h
  exact ⟨x, funext hx⟩

def PeriodTorusHigherHomology.coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    Path (0 : ProductTorus n) 0 :=
  ((Path.segment (0 : Fin n → ℝ) (fun i => (v i : ℝ))).map
        (coordinateProjection_continuous n)).cast
    (map_zero (coordinateProjection n)).symm
    ((coordinateProjection_eq_zero_iff n _).mpr ⟨v, rfl⟩).symm

@[simp]
theorem PeriodTorusHigherHomology.coordinatePeriodLoop_apply (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) (i : Fin n) :
    coordinatePeriodLoop n v t i = ((t : ℝ) * (v i : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [coordinatePeriodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add,
    coordinateProjection_apply, Pi.smul_apply, smul_eq_mul]

def PeriodTorusHigherHomology.rightTranslation {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (a : G) : C(G, G) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

@[simp]
theorem PeriodTorusHigherHomology.rightTranslation_apply {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] (a x : G) : rightTranslation a x = x + a :=
  rfl

def PeriodTorusHigherHomology.rightTranslationHomotopyAlong {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a) :
    (ContinuousMap.id G).Homotopy (rightTranslation a)
    where
  toFun z := z.2 + p z.1
  continuous_toFun := continuous_snd.add (p.continuous.comp continuous_fst)
  map_zero_left x := by simp
  map_one_left x := by simp

theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap_of_path {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_homologyMap (rightTranslationHomotopyAlong p) n, singularHomologyMap_id]

@[simp]
theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] (a : G)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (PathConnectedSpace.somePath 0 a) n

theorem PeriodTorusHigherHomology.coordinatePeriodLoop_eq_projection (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinatePeriodLoop n v t = coordinateProjection n ((t : ℝ) • (fun i => (v i : ℝ))) := by
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

def PeriodTorusHigherHomology.torusTailMap (n : ℕ) : C(ProductTorus n, ProductTorus (n + 1)) :=
  ((productTorusSuccHomeomorph n).symm : C(_, _)).comp
    (CircleTopology.productSection (ProductTorus n))

@[simp]
theorem PeriodTorusHigherHomology.torusTailMap_apply (n : ℕ) (x : ProductTorus n) :
    torusTailMap n x = Fin.cons 0 x :=
  rfl

theorem PeriodTorusHigherHomology.torusTailMap_add (n : ℕ) (x y : ProductTorus n) :
    torusTailMap n (x + y) = torusTailMap n x + torusTailMap n y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

@[simp]
theorem PeriodTorusHigherHomology.torusTailMap_zero (n : ℕ) : torusTailMap n 0 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

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

theorem PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology (n : ℕ) (v : Fin n → ℤ) :
    SingularMayerVietoris.singularHomologyMap (torusTailMap n) 1
        (SingularChains.loopHomologyClass (coordinatePeriodLoop n v)) =
      SingularChains.loopHomologyClass (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)) := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    SingularChains.inducedHomology_loopHomologyClass, torusTailMap_coordinatePeriodLoop]
  rfl

def PeriodTorusHigherHomology.omitHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin n) ℤ :=
  Fin.cons 0 A

def PeriodTorusHigherHomology.takeHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i))

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

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_degree_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusMap r 0 i = ContinuousMap.const _ 0 := by cases r <;> rfl

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_omit_apply (r n : ℕ)
    (j : Fin (r.choose (n + 1))) (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x =
      Fin.cons 0 (coordinateTorusMap r (n + 1) j x) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_take_apply (r n : ℕ) (j : Fin (r.choose n))
    (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x =
      Fin.cons (x 0) (coordinateTorusMap r n j (fun k => x k.succ)) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

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

def PeriodTorusHigherHomology.coordinateTorusMatrix :
    (r n : ℕ) → Fin (r.choose n) → Matrix (Fin r) (Fin n) ℤ
  | 0, 0, _ => 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j => omitHeadMatrix (coordinateTorusMatrix r (n + 1) j)
    | Sum.inr j => takeHeadMatrix (coordinateTorusMatrix r n j)

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMatrix_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) =
      omitHeadMatrix (coordinateTorusMatrix r (n + 1) j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMatrix_take (r n : ℕ) (j : Fin (r.choose n)) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) =
      takeHeadMatrix (coordinateTorusMatrix r n j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

def PeriodTorusHigherHomology.coordinateTorusClass (r n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n (productTorusTopClass n)

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusClass_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusClass r 0 i = pointClass (0 : ProductTorus r) := by
  rw [coordinateTorusClass, productTorusTopClass_zero, singularHomologyMap_pointClass,
    coordinateTorusMap_degree_zero]
  rfl

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

theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))) =
      (coordinateTorusClass r (n + 1) j, 0) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_omit, circleProductHomologyEquiv_section]

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

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_pair (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      ((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
          (productTorusHomologyEquiv r n).toAddEquiv)
        (circleProductHomologyEquiv (ProductTorus r) n
          (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)) :=
  productTorusHomologyEquiv_succ_apply r n a

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

def PeriodTorusHigherHomology.coordinateTorusBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ
      (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  (binomialCoordinateBasis r n).map (productTorusHomologyEquiv r n).symm

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasis r n i = coordinateTorusClass r n i := by
  apply (productTorusHomologyEquiv r n).injective
  rw [coordinateTorusBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    binomialCoordinateBasis_apply, productTorusHomologyEquiv_coordinateTorusClass]

def PeriodTorusHigherHomology.coordinateTorusMapAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) : C(ProductTorus n, X) :=
  (e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)

def PeriodTorusHigherHomology.coordinateTorusClassAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMapAlong e n i) n
    (productTorusTopClass n)

def PeriodTorusHigherHomology.coordinateTorusBasisAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularMayerVietoris.SingularHomology X n) :=
  (coordinateTorusBasis r n).map (homeomorphHomologyEquiv e n).symm

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

theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_coe {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    ⇑(coordinateTorusBasisAlong e n) = coordinateTorusClassAlong e n :=
  funext (coordinateTorusBasisAlong_apply e n)

theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_span {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClassAlong e n)) = ⊤ := by
  simpa only [coordinateTorusBasisAlong_coe] using (coordinateTorusBasisAlong e n).span_eq

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

theorem PeriodTorusHigherHomology.homeomorph_symm_add_of_add {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Add X] [Add Y] (e : X ≃ₜ Y) (he : ∀ x y, e (x + y) = e x + e y)
    (x y : Y) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

def PeriodTorusHigherHomology.coordinateH1Add (n : ℕ) :
    (Fin n → ℤ) →+ SingularChains.SingularH1 (ProductTorus n)
    where
  toFun v := ∑ i, v i • SingularChains.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))
  map_zero' := by simp only [Pi.zero_apply, zero_zsmul, Finset.sum_const_zero]
  map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

def PeriodTorusHigherHomology.coordinateH1 (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] SingularChains.SingularH1 (ProductTorus n) :=
  { toFun := coordinateH1Add n
    map_add' := (coordinateH1Add n).map_add
    map_smul' r
      a := by
      convert! (coordinateH1Add n).map_zsmul r a using 1
      exact int_smul_eq_zsmul .. }

@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_basis (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.basisFun ℤ (Fin n) i) =
      SingularChains.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simp [coordinateH1, coordinateH1Add, Pi.basisFun_apply, Pi.single_apply]

@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_single (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.single i 1) =
      SingularChains.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simpa only [Pi.basisFun_apply] using coordinateH1_basis n i

theorem PeriodTorusHigherHomology.positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv
        (Homeomorph.prodUnique (SingularHomology.CircleTopology.Circle) Unit).symm 1
        (SingularChains.loopHomologyClass CirclePaths.positiveLoop) :=
  crossProductHomology_pointClass_right (SingularHomology.CircleTopology.Circle) Unit
    (SingularChains.loopHomologyClass CirclePaths.positiveLoop) ()

end
