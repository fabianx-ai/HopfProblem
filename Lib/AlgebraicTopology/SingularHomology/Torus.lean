/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.AlgebraicTopology.SingularHomology.CirclePaths

/-!
# Homology of the product torus

The rank-`r` product torus `ProductTorus r = (S¹)^r` as a function space `Fin r → AddCircle 1`,
its zero- and successor-step homeomorphisms, and the recursive computation of its singular
homology via the circle Künneth splitting `circleProductHomologyEquiv`:

```
H_n((S¹)^r) ≅ ℤ^{C(r,n)}
```

The recursion is on both `r` and `n`: degree `0` uses `connectedHomologyZeroEquiv`,
rank `0` in positive degree is subsingleton (totally disconnected `PUnit`), and the
successor step splits `H_{n+1}((S¹)^{r+1})` through the product homeomorphism and the
circle splitting into `H_{n+1}((S¹)^r) ⊕ H_n((S¹)^r)`.

The binomial bookkeeping (`binomialModule`, `binomialModuleSuccEquiv`) implements Pascal's
rule `C(r+1, n+1) = C(r, n+1) + C(r, n)` on the coefficient side.

`productTorusTopClass n` is the distinguished top-degree generator, characterized by
its coordinate value `fun _ => 1` under `productTorusHomologyEquiv n n`.

## References

Hatcher, *Algebraic Topology*, §2.2 (Mayer–Vietoris, product homology).
-/

@[expose] public noncomputable section

open SingularHomology

abbrev PeriodTorusHigherHomology.ProductTorus (n : ℕ) :=
  Fin n → AddCircle (1 : ℝ)

def PeriodTorusHigherHomology.productTorusSuccHomeomorph (n : ℕ) :
    ProductTorus (n + 1) ≃ₜ AddCircle (1 : ℝ) × ProductTorus n
    where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := Fin.cons_self_tail x
  right_inv x := by simp
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

@[simp]
theorem PeriodTorusHigherHomology.productTorusSuccHomeomorph_apply (n : ℕ)
    (x : ProductTorus (n + 1)) : productTorusSuccHomeomorph n x = (x 0, fun i => x i.succ) :=
  rfl

def PeriodTorusHigherHomology.productTorusZeroHomeomorph : ProductTorus 0 ≃ₜ PUnit
    where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

abbrev PeriodTorusHigherHomology.binomialModule (r n : ℕ) :=
  Fin (r.choose n) → ℤ

def PeriodTorusHigherHomology.binomialPascalIndexEquiv (r n : ℕ) :
    Fin ((r + 1).choose (n + 1)) ≃ Fin (r.choose (n + 1)) ⊕ Fin (r.choose n) :=
  (finCongr ((Nat.choose_succ_succ' r n).trans (Nat.add_comm _ _))).trans finSumFinEquiv.symm

def PeriodTorusHigherHomology.binomialModuleSuccEquiv (r n : ℕ) :
    binomialModule (r + 1) (n + 1) ≃ₗ[ℤ] binomialModule r (n + 1) × binomialModule r n :=
  (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (binomialPascalIndexEquiv r n)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ ℤ)

@[simp]
theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_apply_fst (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose (n + 1))) :
    (binomialModuleSuccEquiv r n x).1 i = x ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_apply_snd (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose n)) :
    (binomialModuleSuccEquiv r n x).2 i = x ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) :=
  rfl

def PeriodTorusHigherHomology.integerBinomialZeroEquiv (r : ℕ) : ℤ ≃ₗ[ℤ] binomialModule r 0 :=
  (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (finCongr (Nat.choose_zero_right r)).symm)

@[simp]
theorem PeriodTorusHigherHomology.binomialModule_finrank (r n : ℕ) :
    Module.finrank ℤ (binomialModule r n) = r.choose n :=
  Module.finrank_fin_fun ℤ

theorem PeriodTorusHigherHomology.binomialModule_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (binomialModule r n) := by
  change Subsingleton (Fin (r.choose n) → ℤ)
  rw [Nat.choose_eq_zero_of_lt h]
  infer_instance

instance PeriodTorusHigherHomology.binomialModule_zero_succ_subsingleton (n : ℕ) :
    Subsingleton (binomialModule 0 (n + 1)) :=
  binomialModule_subsingleton_of_lt (Nat.zero_lt_succ n)

theorem PeriodTorusHigherHomology.binomialModule_eq_zero_of_lt {r n : ℕ} (h : r < n)
    (x : binomialModule r n) : x = 0 :=
  @Subsingleton.elim (binomialModule r n) (binomialModule_subsingleton_of_lt h) x 0

def PeriodTorusHigherHomology.binomialCoordinateBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (binomialModule r n) :=
  Pi.basisFun ℤ (Fin (r.choose n))

@[simp]
theorem PeriodTorusHigherHomology.binomialCoordinateBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    binomialCoordinateBasis r n i = Pi.single i 1 :=
  Pi.basisFun_apply ℤ (Fin (r.choose n)) i

@[simp]
theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_single_inl (r n : ℕ)
    (i : Fin (r.choose (n + 1))) :
    binomialModuleSuccEquiv r n (Pi.single ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) 1) =
      (Pi.single i 1, 0) := by
  apply Prod.ext
  · funext j
    simp only [binomialModuleSuccEquiv_apply_fst, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq]
  · funext j
    simp only [binomialModuleSuccEquiv_apply_snd, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inr_ne_inl, if_false, Pi.zero_apply]

@[simp]
theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_single_inr (r n : ℕ)
    (i : Fin (r.choose n)) :
    binomialModuleSuccEquiv r n (Pi.single ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) 1) =
      (0, Pi.single i 1) := by
  apply Prod.ext
  · funext j
    simp only [binomialModuleSuccEquiv_apply_fst, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inl_ne_inr, if_false, Pi.zero_apply]
  · funext j
    simp only [binomialModuleSuccEquiv_apply_snd, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inr.injEq]

theorem PeriodTorusHigherHomology.integerBinomialZeroEquiv_one_single (r : ℕ)
    (i : Fin (r.choose 0)) : integerBinomialZeroEquiv r 1 = Pi.single i 1 := by
  have hsingle : Subsingleton (Fin (r.choose 0)) := by
    rw [Nat.choose_zero_right]
    infer_instance
  funext j
  have hij : i = j := hsingle.elim i j
  subst j
  simp [integerBinomialZeroEquiv]

theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_top (n : ℕ) :
    binomialModuleSuccEquiv n n (fun _ => 1) = (0, fun _ => 1) := by
  apply Prod.ext
  · exact binomialModule_eq_zero_of_lt (Nat.lt_succ_self n) _
  · rfl

def PeriodTorusHigherHomology.productTorusHomologyEquiv :
    (r n : ℕ) → SingularMayerVietoris.SingularHomology (ProductTorus r) n ≃ₗ[ℤ] binomialModule r n
  | r, 0 => (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r)
  | 0, n + 1 =>
    by
    letI := totallyDisconnected_homology_subsingleton PUnit (n + 1) (Nat.succ_ne_zero n)
    exact
      (homeomorphHomologyEquiv productTorusZeroHomeomorph (n + 1)).trans
        (LinearEquiv.ofSubsingleton (SingularMayerVietoris.SingularHomology PUnit (n + 1))
          (binomialModule 0 (n + 1)))
  | r + 1, n + 1 =>
    ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
        ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                (productTorusHomologyEquiv r n).toAddEquiv).trans
            (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv

@[simp]
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_zero (r : ℕ) :
    productTorusHomologyEquiv r 0 =
      (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r) := by
  cases r <;> rfl

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ (r n : ℕ) :
    productTorusHomologyEquiv (r + 1) (n + 1) =
      ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
          ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
            (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                  (productTorusHomologyEquiv r n).toAddEquiv).trans
              (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv :=
  rfl

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_apply (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      (productTorusHomologyEquiv r (n + 1)
          (circleProjectionHomology (ProductTorus r) (n + 1)
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)),
        productTorusHomologyEquiv r n
          (circleBoundary (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a))) := by
  rw [productTorusHomologyEquiv_succ]
  change
    binomialModuleSuccEquiv r n
        ((binomialModuleSuccEquiv r n).symm
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
              (productTorusHomologyEquiv r n).toAddEquiv)
            (circleProductHomologyEquiv (ProductTorus r) n
              (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)))) =
      _
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_apply]
  rfl

theorem PeriodTorusHigherHomology.productTorus_homology_free (r n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  Module.Free.of_equiv (productTorusHomologyEquiv r n).symm

theorem PeriodTorusHigherHomology.productTorus_homology_finite (r n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  Module.Finite.of_surjective (productTorusHomologyEquiv r n).symm.toLinearMap
    (productTorusHomologyEquiv r n).symm.surjective

theorem PeriodTorusHigherHomology.productTorus_homology_finrank (r n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) = r.choose n := by
  rw [(productTorusHomologyEquiv r n).finrank_eq]
  exact binomialModule_finrank r n

theorem PeriodTorusHigherHomology.productTorus_homology_torsionFree (r n : ℕ) :
    Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) := by
  let := productTorus_homology_free r n
  infer_instance

theorem PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (ProductTorus r) n) := by
  let := binomialModule_subsingleton_of_lt h
  exact (productTorusHomologyEquiv r n).injective.subsingleton

def PeriodTorusHigherHomology.productTorusTopClass (n : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus n) n :=
  (productTorusHomologyEquiv n n).symm (fun _ => (1 : ℤ))

@[simp]
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_topClass (n : ℕ) :
    productTorusHomologyEquiv n n (productTorusTopClass n) = fun _ => (1 : ℤ) :=
  (productTorusHomologyEquiv n n).apply_symm_apply _

@[simp]
theorem PeriodTorusHigherHomology.productTorusTopClass_zero :
    productTorusTopClass 0 = pointClass (0 : ProductTorus 0) := by
  apply (productTorusHomologyEquiv 0 0).injective
  rw [productTorusHomologyEquiv_topClass, productTorusHomologyEquiv_zero]
  simp only [LinearEquiv.trans_apply, connectedHomologyZeroEquiv_pointClass]
  rfl

theorem PeriodTorusHigherHomology.productTorusTopClass_succ_coordinates (n : ℕ) :
    circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) =
      (0, productTorusTopClass n) := by
  apply Prod.ext
  · exact
      @Subsingleton.elim (SingularMayerVietoris.SingularHomology (ProductTorus n) (n + 1))
        (productTorus_homology_subsingleton_of_lt (Nat.lt_succ_self n)) _ _
  · apply (productTorusHomologyEquiv n n).injective
    have h :=
      congrArg Prod.snd (productTorusHomologyEquiv_succ_apply n n (productTorusTopClass (n + 1)))
    rw [productTorusHomologyEquiv_topClass, binomialModuleSuccEquiv_top] at h
    exact h.symm.trans (productTorusHomologyEquiv_topClass n).symm

@[simp]
theorem PeriodTorusHigherHomology.productTorusTopClass_succ_boundary (n : ℕ) :
    circleBoundary (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) =
      productTorusTopClass n :=
  congrArg Prod.snd (productTorusTopClass_succ_coordinates n)

def PeriodTorusHigherHomology.torusMatrixLinearMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ProductTorus n →ₗ[ℤ] ProductTorus m
    where
  toFun x i := ∑ j, A i j • x j
  map_add' x
    y := by
    ext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r
    x := by
    ext i
    change (∑ j, A i j • (r • x j)) = r • ∑ j, A i j • x j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact SMulCommClass.smul_comm (A i j) r (x j)

theorem PeriodTorusHigherHomology.torusMatrixLinearMap_continuous {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) : Continuous (torusMatrixLinearMap A) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ProductTorus n => ∑ j, A i j • x j)
  exact continuous_finsetSum Finset.univ (fun j _ => (continuous_apply j).zsmul (A i j))

def PeriodTorusHigherHomology.torusMatrixMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    C(ProductTorus n, ProductTorus m) :=
  ⟨torusMatrixLinearMap A, torusMatrixLinearMap_continuous A⟩

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x : ProductTorus n) (i : Fin m) : torusMatrixMap A x i = ∑ j, A i j • x j :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_one (n : ℕ) :
    torusMatrixMap (1 : Matrix (Fin n) (Fin n) ℤ) = ContinuousMap.id (ProductTorus n) := by
  apply ContinuousMap.ext
  intro x
  ext i
  simp [torusMatrixMap_apply, Matrix.one_apply]

theorem PeriodTorusHigherHomology.torusMatrixMap_mul {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin r) ℤ) :
    torusMatrixMap (A * B) = (torusMatrixMap A).comp (torusMatrixMap B) := by
  apply ContinuousMap.ext
  intro x
  ext i
  change (∑ j, (A * B) i j • x j) = ∑ k, A i k • ∑ j, B k j • x j
  simp only [Matrix.mul_apply, Finset.sum_smul, SemigroupAction.mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

def PeriodTorusHigherHomology.coordinateCircleMap {n : ℕ} (v : Fin n → ℤ) :
    C((CircleTopology.Circle), ProductTorus n)
    where
  toFun z i := v i • z
  continuous_toFun := continuous_pi fun i => continuous_id.zsmul (v i)

@[simp]
theorem PeriodTorusHigherHomology.coordinateCircleMap_apply {n : ℕ} (v : Fin n → ℤ)
    (z : (CircleTopology.Circle)) (i : Fin n) :
    coordinateCircleMap v z i = v i • z :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.coordinateCircleMap_zero {n : ℕ} (v : Fin n → ℤ) :
    coordinateCircleMap v 0 = 0 := by
  ext i
  exact smul_zero (v i)

theorem PeriodTorusHigherHomology.coordinateCircleMap_add {n : ℕ} (v : Fin n → ℤ)
    (x y : (CircleTopology.Circle)) :
    coordinateCircleMap v (x + y) = coordinateCircleMap v x + coordinateCircleMap v y := by
  ext i
  exact smul_add (v i) x y

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    torusMatrixMap A 0 = 0 :=
  (torusMatrixLinearMap A).map_zero

def PeriodTorusHigherHomology.torusHeadCircleMap (n : ℕ) :
    C((CircleTopology.Circle), ProductTorus (n + 1)) :=
  coordinateCircleMap (Pi.single (0 : Fin (n + 1)) 1)

@[simp]
theorem PeriodTorusHigherHomology.torusHeadCircleMap_apply (n : ℕ)
    (z : (CircleTopology.Circle)) :
    torusHeadCircleMap n z = Fin.cons z 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]

theorem PeriodTorusHigherHomology.productTorusTopClass_succ_cross (n : ℕ) :
    productTorusTopClass (n + 1) =
      SingularMayerVietoris.singularHomologyMap ((productTorusSuccHomeomorph n).symm : C(_, _))
        (n + 1) (positiveCircleCross (ProductTorus n) n (productTorusTopClass n)) := by
  apply (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).injective
  apply (circleProductHomologyEquiv (ProductTorus n) n).injective
  rw [productTorusTopClass_succ_coordinates]
  change
    (0, productTorusTopClass n) =
      circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          ((homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).symm
            (positiveCircleCross (ProductTorus n) n (productTorusTopClass n))))
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_positiveCircleCross]

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_zero_source {r : ℕ}
    (A : Matrix (Fin r) (Fin 0) ℤ) : torusMatrixMap A = ContinuousMap.const (ProductTorus 0) 0 := by
  apply ContinuousMap.ext
  intro x
  funext i
  simp

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x y : ProductTorus n) : torusMatrixMap A (x + y) = torusMatrixMap A x + torusMatrixMap A y :=
  (torusMatrixLinearMap A).map_add x y
