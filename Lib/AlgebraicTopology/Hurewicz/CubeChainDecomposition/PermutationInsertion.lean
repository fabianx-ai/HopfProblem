/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.StandardPrism

/-!
# Permutation insertion and the shuffle prism

`Hurewicz.CubeSubdivision.PermutationInsertion.insert k e` is the permutation of
`Fin (n + 1)` sending `k` to `0` and `k.succAbove j` to `(e j).succ`; its sign is
`(-1)^k • sign e` (`sign_insert`), and `(k, e) ↦ insert k e` is a bijection
`Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1))` (`insert_bijective`), so that
sign-weighted sums over `Perm (Fin (n + 1))` reindex as double sums (`sum_sign_insert`,
`sum_sign_smul_insert`).

The geometric content is that the `k`-th shuffle simplex of the prism `Δ¹ × (cell of e)`
is the Kuhn cell of `insert k e` (`prismCubeSimplex_shuffle`). Consequently the oriented
prism realization of the standard prism is the signed sum of the Kuhn cells of the
`(n + 1)`-cube (`orientedPrismRealization_standardPrism`): the prism triangulation of
`I × Iⁿ` refines to the Kuhn triangulation of `Iⁿ⁺¹`.

This is the recursion `S_{n+1} = (n + 1) × S_n` on the Kuhn (Freudenthal) chambers,
applied to the prism decomposition of Hatcher, *Algebraic Topology*, proof of
Theorem 2.10.

## Main definitions

* `Hurewicz.CubeSubdivision.PermutationInsertion.insert`

## Main results

* `Hurewicz.CubeSubdivision.PermutationInsertion.sign_insert`,
  `Hurewicz.CubeSubdivision.PermutationInsertion.insert_bijective`
* `Hurewicz.CubeSubdivision.PermutationInsertion.sum_sign_smul_insert`
* `Hurewicz.CubeSubdivision.prismCubeSimplex_shuffle`
* `Hurewicz.CubeSubdivision.orientedPrismRealization_standardPrism`
-/

open Set Function Topology

noncomputable section

/-! ### Permutation insertion -/

/-- The permutation of `Fin (n+1)` obtained from `e : Perm (Fin n)` by inserting the
index `k` at position `0` (sending `k` to `0` and `succAbove`ing the rest). -/
def Hurewicz.CubeSubdivision.PermutationInsertion.insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e) * k.cycleRange

/-- `insert k e` sends `k` to `0`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_apply_self {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Hurewicz.CubeSubdivision.PermutationInsertion.insert k e k = 0 := by
  simp [Hurewicz.CubeSubdivision.PermutationInsertion.insert]

/-- `insert k e` sends `k.succAbove j` to `(e j).succ`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_apply_succAbove {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    Hurewicz.CubeSubdivision.PermutationInsertion.insert k e (k.succAbove j) = (e j).succ :=
  by simp [Hurewicz.CubeSubdivision.PermutationInsertion.insert]

/-- The inverse of `insert k e` sends `0` to `k`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_zero {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm 0 = k := by
  apply (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

/-- The inverse of `insert k e` sends `r.succ` to `k.succAbove (e.symm r)`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_succ {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm j.succ =
      k.succAbove (e.symm j) := by
  apply (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

/-- The sign of `insert k e` is `(-1)^k` times the sign of `e`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sign_insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e) =
      (-1) ^ (k : ℕ) * Equiv.Perm.sign e := by
  simp [Hurewicz.CubeSubdivision.PermutationInsertion.insert, mul_comm]

/-- The integer sign of `insert k e` is `(-1)^k` times the integer sign of `e`. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sign_insert_int {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e) : ℤ) =
      (-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ) := by simp

/-- `j.val < (k.predAbove r).val` iff `(k.succAbove j).val < r.val`. -/
theorem Hurewicz.CubeSubdivision.lt_predAbove_iff_succAbove_lt {n : ℕ} (k : Fin (n + 1))
    (j : Fin n) (r : Fin (n + 2)) : j.val < (k.predAbove r).val ↔ (k.succAbove j).val < r.val := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- The prism cube vertex of the shuffle at index `r` equals the prism cube vertex of
the inserted permutation `insert r e`. -/
theorem Hurewicz.CubeSubdivision.prismCubeVertex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (r : Fin (n + 2)) :
    prismCubeVertex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k r) =
      Hurewicz.CubeTriangulation.cubeVertex (PermutationInsertion.insert k e) r := by
  funext coord
  refine Fin.cases ?_ (fun j => ?_) coord
  · by_cases h : r ≤ k.castSucc
    · have h' : ¬k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_lt] using h
      simp [prismCubeVertex, shufflePrismVertices, h, Hurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
    · have h' : k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_le] using h
      simp [prismCubeVertex, shufflePrismVertices, h, Hurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
  · simp only [shufflePrismVertices, prismCubeVertex_succ,
      Hurewicz.CubeTriangulation.cubeVertex, PermutationInsertion.insert_symm_apply_succ]
    simp only [lt_predAbove_iff_succAbove_lt]

/-- The prism cube simplex of the shuffle at `k` equals the prism cube simplex of
`insert k e`. -/
theorem Hurewicz.CubeSubdivision.prismCubeSimplex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    prismCubeSimplex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k) =
      Hurewicz.CubeTriangulation.cubeSimplex (PermutationInsertion.insert k e) := by
  apply congrArg Hurewicz.CubeTriangulation.cubeAffineSimplex
  funext r
  exact prismCubeVertex_shuffle e k r

/-- Insertion `(k, e) ↦ insert k e` is injective. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_injective {n : ℕ} :
    Function.Injective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        Hurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  rintro ⟨k, e⟩ ⟨l, f⟩ h
  have hk : k = l := by simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0) h
  subst l
  refine Prod.ext rfl ?_
  apply Equiv.ext
  intro j
  apply Fin.succ_injective n
  simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (k.succAbove j)) h

/-- Insertion `(k, e) ↦ insert k e` is bijective onto `Perm (Fin (n+1))`. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_bijective {n : ℕ} :
    Function.Bijective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        Hurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨insert_injective, by simp [Fintype.card_perm, Nat.factorial_succ]⟩

/-- Sums over `Perm (Fin (n+1))` reindex as double sums over `k` and
`Perm (Fin n)` via insertion. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sum_insert {n : ℕ} {A : Type*}
    [AddCommMonoid A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          f (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f σ := by
  rw [← Fintype.sum_prod_type']
  exact insert_bijective.sum_comp f

/-- The sign-weighted sum over `Perm (Fin (n+1))` reindexed by insertion picks up the
factor `(-1)^k`. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sum_sign_insert {n : ℕ} {A : Type*}
    [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          ((-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ)) •
            f (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [sign_insert_int] using sum_insert (fun σ => (Equiv.Perm.sign σ : ℤ) • f σ)

/-- The `(-1)^k •`-weighted sum over `Perm (Fin (n+1))` reindexed by insertion. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sum_sign_smul_insert {n : ℕ}
    {A : Type*} [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          (-1 : ℤ) ^ (k : ℕ) •
            ((Equiv.Perm.sign e : ℤ) •
              f (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e))) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [SemigroupAction.mul_smul] using sum_sign_insert f

/-- The oriented prism realization of the standard prism equals the signed Kuhn-cell
sum of `p`. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_standardPrism {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X)) :
    orientedPrismRealization p (n + 1)
        (standardPrism n (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j)) =
      ∑ perm : Equiv.Perm (Fin (n + 1)),
        Hurewicz.CubeTriangulation.cubeOrientation perm •
          SingularChains.simplexChain X (n + 1)
            (p.comp (Hurewicz.CubeTriangulation.cubeSimplex perm)) := by
  simp only [standardPrism, map_sum, map_zsmul, orientedPrismRealization_simplex,
    prismCubeSimplex_shuffle, ← Finset.sum_zsmul,
    Hurewicz.CubeTriangulation.cubeOrientation]
  exact
    PermutationInsertion.sum_sign_smul_insert
      (fun perm =>
        SingularChains.simplexChain X (n + 1)
          (p.comp (Hurewicz.CubeTriangulation.cubeSimplex perm)))
