/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Hom.PowersetCard
public import Mathlib.Data.List.Lex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fintype.Pi

/-!
# Minor coordinates on exterior powers

Coordinates on `⋀[ℤ]^n (Fin m → ℤ)` in the standard basis indexed by the `n`-element subsets of
`Fin m`, enumerated lexicographically by `Fin (m.choose n)`, and the Cauchy–Binet law: the matrix
of `⋀^n` of a product is the product of the matrices of `n × n` minors (the compound matrices).

## Main definitions

* `SortedSubset m n` — `n`-subsets of `Fin m` carrying the lexicographic order on
  sorted tuples (the `Lex` synonym is needed because `↥(Set.powersetCard _ _)`
  already carries the subset `PartialOrder`).
* `powersetCardFinEquiv` — the enumeration `Set.powersetCard (Fin m) n ≃
  Fin (m.choose n)`, pinned by `powersetCardFinEquiv_lt_iff`.
* `standardExteriorBasis`, `standardExteriorBasisFin`, `standardExteriorCoordinates`
  — the standard exterior basis in powersetCard and `Fin (m.choose n)` indexing.
* `exteriorMinorMatrix`, `exteriorPowerMap`, `exteriorPowerMap_toMatrix`,
  `cauchyBinet_minors` — the rectangular minor matrix of a linear map and the
  Cauchy–Binet multiplication law.

## References

* [Nicolas Bourbaki, *Algebra I, Chapters 1–3*][bourbaki1989], A III §8.6 (the minors of a
  composite map: Cauchy–Binet).
* [Roger A. Horn and Charles R. Johnson, *Matrix Analysis*][horn_johnson2012], §0.8.7 (compound
  matrices and the Cauchy–Binet formula).
-/

open scoped Matrix
open Set

namespace PeriodTorusHigherHomologyExterior

@[expose] public noncomputable section

/-- `n`-subsets of `Fin m` carrying the lexicographic order on sorted tuples. -/
abbrev SortedSubset (m n : ℕ) := Lex (Set.powersetCard (Fin m) n)

/-- `n`-subsets of `Fin m` form a finite type. -/
instance sortedSubsetFintype (m n : ℕ) : Fintype (SortedSubset m n) :=
  inferInstanceAs (Fintype (Set.powersetCard (Fin m) n))

/-- Lexicographic order on `n`-subsets via their sorted tuples of elements. -/
instance sortedSubsetLinearOrder (m n : ℕ) : LinearOrder (SortedSubset m n) :=
  LinearOrder.lift' (fun s ↦ (ofLex s).1.sort (· ≤ ·)) fun s t h ↦
    ofLex.injective <| Subtype.ext <| by
      have h2 := congrArg List.toFinset h
      rwa [Finset.sort_toFinset, Finset.sort_toFinset] at h2

/-- There are `m.choose n` subsets of `Fin m` of cardinality `n`. -/
theorem sortedSubset_card (m n : ℕ) :
    Fintype.card (SortedSubset m n) = m.choose n := by
  rw [show Fintype.card (SortedSubset m n) =
      Fintype.card (↥(Set.powersetCard (Fin m) n)) from
      Fintype.card_congr (Equiv.refl _), ← Nat.card_eq_fintype_card,
    Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The lexicographic enumeration of `n`-subsets of `Fin m`: the unique
order-isomorphism from the sorted-tuple lex order to `Fin (m.choose n)`. -/
def powersetCardFinEquiv (m n : ℕ) :
    Set.powersetCard (Fin m) n ≃ Fin (m.choose n) :=
  toLex.trans <|
    (Equiv.subtypeUnivEquiv (fun s ↦ Finset.mem_univ s)).symm.trans <|
      ((Finset.orderIsoOfFin (Finset.univ : Finset (SortedSubset m n))
        (by rw [Finset.card_univ]; exact sortedSubset_card m n)).symm.toEquiv)

/-- The enumeration is pinned by its characterization: `e s < e t` iff the sorted
tuple of `s` is lexicographically below that of `t`. -/
theorem powersetCardFinEquiv_lt_iff {m n : ℕ}
    (s t : Set.powersetCard (Fin m) n) :
    powersetCardFinEquiv m n s < powersetCardFinEquiv m n t ↔
      List.Lex (· < ·) ((s : Finset (Fin m)).sort (· ≤ ·))
        ((t : Finset (Fin m)).sort (· ≤ ·)) := by
  have hcard : (Finset.univ : Finset (SortedSubset m n)).card = m.choose n := by
    rw [Finset.card_univ]; exact sortedSubset_card m n
  have key : ∀ x y : ↥(Finset.univ : Finset (SortedSubset m n)),
      ((Finset.univ.orderIsoOfFin hcard).symm.toEquiv x <
        (Finset.univ.orderIsoOfFin hcard).symm.toEquiv y) ↔
        (x : SortedSubset m n) < y := fun x y ↦
      (OrderIso.lt_iff_lt (Finset.univ.orderIsoOfFin hcard).symm).trans Iff.rfl
  unfold powersetCardFinEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply]
  rw [key]
  show (toLex s : SortedSubset m n) < toLex t ↔ _
  exact Iff.rfl

/-- The standard exterior basis of `⋀[ℤ]^n (Fin m → ℤ)`, indexed by `n`-subsets
of `Fin m`. -/
def standardExteriorBasis (m n : ℕ) :
    Module.Basis (Set.powersetCard (Fin m) n) ℤ (⋀[ℤ]^n (Fin m → ℤ)) :=
  (Pi.basisFun ℤ (Fin m)).exteriorPower n

/-- The `s`-th coefficient of `A.mulVecLin` acting on the `t`-th basis element is
the `n × n` minor of `A` on row-set `s` and column-set `t`. -/
theorem standardExterior_map_coefficient (m n : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (s t : Set.powersetCard (Fin m) n) :
    (standardExteriorBasis m n).repr
        (exteriorPower.map n A.mulVecLin (standardExteriorBasis m n t)) s =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  unfold standardExteriorBasis
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
    (Matrix.of fun i j =>
        (Pi.basisFun ℤ (Fin m)).coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
          ((A.mulVecLin ∘ ((Pi.basisFun ℤ (Fin m)) ∘ Set.powersetCard.ofFinEmbEquiv.symm t)) i)) =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).transpose := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr, Function.comp_apply,
      Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [hmatrix, Matrix.det_transpose]

/-- The standard exterior basis reindexed by `Fin (m.choose n)`. -/
def standardExteriorBasisFin (m n : ℕ) :
    Module.Basis (Fin (m.choose n)) ℤ (⋀[ℤ]^n (Fin m → ℤ)) :=
  (standardExteriorBasis m n).reindex (powersetCardFinEquiv m n)

/-- Coordinates of `⋀[ℤ]^n (Fin m → ℤ)` as a plain function space. -/
def standardExteriorCoordinates (m n : ℕ) :
    (⋀[ℤ]^n (Fin m → ℤ)) ≃ₗ[ℤ] (Fin (m.choose n) → ℤ) :=
  (standardExteriorBasisFin m n).equivFun

/-- The `n`-th exterior power of `Fin m → ℤ` is free of rank `m.choose n`. -/
theorem exteriorPower_finrank_choose (m n : ℕ) :
    Module.finrank ℤ (⋀[ℤ]^n (Fin m → ℤ)) = m.choose n := by
  rw [exteriorPower.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The `n`-minor matrix of `T : Matrix (Fin p) (Fin m) ℤ`: entry `(s, t)` is the
`n × n` minor of `T` on row-set `s` and column-set `t`, with `Fin (_.choose n)`
indices decoded to sorted `n`-tuples via `powersetCardFinEquiv`. -/
def exteriorMinorMatrix (p m n : ℕ)
    (T : Matrix (Fin p) (Fin m) ℤ) :
    Matrix (Fin (p.choose n)) (Fin (m.choose n)) ℤ :=
  fun s t ↦ (T.submatrix
    ((Set.powersetCard.ofFinEmbEquiv.symm ((powersetCardFinEquiv p n).symm s) :
      Fin n → Fin p))
    ((Set.powersetCard.ofFinEmbEquiv.symm ((powersetCardFinEquiv m n).symm t) :
      Fin n → Fin m))).det

/-- The map induced by `A.mulVecLin` on the `n`-th exterior powers. -/
def exteriorPowerMap (p m n : ℕ) (A : Matrix (Fin p) (Fin m) ℤ) :
    (⋀[ℤ]^n (Fin m → ℤ)) →ₗ[ℤ] (⋀[ℤ]^n (Fin p → ℤ)) :=
  exteriorPower.map n A.mulVecLin

/-- In standard coordinates, `exteriorPowerMap A` is the minor matrix of `A`. -/
theorem exteriorPowerMap_toMatrix (p m n : ℕ) (A : Matrix (Fin p) (Fin m) ℤ) :
    LinearMap.toMatrix (standardExteriorBasisFin m n)
        (standardExteriorBasisFin p n) (exteriorPowerMap p m n A) =
      exteriorMinorMatrix p m n A := by
  ext s t
  rw [LinearMap.toMatrix_apply]
  unfold standardExteriorBasisFin exteriorPowerMap standardExteriorBasis
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply,
    exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
    (Matrix.of fun i j =>
        (Pi.basisFun ℤ (Fin p)).coord
          (Set.powersetCard.ofFinEmbEquiv.symm ((powersetCardFinEquiv p n).symm s) j)
          (((A.mulVecLin ∘ (Pi.basisFun ℤ (Fin m))) ∘
            Set.powersetCard.ofFinEmbEquiv.symm ((powersetCardFinEquiv m n).symm t)) i)) =
      (A.submatrix
          (Set.powersetCard.ofFinEmbEquiv.symm ((powersetCardFinEquiv p n).symm s) :
            Fin n → Fin p)
          (Set.powersetCard.ofFinEmbEquiv.symm ((powersetCardFinEquiv m n).symm t) :
            Fin n → Fin m)).transpose := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr, Function.comp_apply,
      Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [hmatrix, Matrix.det_transpose]
  rfl

/-- Cauchy–Binet: the `n`-minor matrix of a product is the product of the
`n`-minor matrices. -/
theorem cauchyBinet_minors (p q m n : ℕ)
    (A : Matrix (Fin p) (Fin q) ℤ) (B : Matrix (Fin q) (Fin m) ℤ) :
    exteriorMinorMatrix p m n (A * B) =
      exteriorMinorMatrix p q n A * exteriorMinorMatrix q m n B := by
  have hcomp : exteriorPowerMap p m n (A * B) =
      (exteriorPowerMap p q n A).comp (exteriorPowerMap q m n B) := by
    unfold exteriorPowerMap
    rw [Matrix.mulVecLin_mul, exteriorPower.map_comp]
  rw [← exteriorPowerMap_toMatrix p m n (A * B), hcomp,
    LinearMap.toMatrix_comp (standardExteriorBasisFin m n) (standardExteriorBasisFin q n)
      (standardExteriorBasisFin p n),
    exteriorPowerMap_toMatrix, exteriorPowerMap_toMatrix]

end

end PeriodTorusHigherHomologyExterior
