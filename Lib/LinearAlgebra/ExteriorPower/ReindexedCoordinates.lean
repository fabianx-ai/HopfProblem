/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module


public import Lib.LinearAlgebra.ExteriorPower.MatrixCoordinates

/-!
# Reindexed coordinates on finite exterior powers

This file transports the standard powerset-indexed exterior basis of `⋀[R]^n (Fin m → R)`, its
compound matrix of minors, and its coordinate formula across an arbitrary bijection `I ≃
Set.powersetCard (Fin m) n`, i.e. across a chosen ordering of the coordinates of the exterior
power.

## Main definitions

* `exteriorPower.reindexedFinBasis`: the standard exterior basis reindexed by `I`.
* `exteriorPower.reindexedFinCoordinates`: the resulting coordinates in `I → R`.
* `exteriorPower.reindexedFinMatrix`: the compound matrix of minors reindexed on both sides.

## Main results

* `exteriorPower.toMatrix_map_reindexed`, `exteriorPower.reindexedFinCoordinates_map`: the matrix
  of `⋀^n A` in the reindexed bases is the reindexed compound matrix.

## References

* [Nicolas Bourbaki, *Algebra I, Chapters 1–3*][bourbaki1989], A III §8.5–8.6.
-/

@[expose] public section

namespace exteriorPower

open scoped Matrix

universe u v₁ v₂

variable (R : Type u) [CommRing R]

/-- The standard exterior basis transported across a chosen finite coordinate ordering. -/
noncomputable def reindexedFinBasis {m n : ℕ} {I : Type v₁}
    (e : I ≃ Set.powersetCard (Fin m) n) :
    Module.Basis I R (⋀[R]^n (Fin m → R)) :=
  (finBasis R m n).reindex e.symm

/-- A reindexed basis vector is the standard basis vector at the corresponding subset. -/
@[simp]
theorem reindexedFinBasis_apply {m n : ℕ} {I : Type v₁}
    (e : I ≃ Set.powersetCard (Fin m) n) (i : I) :
    reindexedFinBasis R e i = finBasis R m n (e i) := by
  rw [reindexedFinBasis, Module.Basis.reindex_apply]
  simp only [Equiv.symm_symm]

/-- Coordinates in a chosen finite ordering of the standard exterior basis. -/
noncomputable def reindexedFinCoordinates {m n : ℕ} {I : Type v₁} [Fintype I]
    (e : I ≃ Set.powersetCard (Fin m) n) :
    (⋀[R]^n (Fin m → R)) ≃ₗ[R] (I → R) :=
  (reindexedFinBasis R e).equivFun

/-- The reindexed coordinates of a vector are its coefficients in the reindexed basis. -/
@[simp]
theorem reindexedFinCoordinates_apply {m n : ℕ} {I : Type v₁} [Fintype I]
    (e : I ≃ Set.powersetCard (Fin m) n) (x : ⋀[R]^n (Fin m → R)) (i : I) :
    reindexedFinCoordinates R e x i = (reindexedFinBasis R e).repr x i :=
  congrFun ((reindexedFinBasis R e).equivFun_apply x) i

/-- A reindexed basis vector has the corresponding coordinate unit vector. -/
@[simp]
theorem reindexedFinCoordinates_basis {m n : ℕ} {I : Type v₁}
    [Fintype I] [DecidableEq I]
    (e : I ≃ Set.powersetCard (Fin m) n) (i : I) :
    reindexedFinCoordinates R e (reindexedFinBasis R e i) = Pi.single i 1 := by
  ext j
  simp only [reindexedFinCoordinates_apply, Module.Basis.repr_self_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- The matrix of minors transported across chosen source and target coordinate orderings. -/
def reindexedFinMatrix {m₁ m₂ n : ℕ} {I₁ : Type v₁} {I₂ : Type v₂}
    (e₁ : I₁ ≃ Set.powersetCard (Fin m₁) n)
    (e₂ : I₂ ≃ Set.powersetCard (Fin m₂) n)
    (A : Matrix (Fin m₂) (Fin m₁) R) : Matrix I₂ I₁ R :=
  fun i j => finMatrix R n A (e₂ i) (e₁ j)

/-- A reindexed coefficient of an induced exterior map is the corresponding matrix minor. -/
theorem reindexedFinBasis_map_coefficient {m₁ m₂ n : ℕ}
    {I₁ : Type v₁} {I₂ : Type v₂}
    (e₁ : I₁ ≃ Set.powersetCard (Fin m₁) n)
    (e₂ : I₂ ≃ Set.powersetCard (Fin m₂) n)
    (A : Matrix (Fin m₂) (Fin m₁) R) (i : I₂) (j : I₁) :
    (reindexedFinBasis R e₂).repr
        (exteriorPower.map n A.mulVecLin (reindexedFinBasis R e₁ j)) i =
      reindexedFinMatrix R e₁ e₂ A i j := by
  simp only [reindexedFinBasis, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply, Equiv.symm_symm]
  change
    (finBasis R m₂ n).repr
        (exteriorPower.map n A.mulVecLin (finBasis R m₁ n (e₁ j))) (e₂ i) = _
  rw [finBasis_map_coefficient]
  rfl

/-- The matrix of an induced exterior map in arbitrary finite coordinate orderings. -/
theorem toMatrix_map_reindexed {m₁ m₂ n : ℕ}
    {I₁ : Type v₁} {I₂ : Type v₂}
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (e₁ : I₁ ≃ Set.powersetCard (Fin m₁) n)
    (e₂ : I₂ ≃ Set.powersetCard (Fin m₂) n)
    (A : Matrix (Fin m₂) (Fin m₁) R) :
    LinearMap.toMatrix (reindexedFinBasis R e₁) (reindexedFinBasis R e₂)
        (exteriorPower.map n A.mulVecLin) = reindexedFinMatrix R e₁ e₂ A := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact reindexedFinBasis_map_coefficient R e₁ e₂ A i j

/-- Applying an exterior map in reindexed coordinates is multiplication by the reindexed minor
matrix. -/
theorem reindexedFinCoordinates_map {m₁ m₂ n : ℕ}
    {I₁ : Type v₁} {I₂ : Type v₂}
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (e₁ : I₁ ≃ Set.powersetCard (Fin m₁) n)
    (e₂ : I₂ ≃ Set.powersetCard (Fin m₂) n)
    (A : Matrix (Fin m₂) (Fin m₁) R) (x : ⋀[R]^n (Fin m₁ → R)) :
    reindexedFinCoordinates R e₂ (exteriorPower.map n A.mulVecLin x) =
      reindexedFinMatrix R e₁ e₂ A *ᵥ reindexedFinCoordinates R e₁ x := by
  have h := LinearMap.toMatrix_mulVec_repr (reindexedFinBasis R e₁)
    (reindexedFinBasis R e₂) (exteriorPower.map n A.mulVecLin) x
  rw [toMatrix_map_reindexed] at h
  simpa only [reindexedFinCoordinates, Module.Basis.equivFun_apply] using h.symm

end exteriorPower
