/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Matrix coordinates on exterior powers of finite free modules

This file gives the standard basis of `⋀[R]^n (Fin m → R)`, identifies the matrix of an induced
exterior-power map with the corresponding matrix of minors, and exposes the resulting coordinate
formula.

The implementation was extracted and generalized from the integral rank-four development in
`Hopf/LCP/Specialization.lean`, itself move-only extracted from `Solution.lean` at
`9ac8a456b526527837d7082ff775213ca8bc9809` (original monolith lines 133802--148196).
-/

@[expose] public section

namespace exteriorPower

open scoped Matrix

universe u

variable (R : Type u) [CommRing R]

/-- The standard basis of the `n`th exterior power of the coordinate module `Fin m → R`. -/
noncomputable def finBasis (m n : ℕ) :
    Module.Basis (Set.powersetCard (Fin m) n) R (⋀[R]^n (Fin m → R)) :=
  (Pi.basisFun R (Fin m)).exteriorPower n

/-- The coefficient of the exterior map induced by `A` is the corresponding minor of `A`. -/
theorem finBasis_map_coefficient (m₁ m₂ n : ℕ) (A : Matrix (Fin m₂) (Fin m₁) R)
    (s : Set.powersetCard (Fin m₂) n) (t : Set.powersetCard (Fin m₁) n) :
    (finBasis R m₂ n).repr
        (exteriorPower.map n A.mulVecLin (finBasis R m₁ n t)) s =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  unfold finBasis
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
      (Matrix.of fun i j =>
          (Pi.basisFun R (Fin m₂)).coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
            ((A.mulVecLin ∘ ((Pi.basisFun R (Fin m₁)) ∘
              Set.powersetCard.ofFinEmbEquiv.symm t)) i)) =
        (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).transpose := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr, Function.comp_apply,
      Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [hmatrix, Matrix.det_transpose]

/-- The matrix of `⋀^n A` in the standard ordered exterior bases, expressed by minors. -/
def finMatrix (n : ℕ) {m₁ m₂ : ℕ} (A : Matrix (Fin m₂) (Fin m₁) R) :
    Matrix (Set.powersetCard (Fin m₂) n) (Set.powersetCard (Fin m₁) n) R :=
  fun s t =>
    (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
      (Set.powersetCard.ofFinEmbEquiv.symm t)).det

/-- The matrix of the induced exterior-power map is the matrix of minors. -/
theorem toMatrix_map (m₁ m₂ n : ℕ) (A : Matrix (Fin m₂) (Fin m₁) R) :
    LinearMap.toMatrix (finBasis R m₁ n) (finBasis R m₂ n) (exteriorPower.map n A.mulVecLin) =
      finMatrix R n A := by
  ext s t
  rw [LinearMap.toMatrix_apply]
  exact finBasis_map_coefficient R m₁ m₂ n A s t

/-- Coordinates in the standard ordered basis of an exterior power of `Fin m → R`. -/
noncomputable def finCoordinates (m n : ℕ) :
    (⋀[R]^n (Fin m → R)) ≃ₗ[R] (Set.powersetCard (Fin m) n → R) :=
  (finBasis R m n).equivFun

@[simp]
theorem finCoordinates_apply (m n : ℕ) (x : ⋀[R]^n (Fin m → R))
    (s : Set.powersetCard (Fin m) n) :
    finCoordinates R m n x s = (finBasis R m n).repr x s :=
  congrFun ((finBasis R m n).equivFun_apply x) s

/-- Applying an exterior-power map in coordinates is multiplication by the matrix of minors. -/
theorem finCoordinates_map (m₁ m₂ n : ℕ) (A : Matrix (Fin m₂) (Fin m₁) R)
    (x : ⋀[R]^n (Fin m₁ → R)) :
    finCoordinates R m₂ n (exteriorPower.map n A.mulVecLin x) =
      finMatrix R n A *ᵥ finCoordinates R m₁ n x := by
  have h := LinearMap.toMatrix_mulVec_repr (finBasis R m₁ n) (finBasis R m₂ n)
    (exteriorPower.map n A.mulVecLin) x
  rw [toMatrix_map] at h
  simpa only [finCoordinates, Module.Basis.equivFun_apply] using h.symm

end exteriorPower
