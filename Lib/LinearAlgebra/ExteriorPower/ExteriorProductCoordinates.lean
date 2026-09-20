/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.LinearAlgebra.ExteriorPower.MatrixCoordinates
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Exterior products in standard coordinates

This file equips homogeneous exterior powers with their bilinear exterior product and computes
that product on the standard ordered bases of finite coordinate modules: `e_S ∧ e_T` vanishes when
`S` and `T` meet, and equals `± e_{S ∪ T}` otherwise, the sign being the signature of the
permutation that sorts the concatenation of the increasing enumerations of `S` and `T`
(`Set.powersetCard.permOfDisjoint`).

## Main definitions

* `exteriorPower.wedge`: the exterior product `⋀^p M →ₗ ⋀^q M →ₗ ⋀^(p + q) M`.

## Main results

* `exteriorPower.finBasis_wedge_of_not_disjoint`, `exteriorPower.finBasis_wedge_of_disjoint`:
  the product of two standard basis vectors.

## References

* [Nicolas Bourbaki, *Algebra I, Chapters 1–3*][bourbaki1989], A III §8.5 (multiplication in the
  exterior algebra of a free module on a basis).
-/

@[expose] public section

namespace exteriorPower

universe u v

variable (R : Type u) [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The exterior product of two homogeneous exterior powers, as a curried bilinear map. -/
def wedge (p q : ℕ) :
    (⋀[R]^p M) →ₗ[R] (⋀[R]^q M) →ₗ[R] (⋀[R]^(p + q) M) :=
  LinearMap.mk₂ R
    (fun x y => ⟨x.1 * y.1, SetLike.GradedMul.mul_mem x.2 y.2⟩)
    (fun x y z => by
      apply Subtype.ext
      exact add_mul x.1 y.1 z.1)
    (fun c x y => by
      apply Subtype.ext
      exact Algebra.smul_mul_assoc c x.1 y.1)
    (fun x y z => by
      apply Subtype.ext
      exact mul_add x.1 y.1 z.1)
    (fun c x y => by
      apply Subtype.ext
      exact Algebra.mul_smul_comm c x.1 y.1)

/-- The exterior product is the multiplication of the exterior algebra, read on the homogeneous
components. -/
@[simp]
theorem coe_wedge (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    (wedge R p q x y : ExteriorAlgebra R M) = x.1 * y.1 :=
  rfl

variable (m p q : ℕ)

/-- A standard exterior basis vector has the corresponding coordinate unit vector. -/
@[simp]
theorem finCoordinates_finBasis (n : ℕ) (s : Set.powersetCard (Fin m) n) :
    finCoordinates R m n (finBasis R m n s) = Pi.single s 1 := by
  ext t
  simp only [finCoordinates_apply, Module.Basis.repr_self_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- Standard basis exterior products with repeated indices vanish. -/
theorem finBasis_wedge_of_not_disjoint
    (s : Set.powersetCard (Fin m) p) (t : Set.powersetCard (Fin m) q)
    (h : ¬Disjoint s.val t.val) :
    wedge R p q (finBasis R m p s) (finBasis R m q t) = 0 := by
  apply Subtype.ext
  change (finBasis R m p s : ExteriorAlgebra R (Fin m → R)) *
      (finBasis R m q t : ExteriorAlgebra R (Fin m → R)) = 0
  unfold finBasis
  rw [← ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun R (Fin m)) s,
    ← ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun R (Fin m)) t]
  exact ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun R (Fin m)) s t h

/-- In standard coordinates, a product with repeated basis indices is zero. -/
theorem finCoordinates_wedge_of_not_disjoint
    (s : Set.powersetCard (Fin m) p) (t : Set.powersetCard (Fin m) q)
    (h : ¬Disjoint s.val t.val) :
    finCoordinates R m (p + q)
        (wedge R p q (finBasis R m p s) (finBasis R m q t)) = 0 := by
  rw [finBasis_wedge_of_not_disjoint R m p q s t h, map_zero]

/-- Standard basis exterior products concatenate with the shuffle sign. -/
theorem finBasis_wedge_of_disjoint
    (s : Set.powersetCard (Fin m) p) (t : Set.powersetCard (Fin m) q)
    (h : Disjoint s.val t.val) :
    wedge R p q (finBasis R m p s) (finBasis R m q t) =
      (Set.powersetCard.permOfDisjoint h).sign •
        finBasis R m (p + q) (Set.powersetCard.disjUnion h) := by
  apply Subtype.ext
  change (finBasis R m p s : ExteriorAlgebra R (Fin m → R)) *
      (finBasis R m q t : ExteriorAlgebra R (Fin m → R)) =
        (Set.powersetCard.permOfDisjoint h).sign •
          (finBasis R m (p + q) (Set.powersetCard.disjUnion h) :
            ExteriorAlgebra R (Fin m → R))
  unfold finBasis
  rw [← ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun R (Fin m)) s,
    ← ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun R (Fin m)) t,
    ← ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun R (Fin m))
      (Set.powersetCard.disjUnion h)]
  exact ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun R (Fin m)) s t h

/-- In standard coordinates, disjoint basis products are signed coordinate unit vectors. -/
theorem finCoordinates_wedge_of_disjoint
    (s : Set.powersetCard (Fin m) p) (t : Set.powersetCard (Fin m) q)
    (h : Disjoint s.val t.val) :
    finCoordinates R m (p + q)
        (wedge R p q (finBasis R m p s) (finBasis R m q t)) =
      (Set.powersetCard.permOfDisjoint h).sign •
        Pi.single (Set.powersetCard.disjUnion h) 1 := by
  rw [finBasis_wedge_of_disjoint R m p q s t h, Units.smul_def, map_zsmul,
    Units.smul_def,
    finCoordinates_finBasis]

end exteriorPower
