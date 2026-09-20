/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.RepresentationTheory.FreeGroupCoinvariants
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Oriented free-generator cokernels

For a representation `ρ` of a free group `F(A)` on a module `V` with `A` finite, the map
`(v_a) ↦ ∑_a (ρ (x_a) v_a - v_a) : (A → V) →ₗ V` has image the submodule of coinvariant relations,
so its cokernel is the coinvariants `V_F` and hence the zeroth group homology `H₀(F(A); V)`.  Each
generator `x_a` may independently be replaced by its inverse without changing the image, since
`ρ (x⁻¹) - 1` and `ρ (x) - 1` have the same range.

## Main definitions

* `Representation.freeGroupOrientedGeneratorDifference`: the sum of the generator differences for
  a choice of generator or inverse generator at each index.
* `Representation.FreeGroupGeneratorCokernel`: its cokernel.

## Main results

* `Representation.freeGroupGeneratorCokernelEquivCoinvariants`: the cokernel is the coinvariants.
* `Representation.freeGroupGeneratorCokernelEquivGroupHomologyH0`: the cokernel is `H₀(F(A); V)`.

## References

* [Kenneth S. Brown, *Cohomology of Groups*][brown1982], Ch. I §4 (the beginning of the free
  resolution of `ℤ` over `ℤF` for a free group `F`), II.2 (coinvariants) and III.1 (homology with
  coefficients, `H₀(F(A); M) ≅ M_F`).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

namespace Representation

universe u v w

variable {R : Type u} {A : Type v} {V : Type w}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Choose each distinguished free generator or its inverse. -/
def orientedFreeGenerator (orientation : A → Bool) (a : A) : FreeGroup A :=
  if orientation a then (FreeGroup.of a)⁻¹ else FreeGroup.of a

/-- The sum of the chosen oriented generator differences. -/
def freeGroupOrientedGeneratorDifference [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool) :
    (A → V) →ₗ[R] V where
  toFun x := ∑ a, (rho (orientedFreeGenerator orientation a) (x a) - x a)
  map_add' x y := by
    simp only [Pi.add_apply, map_add]
    simp only [add_sub_add_comm, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, map_smul, smul_sub, Finset.smul_sum, RingHom.id_apply]

/-- The generator difference `ρ (x_a) v - v` is hit by the oriented difference map, at the
one-point family supported at `a`. -/
theorem freeGroupOrientedGeneratorDifference_single [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool)
    (a : A) (x : V) :
    freeGroupOrientedGeneratorDifference rho orientation
        (Pi.single a (if orientation a then -(rho (FreeGroup.of a) x) else x)) =
      rho (FreeGroup.of a) x - x := by
  classical
  have hsum (y : V) :
      (∑ b, (rho (orientedFreeGenerator orientation b)
          ((Pi.single a y : A → V) b) -
        (Pi.single a y : A → V) b)) =
        rho (orientedFreeGenerator orientation a) y - y := by
    let f : A → V := fun b ↦
      rho (orientedFreeGenerator orientation b) ((Pi.single a y : A → V) b) -
        (Pi.single a y : A → V) b
    change (∑ b, f b) = _
    calc
      _ = f a := Finset.sum_eq_single_of_mem a (Finset.mem_univ a) (by
        intro b _ hba
        simp [f, Pi.single_apply, hba])
      _ = _ := by simp [f]
  by_cases h : orientation a
  · change (∑ b, (rho (orientedFreeGenerator orientation b)
        ((Pi.single a (if orientation a then -(rho (FreeGroup.of a) x) else x) : A → V) b) -
      (Pi.single a (if orientation a then -(rho (FreeGroup.of a) x) else x) : A → V) b)) = _
    rw [hsum]
    simp [orientedFreeGenerator, h]
    abel
  · change (∑ b, (rho (orientedFreeGenerator orientation b)
        ((Pi.single a (if orientation a then -(rho (FreeGroup.of a) x) else x) : A → V) b) -
      (Pi.single a (if orientation a then -(rho (FreeGroup.of a) x) else x) : A → V) b)) = _
    rw [hsum]
    simp [orientedFreeGenerator, h]

/-- The image of the oriented presentation differential is the full standard coinvariant
relation submodule. -/
theorem freeGroupOrientedGeneratorDifference_range_eq_coinvariants_ker
    [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool) :
    LinearMap.range (freeGroupOrientedGeneratorDifference rho orientation) =
      Coinvariants.ker rho := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact Submodule.sum_mem _ fun a _ ↦
      Coinvariants.sub_mem_ker (orientedFreeGenerator orientation a) (x a)
  · rw [coinvariants_ker_eq_freeGroupGeneratorRelations]
    apply Submodule.span_le.2
    rintro y ⟨⟨a, x⟩, rfl⟩
    exact ⟨Pi.single a (if orientation a then -(rho (FreeGroup.of a) x) else x),
      freeGroupOrientedGeneratorDifference_single rho orientation a x⟩

/-- The presentation-level top cokernel associated to oriented free generators. -/
abbrev FreeGroupGeneratorCokernel [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool) :=
  V ⧸ LinearMap.range (freeGroupOrientedGeneratorDifference rho orientation)

/-- Oriented generator cokernels are canonically the standard coinvariants. -/
def freeGroupGeneratorCokernelEquivCoinvariants [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool) :
    FreeGroupGeneratorCokernel rho orientation ≃ₗ[R] Coinvariants rho :=
  Submodule.quotEquivOfEq _ _
    (freeGroupOrientedGeneratorDifference_range_eq_coinvariants_ker rho orientation)

/-- The identification of the cokernel with the coinvariants sends the class of `x` to the
coinvariant class of `x`. -/
@[simp]
theorem freeGroupGeneratorCokernelEquivCoinvariants_mk [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool) (x : V) :
    freeGroupGeneratorCokernelEquivCoinvariants rho orientation
        (Submodule.Quotient.mk x) = Coinvariants.mk rho x := by
  rfl

/-- The oriented generator cokernel as the standard zeroth group-homology module.

The ring, the generating set and the module share one universe because Mathlib's `groupHomology`
is declared for a ring and a group in a single universe `{k G : Type u} (A : Rep.{u} k G)`
(`Rep` itself is universe-polymorphic in all three). -/
def freeGroupGeneratorCokernelEquivGroupHomologyH0
    {S B M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype B] [DecidableEq B]
    (rho : Representation S (FreeGroup B) M) (orientation : B → Bool) :
    FreeGroupGeneratorCokernel rho orientation ≃ₗ[S]
      (groupHomology (Rep.of rho) 0 : Type u) :=
  (freeGroupGeneratorCokernelEquivCoinvariants rho orientation).trans
    (groupHomology.H0Iso (Rep.of rho)).symm.toLinearEquiv

end Representation
