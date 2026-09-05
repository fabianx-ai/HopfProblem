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

For a finite set of free generators, this module identifies the cokernel of the sum of the
generator-difference maps with the standard coinvariants.  Each generator may independently be
replaced by its inverse, as happens when cellular edge orientations or slit-cover transitions are
changed.  The resulting cokernel is also identified with standard zeroth group homology.

This is the algebraic endpoint needed by a future cellular or local-coefficient Poincare-duality
comparison.  It contains no topology, sheaf, spectral sequence, or application-specific
monodromy representation.
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

@[simp]
theorem freeGroupGeneratorCokernelEquivCoinvariants_mk [Fintype A] [DecidableEq A]
    (rho : Representation R (FreeGroup A) V) (orientation : A → Bool) (x : V) :
    freeGroupGeneratorCokernelEquivCoinvariants rho orientation
        (Submodule.Quotient.mk x) = Coinvariants.mk rho x := by
  rfl

/-- The oriented generator cokernel as the standard zeroth group-homology module. -/
def freeGroupGeneratorCokernelEquivGroupHomologyH0
    {S B M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype B] [DecidableEq B]
    (rho : Representation S (FreeGroup B) M) (orientation : B → Bool) :
    FreeGroupGeneratorCokernel rho orientation ≃ₗ[S]
      (groupHomology (Rep.of rho) 0 : Type u) :=
  (freeGroupGeneratorCokernelEquivCoinvariants rho orientation).trans
    (groupHomology.H0Iso (Rep.of rho)).symm.toLinearEquiv

end Representation
