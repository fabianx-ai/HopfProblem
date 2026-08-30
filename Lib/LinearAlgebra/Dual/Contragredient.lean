/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Contragredient integral representations

This file supplies two small conversion tools used when a geometric monodromy action is first
constructed on a multiplicatively tagged abelian group:

* removal of the `Multiplicative` tag as an integral-linear representation;
* the contragredient representation on the integral dual.

The inverse in the definition of `contragredient` is essential: dualization reverses composition.
-/

@[expose] public section

namespace LinearRepresentation

variable {G M : Type*} [Group G] [AddCommGroup M]

/-- Remove a `Multiplicative` tag from an automorphism of an abelian group and regard the result
as an integral-linear equivalence. -/
def ofMultiplicativeEquiv (e : MulAut (Multiplicative M)) : M ≃ₗ[ℤ] M :=
  (((AddEquiv.additiveMultiplicative M).symm.trans e.toAdditive).trans
    (AddEquiv.additiveMultiplicative M)).toIntLinearEquiv

@[simp]
theorem ofMultiplicativeEquiv_apply (e : MulAut (Multiplicative M)) (x : M) :
    ofMultiplicativeEquiv e x = (e (Multiplicative.ofAdd x)).toAdd :=
  rfl

/-- A multiplicative action on the multiplicative tag of an abelian group is an integral-linear
representation on that group. -/
def ofMultiplicative (ρ : G →* MulAut (Multiplicative M)) : G →* (M ≃ₗ[ℤ] M) where
  toFun g := ofMultiplicativeEquiv (ρ g)
  map_one' := by
    ext x
    simp [ofMultiplicativeEquiv]
  map_mul' g h := by
    ext x
    simp [ofMultiplicativeEquiv, LinearEquiv.mul_apply]

@[simp]
theorem ofMultiplicative_apply (ρ : G →* MulAut (Multiplicative M)) (g : G) (x : M) :
    ofMultiplicative ρ g x = (ρ g (Multiplicative.ofAdd x)).toAdd :=
  by rfl

/-- The contragredient representation.  A group element acts on a functional by precomposition
with the inverse action on the original module. -/
def contragredient {R : Type*} [CommSemiring R] {N : Type*}
    [AddCommMonoid N] [Module R N] (ρ : G →* (N ≃ₗ[R] N)) :
    G →* (Module.Dual R N ≃ₗ[R] Module.Dual R N) where
  toFun g := (ρ g⁻¹).dualMap
  map_one' := by
    apply LinearEquiv.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp [LinearEquiv.dualMap_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp only [mul_inv_rev, map_mul, LinearEquiv.mul_apply, LinearEquiv.dualMap_apply]

@[simp]
theorem contragredient_apply {R : Type*} [CommSemiring R] {N : Type*}
    [AddCommMonoid N] [Module R N] (ρ : G →* (N ≃ₗ[R] N)) (g : G)
    (φ : Module.Dual R N) (x : N) :
    contragredient ρ g φ x = φ (ρ g⁻¹ x) :=
  by rfl

/-- A vector in a representation of a free group is invariant exactly when it is fixed by every
free generator. -/
theorem freeGroup_invariant_iff {A R N : Type*} [CommSemiring R]
    [AddCommMonoid N] [Module R N] (ρ : FreeGroup A →* (N ≃ₗ[R] N)) (x : N) :
    (∀ g, ρ g x = x) ↔ ∀ a, ρ (FreeGroup.of a) x = x := by
  constructor
  · exact fun h a ↦ h (FreeGroup.of a)
  · intro h g
    induction g using FreeGroup.induction_on with
    | C1 => simp
    | of a => exact h a
    | inv_of a ha =>
        rw [map_inv]
        calc
          (ρ (FreeGroup.of a))⁻¹ x =
              (ρ (FreeGroup.of a))⁻¹ (ρ (FreeGroup.of a) x) :=
            congrArg (fun y ↦ (ρ (FreeGroup.of a))⁻¹ y) ha.symm
          _ = x := by
            rw [← LinearEquiv.mul_apply]
            simp
    | mul g k hg hk =>
        simp only [map_mul, LinearEquiv.mul_apply, hk, hg]

end LinearRepresentation
