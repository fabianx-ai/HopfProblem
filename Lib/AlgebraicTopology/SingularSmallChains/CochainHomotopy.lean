/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.Homotopy.CocycleEvaluation
public import Lib.AlgebraicTopology.SingularSmallChains.Basic

/-!
# Positive-degree cochain consequences of the small-chain homotopy equivalence

This file extracts the degree-independent statements used by the sheafification comparison.
For every positive degree, a small cocycle lifts to a global cocycle with exactly the prescribed
restriction, and a global cocycle whose small restriction is a boundary is already a global
boundary.

These are the cohomological form of Hatcher, *Algebraic Topology*, Proposition 2.21: a chain
homotopy equivalence induces isomorphisms on cohomology with any coefficients
(`HomotopyEquiv.quasiIso`).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace TopCat.SingularSmallChains

/-- Under a literal small-chain homotopy equivalence, every positive-degree small cocycle is the
exact restriction of a global cocycle. -/
theorem smallCochain_cocycle_lift_exact_succ
    {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U) (n : ℕ)
    (phi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).X (n + 1))
    (hphi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).d
      (n + 1) (n + 2) phi = 0) :
    ∃ psi : (AlgebraicTopology.SingularCochains.complex X A).X (n + 1),
      (AlgebraicTopology.SingularCochains.complex X A).d (n + 1) (n + 2) psi = 0 ∧
      (cochainRestriction A U).f (n + 1) psi = phi := by
  let E := cochainRestrictionHomotopyEquiv A U e he
  let psi := E.inv.f (n + 1) phi
  let chi := E.homotopyInvHomId.hom (n + 1) n phi
  have hpsi : (AlgebraicTopology.SingularCochains.complex X A).d
      (n + 1) (n + 2) psi = 0 := by
    rw [cochainMap_d E.inv (n + 1) (n + 2), hphi, map_zero]
  have hchi : (cochainRestriction A U).f (n + 1) psi =
      (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).d
        n (n + 1) chi + phi := by
    exact CochainComplex.homotopy_on_cocycle_succ E.homotopyInvHomId n phi hphi
  let eta := cochainExtension A U n chi
  refine ⟨psi - (AlgebraicTopology.SingularCochains.complex X A).d
    n (n + 1) eta, ?_, ?_⟩
  · rw [map_sub, hpsi]
    have hz := congrArg
      (fun k : (AlgebraicTopology.SingularCochains.complex X A).X n ⟶
        (AlgebraicTopology.SingularCochains.complex X A).X (n + 2) => k eta)
      ((AlgebraicTopology.SingularCochains.complex X A).d_comp_d n (n + 1) (n + 2))
    change (AlgebraicTopology.SingularCochains.complex X A).d (n + 1) (n + 2)
      ((AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) eta) = 0 at hz
    rw [hz, sub_self]
  · rw [map_sub, ← cochainMap_d (cochainRestriction A U) n (n + 1) eta,
      cochainRestriction_extension A U n chi, hchi, add_sub_cancel_left]

/-- Under a literal small-chain homotopy equivalence, a global positive-degree cocycle whose
small restriction has a primitive has an actual global primitive. -/
theorem smallCochain_boundary_of_restriction_boundary_succ
    {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U) (n : ℕ)
    (phi : (AlgebraicTopology.SingularCochains.complex X A).X (n + 1))
    (hphi : (AlgebraicTopology.SingularCochains.complex X A).d
      (n + 1) (n + 2) phi = 0)
    (chi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).X n)
    (hchi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).d
      n (n + 1) chi = (cochainRestriction A U).f (n + 1) phi) :
    ∃ psi : (AlgebraicTopology.SingularCochains.complex X A).X n,
      (AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) psi = phi := by
  let E := cochainRestrictionHomotopyEquiv A U e he
  refine ⟨E.inv.f n chi - E.homotopyHomInvId.hom (n + 1) n phi, ?_⟩
  rw [map_sub, cochainMap_d E.inv n (n + 1), hchi]
  have hh := CochainComplex.homotopy_on_cocycle_succ E.homotopyHomInvId n phi hphi
  change E.inv.f (n + 1) ((cochainRestriction A U).f (n + 1) phi) =
    (AlgebraicTopology.SingularCochains.complex X A).d n (n + 1)
      (E.homotopyHomInvId.hom (n + 1) n phi) + phi at hh
  rw [hh, add_sub_cancel_left]

/-- A small-chain homotopy equivalence induces an isomorphism on cohomology in every degree. -/
theorem cochainRestriction_homologyMap_isIso
    {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cochainRestriction A U) n) := by
  let E := cochainRestrictionHomotopyEquiv A U e he
  apply (quasiIsoAt_iff_isIso_homologyMap (cochainRestriction A U) n).mp
  change QuasiIsoAt E.hom n
  exact E.quasiIsoAt_hom n

end TopCat.SingularSmallChains
