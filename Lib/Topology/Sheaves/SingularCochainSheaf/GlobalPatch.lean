/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains.Generators
public import Lib.Topology.ClosedRefinement
public import Lib.Topology.Sheaves.SingularCochainSheaf.Presheaf

/-!
# Patching native singular cochains

A closed locally finite refinement lets us choose a local representative using the first vertex
of each singular simplex.  Since a cochain has no continuity requirement in the simplex variable,
these chosen values extend to a genuine native cochain.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace
open scoped Simplicial


namespace TopCat.SingularCochainSheaf

open AlgebraicTopology.SingularCochains

/-- Pull a native global cochain back to an open subspace. -/
def restrictGlobalCochain {X : TopCat.{0}} (A : AddCommGrpCat.{0}) (n : ℕ)
    (phi : Cochains X A n) (U : Opens X) : Cochains U A n :=
  (AlgebraicTopology.SingularCochains.pullback A
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).f n phi


@[simp]
theorem restrictGlobalCochain_simplex {X : TopCat.{0}}
    (A : AddCommGrpCat.{0}) (n : ℕ) (phi : Cochains X A n)
    (U : Opens X) (sigma : TopCat.SingularSmallChains.SingularSimplex U n) :
    restrictGlobalCochain A n phi U
        (TopCat.SingularSmallChains.simplexChain U n sigma) =
      phi (TopCat.SingularSmallChains.simplexChain X n
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp sigma)) :=
  pullback_simplex A _ n phi sigma


/-- Successive restrictions agree with direct restriction. -/
theorem restrictGlobalCochain_restrict {X : TopCat.{0}}
    (A : AddCommGrpCat.{0}) (n : ℕ) (phi : Cochains X A n)
    {U V : Opens X} (i : V ⟶ U) :
    (presheaf X A n).map i.op (restrictGlobalCochain A n phi U) =
      restrictGlobalCochain A n phi V := by
  apply cochain_ext A n
  intro sigma
  let f : C(V, U) := ((Opens.toTopCat X).map i).hom
  exact (pullback_simplex A f n (restrictGlobalCochain A n phi U) sigma).trans
    ((restrictGlobalCochain_simplex A n phi U (f.comp sigma)).trans
      (restrictGlobalCochain_simplex A n phi V sigma).symm)


variable {X : TopCat.{0}} (A : AddCommGrpCat.{0}) (n : ℕ)
variable {ι : Type} (U : ι → Opens X) (R : ClosedRefinement U)
  (t : ∀ i, Cochains (U i) A n)

/-- Choose a cover index using the first vertex of a simplex. -/
def patchIndex (sigma : TopCat.SingularSmallChains.SingularSimplex X n) : ι :=
  R.index (sigma (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))))

/-- Value selected from the chosen local cochain, or zero if the simplex does not fit. -/
def patchedValue (sigma : TopCat.SingularSmallChains.SingularSimplex X n) : A := by
  classical
  exact if hsigma : Set.range sigma ⊆ U (patchIndex n U R sigma) then
    t (patchIndex n U R sigma)
      (TopCat.SingularSmallChains.simplexChain (U (patchIndex n U R sigma)) n
        (simplexInOpen n sigma (U (patchIndex n U R sigma)) hsigma))
  else 0

/-- The native singular cochain obtained by patching local simplex values. -/
def patchedCochain : Cochains X A n :=
  cochainFromValues A n (patchedValue A n U R t)

@[simp]
theorem patchedCochain_simplex
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n) :
    patchedCochain A n U R t
        (TopCat.SingularSmallChains.simplexChain X n sigma) =
      patchedValue A n U R t sigma :=
  cochainFromValues_simplex A n _ sigma

theorem patchedCochain_simplex_of_subset
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n)
    (hsigma : Set.range sigma ⊆ U (patchIndex n U R sigma)) :
    patchedCochain A n U R t
        (TopCat.SingularSmallChains.simplexChain X n sigma) =
      t (patchIndex n U R sigma)
        (TopCat.SingularSmallChains.simplexChain (U (patchIndex n U R sigma)) n
          (simplexInOpen n sigma (U (patchIndex n U R sigma)) hsigma)) := by
  rw [patchedCochain_simplex, patchedValue, dif_pos hsigma]

end TopCat.SingularCochainSheaf
