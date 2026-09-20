/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# The exact geometric seam in the cover-small chain theorem

The native chain groups and cover-small chain groups have explicit simplex bases, hence are
projective.  Consequently it is enough for barycentric subdivision to prove that the literal
cover-small inclusion is a quasi-isomorphism.  Mathlib then upgrades that same map to a chain
homotopy equivalence via `ChainComplex.quasiIso_iff_of_projective`: a quasi-isomorphism
between bounded-below complexes of projectives is a homotopy equivalence
(Weibel, *An Introduction to Homological Algebra*, Theorem 10.4.8).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Set

namespace TopCat.SingularSmallChains

/-- A quasi-isomorphism proof for the literal cover-small inclusion upgrades, without replacing
the map, to a chain-homotopy equivalence. -/
theorem inclusion_isHomotopyEquivalence_of_quasiIso
    {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X)
    (hU : QuasiIso (inclusion U)) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) (inclusion U) := by
  let (n : ℕ) : CategoryTheory.Projective ((complex U).X n) :=
    smallChain_projective U n
  let (n : ℕ) : CategoryTheory.Projective
      ((AlgebraicTopology.SingularCochains.chains X).X n) :=
    ModuleCat.projective_of_free (chainBasis X n)
  exact (ChainComplex.quasiIso_iff_of_projective (inclusion U)).mp hU

/-- The corresponding explicit homotopy equivalence has the literal inclusion as its forward
map. -/
def inclusionHomotopyEquivOfQuasiIso
    {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X)
    (hU : QuasiIso (inclusion U)) :
    HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X) := by
  let e := (inclusion_isHomotopyEquivalence_of_quasiIso U hU).choose
  have he : e.hom = inclusion U :=
    (inclusion_isHomotopyEquivalence_of_quasiIso U hU).choose_spec
  exact
    { hom := inclusion U
      inv := e.inv
      homotopyHomInvId := he ▸ e.homotopyHomInvId
      homotopyInvHomId := he ▸ e.homotopyInvHomId }

/-- The forward map of `inclusionHomotopyEquivOfQuasiIso` is the cover-small inclusion
itself. -/
@[simp]
theorem inclusionHomotopyEquivOfQuasiIso_hom
    {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X)
    (hU : QuasiIso (inclusion U)) :
    (inclusionHomotopyEquivOfQuasiIso U hU).hom = inclusion U := rfl

end TopCat.SingularSmallChains
