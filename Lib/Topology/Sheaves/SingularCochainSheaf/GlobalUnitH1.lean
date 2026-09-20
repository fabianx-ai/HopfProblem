/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalKernelSmall

/-!
# The singular-cochain comparison in degree one

On a normal paracompact space the comparison map `S^•(X; A) → Γ(X, 𝒮^•(·; A))` induces an
isomorphism on degree-one cohomology.  This is the degree-one case of Bredon, *Sheaf Theory* III
Thm. 1.1; the geometric input is the classical theorem that the chains small for an open cover
include into all singular chains by a chain-homotopy equivalence (Hatcher, *Algebraic Topology*
Prop. 2.21).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- On a normal paracompact space the comparison map `S^n(X; A) → Γ(X, 𝒮^n(·; A))` is surjective
in every degree (Bredon, *Sheaf Theory* III Prop. 1.1). -/
theorem globalUnitSurjective [NormalSpace X] [ParacompactSpace X] (n : ℕ) :
    GlobalUnitSurjective X A n :=
  globalCochainUnit_surjective X A n

/-- On a normal paracompact space the comparison `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is an isomorphism
on degree-one cohomology, given the small-chain homotopy equivalences for open covers of `X`
(Bredon, *Sheaf Theory* III Thm. 1.1 at `n = 1`). -/
theorem globalCochainComparison_homology_isIso_one
    [NormalSpace X] [ParacompactSpace X]
    (hsmall : HasSmallChainEquivalences X) :
    IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1) :=
  globalCochainComparison_homology_isIso_one_of_small_chains X A
    (globalUnitSurjective X A 0)
    (globalUnitSurjective X A 1)
    (globalKernelLocallySmall X A 1)
    (globalKernelLocallySmall X A 2)
    (smallKernelGlobalOne X A)
    hsmall

end TopCat.SingularCochainSheaf
