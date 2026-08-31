/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalKernelSmall

/-!
# The global singular-cochain unit in degree one

Closed locally finite patching discharges all sheafification hypotheses in the degree-one global
comparison criterion.  The sole remaining geometric input is the classical theorem that chains
small for an open cover include into all singular chains by a chain-homotopy equivalence.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Closed locally finite patching makes the actual global unit surjective in every degree. -/
theorem globalUnitSurjective [NormalSpace X] [ParacompactSpace X] (n : ℕ) :
    GlobalUnitSurjective X A n :=
  globalCochainUnit_surjective X A n

/-- On a normal paracompact space, the degree-one global comparison is an isomorphism once the
classical cover-small chain equivalences are supplied. -/
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
