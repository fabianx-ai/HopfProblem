/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1
public import Lib.Topology.Sheaves.SingularCochainSheaf.AugmentationMono
public import Lib.Topology.Sheaves.SingularCochainSheaf.LocalExactH1

/-!
# The singular-cochain resolution of the constant sheaf in low degrees

On a locally contractible space the augmented complex `0 → A_X → 𝒮^0 → 𝒮^1 → 𝒮^2` is exact
(Bredon, *Sheaf Theory* III.1).  This is the three-term window of the resolution of the constant
sheaf by sheafified singular cochains, in the form required to compute `H¹`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The three-term window `0 → A_X → 𝒮^0 → 𝒮^1 → 𝒮^2` of the singular-cochain resolution of the
constant sheaf on a locally contractible space (Bredon, *Sheaf Theory* III.1). -/
def resolutionH1 (hLC : LocallyContractibleSpace X) :
    CategoryTheory.Abelian.Ext.AcyclicResolutionH1
      (C := TopCat.Sheaf AddCommGrpCat.{0} X) where
  F := TopCat.ConstantSheaf.sheaf X A
  complex := (complexSheaf X A).sc' 0 1 2
  ι := sheafAugmentation X A
  zero := sheafAugmentation_d X A
  initial_exact := initialComplex_exact X A hLC
  exact :=
    ((complexSheaf X A).exactAt_iff' 0 1 2
      ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))).mp
        (complexSheaf_exactAt_one X A hLC)
  mono_ι := sheafAugmentation_mono X A

end TopCat.SingularCochainSheaf
