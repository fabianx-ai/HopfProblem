/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantProductH1
public import Lib.Topology.Sheaves.ConstantSheafH1

/-!
# Constant-sheaf H¹ of a contractible product

This file combines the natural constant-sheaf/singular-cochain comparison with homotopy
invariance of singular cohomology.  It proves that restriction to a based fibre of a product
with a contractible compact Hausdorff space is an isomorphism on native Ext-defined
constant-sheaf cohomology in degree one.

This is the degree-one case of homotopy invariance of constant-coefficient sheaf cohomology,
`H^n(S × X; A) ≅ H^n(X; A)` for contractible `S`; see Bredon, *Sheaf Theory*, II.11.12, and
cf. Iversen, *Cohomology of Sheaves*, III.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.ConstantProductH1

variable (S X : Type) [TopologicalSpace S] [TopologicalSpace X]
  [CompactSpace S] [T2Space S] [ContractibleSpace S]
  [CompactSpace X] [T2Space X]

/-- Pullback to a based fibre is an isomorphism on native Ext-defined constant-sheaf
cohomology in degree one. -/
theorem nativePullback_basedFibreInclusion_isIso
    (A : AddCommGrpCat.{0}) (s : S)
    (hProd : LocallyContractibleSpace (S × X))
    (hX : LocallyContractibleSpace X) :
    IsIso (TopCat.ConstantSheafCohomology.pullback
      (basedFibreInclusion S X s)
      (basedFibreInclusion_isClosedMap S X s)
      (basedFibreInclusion_finite_fibres S X s) A 1) := by
  obtain ⟨cX, cProd, hcomm⟩ :=
    TopCat.SingularCochainSheaf.exists_h1Comparison_natural
      (basedFibreInclusion S X s)
      (basedFibreInclusion_isClosedMap S X s)
      (basedFibreInclusion_finite_fibres S X s) A hX hProd
  exact nativePullback_isIso_of_comparison
    (basedFibreInclusion S X s)
    (basedFibreInclusion_isClosedMap S X s)
    (basedFibreInclusion_finite_fibres S X s) A cProd cX hcomm

end TopCat.ConstantProductH1
