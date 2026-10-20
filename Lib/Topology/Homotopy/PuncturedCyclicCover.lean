/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.TwoSimplyConnectedCover

/-!
# A two-chart cyclicity criterion

A space covered by two simply connected opens has cyclic fundamental group when their overlap has
at most the component of the base point and one other component.  Although this criterion is used
for punctured-space calculations, its statement and proof are generic.
-/

@[expose] public noncomputable section

set_option warningAsError true
set_option autoImplicit false

open Set TopologicalSpace

namespace FundamentalGroup.VanKampen.Cocone.TwoSimplyConnectedCover

/-- If the overlap of a two-simply-connected-open cover has only the component of the base point
and the component of `x`, then the switch class at `x` generates the whole fundamental group. -/
theorem zpowers_switchClass_eq_top
    {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoSimplyConnectedCover X)
    (x : X) (hxU : x ∈ D.U) (hxV : x ∈ D.V)
    (hcomponents :
      ∀ y (_hyU : y ∈ D.U) (_hyV : y ∈ D.V),
        JoinedIn ((D.U : Set X) ∩ D.V) D.base y ∨
          JoinedIn ((D.U : Set X) ∩ D.V) x y) :
    Subgroup.zpowers (D.switchClass x hxU hxV) = ⊤ := by
  apply D.subgroup_eq_top_of_switchClass_mem
  intro y hyU hyV
  rcases hcomponents y hyU hyV with hbase | hx
  · have hswitch :=
      D.switchClass_eq_of_joinedIn D.baseU D.baseV hyU hyV hbase
    rw [D.switchClass_base] at hswitch
    rw [← hswitch]
    exact Subgroup.one_mem _
  · have hswitch := D.switchClass_eq_of_joinedIn hxU hxV hyU hyV hx
    rw [← hswitch]
    simpa only [zpow_one] using
      (Subgroup.zpow_mem_zpowers (D.switchClass x hxU hxV) (1 : ℤ))

end FundamentalGroup.VanKampen.Cocone.TwoSimplyConnectedCover
