/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Collapse of short additive-subgroup filtrations

Nested additive subgroups coincide when their quotient is trivial. In particular, a two-step
filtration with both successive quotients trivial has bottom term equal to the ambient group.
-/

@[expose] public section

namespace AddSubgroup

/-- If `H ≤ K` and the quotient `K / H` is trivial, then `H = K`. -/
theorem eq_of_le_of_quotient_subsingleton {A : Type*} [AddCommGroup A]
    {H K : AddSubgroup A} (hHK : H ≤ K)
    (hquot : Subsingleton (K ⧸ H.addSubgroupOf K)) : H = K := by
  apply le_antisymm hHK
  exact AddSubgroup.addSubgroupOf_eq_top.mp
    (QuotientAddGroup.addSubgroup_eq_top_of_subsingleton _ hquot)

/-- A two-step filtration with trivial successive quotients has bottom term equal to the ambient
group. -/
theorem eq_top_of_le_of_quotient_subsingleton {A : Type*} [AddCommGroup A]
    (F₀ F₁ : AddSubgroup A) (h₀₁ : F₀ ≤ F₁)
    (h₁₀ : Subsingleton (F₁ ⧸ F₀.addSubgroupOf F₁))
    (hA₁ : Subsingleton (A ⧸ F₁)) : F₀ = ⊤ := by
  exact (eq_of_le_of_quotient_subsingleton h₀₁ h₁₀).trans
    (QuotientAddGroup.addSubgroup_eq_top_of_subsingleton F₁ hA₁)

end AddSubgroup
