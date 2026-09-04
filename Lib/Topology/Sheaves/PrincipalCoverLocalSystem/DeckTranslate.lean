/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.PrincipalCoverLocalSystem
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Deck translation and principal-cover monodromy

Changing the chosen point in a fibre by a deck transformation conjugates the corresponding
fundamental-group monodromy.  This file proves that formula first in Mathlib's opposite-group
convention and then for the inverse-normalized monodromy homomorphism into the deck group.  It
also records the resulting formulas for ranges and cyclic subgroups.

These are generic facts about principal quotient covers.  This file chooses no geometric family,
puncture, meridian, or component, and makes no claim about a local system, higher direct image,
Leray page, or spectral-sequence differential.
-/

@[expose] public section

open Set Topology TopologicalSpace

namespace PrincipalCoverLocalSystem

noncomputable section

universe uG u

variable {G : Type uG} {E X : Type u}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E]

theorem fundamentalGroupToMulOpposite_translate
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) (g : G) (γ : FundamentalGroup X x) :
    (hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ).unop =
      g * (hp.fundamentalGroupToMulOpposite e γ).unop * g⁻¹ := by
  have hprod :
      (hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ).unop * g =
        g * (hp.fundamentalGroupToMulOpposite e γ).unop := by
    apply hp.isCancelSMul.right_cancel _ _ e.1
    calc
      ((hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ).unop * g) • e.1 =
          (hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ).unop •
            (g • e.1) := mul_smul _ _ _
      _ = (hp.isCoveringMap.monodromy γ (hp.toPermFiber x g e)).1 :=
        hp.unop_fundamentalGroupToMulOpposite_smul
      _ = g • (hp.isCoveringMap.monodromy γ e).1 :=
        congrArg Subtype.val hp.monodromy_toPermFiber
      _ = g • ((hp.fundamentalGroupToMulOpposite e γ).unop • e.1) :=
        congrArg (g • ·) hp.unop_fundamentalGroupToMulOpposite_smul.symm
      _ = (g * (hp.fundamentalGroupToMulOpposite e γ).unop) • e.1 :=
        (mul_smul _ _ _).symm
  calc
    _ = ((hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ).unop * g) * g⁻¹ := by
      simp
    _ = (g * (hp.fundamentalGroupToMulOpposite e γ).unop) * g⁻¹ :=
      congrArg (· * g⁻¹) hprod

theorem inverseFundamentalGroupToMulOpposite_translate
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) (g : G) (γ : FundamentalGroup X x) :
    (hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ).unop⁻¹ =
      g * (hp.fundamentalGroupToMulOpposite e γ).unop⁻¹ * g⁻¹ := by
  rw [fundamentalGroupToMulOpposite_translate hp e g γ]
  simp only [mul_inv_rev, inv_inv]
  exact (mul_assoc _ _ _).symm

/-- Deck monodromy in the non-opposite group convention. -/
def deckMonodromyHom {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) : FundamentalGroup X x →* G :=
  (MulEquiv.inv' G).symm.toMonoidHom.comp (hp.fundamentalGroupToMulOpposite e)

theorem deckMonodromyHom_translate_apply
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) (g : G) (γ : FundamentalGroup X x) :
    deckMonodromyHom hp (hp.toPermFiber x g e) γ =
      g * deckMonodromyHom hp e γ * g⁻¹ := by
  exact inverseFundamentalGroupToMulOpposite_translate hp e g γ

theorem deckMonodromyHom_translate
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) (g : G) :
    deckMonodromyHom hp (hp.toPermFiber x g e) =
      (MulAut.conj g).toMonoidHom.comp (deckMonodromyHom hp e) := by
  ext γ
  change deckMonodromyHom hp (hp.toPermFiber x g e) γ =
    MulAut.conj g (deckMonodromyHom hp e γ)
  rw [MulAut.conj_apply]
  exact deckMonodromyHom_translate_apply hp e g γ

theorem deckMonodromyHom_translate_range
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) (g : G) :
    (deckMonodromyHom hp (hp.toPermFiber x g e)).range =
      (deckMonodromyHom hp e).range.map (MulAut.conj g).toMonoidHom := by
  rw [deckMonodromyHom_translate, MonoidHom.range_comp]

theorem map_conj_zpowers_inv_mul_mul (g a : G) :
    (Subgroup.zpowers (g⁻¹ * a * g)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers a := by
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (MulAut.conj g (g⁻¹ * a * g)) = Subgroup.zpowers a
  rw [MulAut.conj_apply]
  congr 1
  simp [mul_assoc]

end

end PrincipalCoverLocalSystem
