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
also proves compatibility with a homeomorphic change of the cover's base, transport across equal
base points, and moving the base point by a lifted path, and records the resulting formulas for
ranges and cyclic subgroups.

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

/-- Postcomposing a principal quotient cover with a homeomorphism of its base preserves deck
monodromy after transporting the fundamental group along that homeomorphism. -/
theorem deckMonodromyHom_homeomorph_comp
    {Y : Type u} [TopologicalSpace Y]
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    (h : X ≃ₜ Y) {x : X} (e : p ⁻¹' {x})
    (gamma : FundamentalGroup X x) :
    deckMonodromyHom (hp.homeomorph_comp h)
        (⟨e.1, congrArg h e.2⟩ : (h ∘ p) ⁻¹' {h x})
        (FundamentalGroup.map ⟨h, h.continuous⟩ x gamma) =
      deckMonodromyHom hp e gamma := by
  change
    (((hp.homeomorph_comp h).fundamentalGroupToMulOpposite
      (⟨e.1, congrArg h e.2⟩ : (h ∘ p) ⁻¹' {h x})
      (FundamentalGroup.map ⟨h, h.continuous⟩ x gamma)).unop)⁻¹ =
    ((hp.fundamentalGroupToMulOpposite e gamma).unop)⁻¹
  congr 1
  apply hp.isCancelSMul.right_cancel _ _ e.1
  calc
    ((hp.homeomorph_comp h).fundamentalGroupToMulOpposite
          (⟨e.1, congrArg h e.2⟩ : (h ∘ p) ⁻¹' {h x})
          (FundamentalGroup.map ⟨h, h.continuous⟩ x gamma)).unop • e.1 =
        (((hp.homeomorph_comp h).isCoveringMap.monodromy
          (FundamentalGroup.map ⟨h, h.continuous⟩ x gamma)
          (⟨e.1, congrArg h e.2⟩ : (h ∘ p) ⁻¹' {h x})).1) :=
      (hp.homeomorph_comp h).unop_fundamentalGroupToMulOpposite_smul
    _ = (hp.isCoveringMap.monodromy gamma e).1 := by
      induction gamma using Path.Homotopic.Quotient.ind with
      | mk gamma =>
          let Gamma := hp.isCoveringMap.liftPath gamma e.1
            (gamma.source.trans e.2.symm)
          have hGamma :
              (hp.homeomorph_comp h).isCoveringMap.liftPath
                  (gamma.map h.continuous) e.1
                    ((gamma.map h.continuous).source.trans (congrArg h e.2).symm) =
                Gamma := by
            symm
            apply ((hp.homeomorph_comp h).isCoveringMap.eq_liftPath_iff' _).mpr
            constructor
            · funext t
              change h (p (Gamma t)) = h (gamma t)
              congr 1
              exact congrFun (hp.isCoveringMap.liftPath_lifts gamma e.1
                (gamma.source.trans e.2.symm)) t
            · exact hp.isCoveringMap.liftPath_zero gamma e.1
                (gamma.source.trans e.2.symm)
          exact congrArg (fun f ↦ f 1) hGamma
    _ = (hp.fundamentalGroupToMulOpposite e gamma).unop • e.1 :=
      hp.unop_fundamentalGroupToMulOpposite_smul.symm

/-- Regard a point of a cover fibre as lying over an equal base point. -/
def fiberTransport {p : E → X} {x y : X} (hxy : x = y)
    (e : p ⁻¹' {x}) : p ⁻¹' {y} :=
  ⟨e.1, by simpa only [Set.mem_preimage, Set.mem_singleton_iff, ← hxy] using e.2⟩

/-- Transporting both a fibre point and a fundamental-group class across an equality of base
points preserves deck monodromy. -/
theorem deckMonodromyHom_fiberTransport
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x y : X} (hxy : x = y) (e : p ⁻¹' {x})
    (gamma : FundamentalGroup X x) :
    deckMonodromyHom hp (fiberTransport hxy e)
        (FundamentalGroup.fromPath
          ((FundamentalGroup.toPath gamma).cast hxy.symm hxy.symm)) =
      deckMonodromyHom hp e gamma := by
  subst y
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  congr 2

/-- Moving the chosen fibre point by lifting a path transports deck monodromy by whiskering the
downstairs loop with that path. -/
theorem deckMonodromyHom_liftedPath
    {p : E → X} (hp : IsQuotientCoveringMap p G)
    {x y : X} (τ : Path x y) (e : p ⁻¹' {x}) (γ : FundamentalGroup X y) :
    let e' := hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk τ) e
    deckMonodromyHom hp e' γ =
      deckMonodromyHom hp e
        ((Path.Homotopic.Quotient.mk τ).trans
          (γ.trans (Path.Homotopic.Quotient.mk τ).symm)) := by
  dsimp only
  change
    ((hp.fundamentalGroupToMulOpposite
      (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk τ) e) γ).unop)⁻¹ =
      ((hp.fundamentalGroupToMulOpposite e
        ((Path.Homotopic.Quotient.mk τ).trans
          (γ.trans (Path.Homotopic.Quotient.mk τ).symm))).unop)⁻¹
  let e' := hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk τ) e
  have hback :
      hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk τ).symm
          e' = e := by
    have h := hp.isCoveringMap.monodromy_trans_apply
      (Path.Homotopic.Quotient.mk τ)
      (Path.Homotopic.Quotient.mk τ).symm e
    rw [Path.Homotopic.Quotient.trans_symm,
      hp.isCoveringMap.monodromy_refl] at h
    exact h.symm
  have hopp :
      hp.fundamentalGroupToMulOpposite e
          ((Path.Homotopic.Quotient.mk τ).trans
            (γ.trans (Path.Homotopic.Quotient.mk τ).symm)) =
        hp.fundamentalGroupToMulOpposite e' γ := by
    apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
    change
      (hp.fundamentalGroupToMulOpposite e' γ).unop • e.1 =
        (hp.isCoveringMap.monodromy
          ((Path.Homotopic.Quotient.mk τ).trans
            (γ.trans (Path.Homotopic.Quotient.mk τ).symm)) e).1
    rw [hp.isCoveringMap.monodromy_trans_apply,
      hp.isCoveringMap.monodromy_trans_apply]
    change
      (hp.fundamentalGroupToMulOpposite e' γ).unop • e.1 =
        (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk τ).symm
          (hp.isCoveringMap.monodromy γ e')).1
    have hγ :
        hp.isCoveringMap.monodromy γ e' =
          hp.toPermFiber y (hp.fundamentalGroupToMulOpposite e' γ).unop e' := by
      apply Subtype.ext
      exact hp.unop_fundamentalGroupToMulOpposite_smul.symm
    rw [hγ, hp.monodromy_toPermFiber]
    exact congrArg
      (fun z : p ⁻¹' {x} ↦
        (hp.fundamentalGroupToMulOpposite e' γ).unop • z.1) hback |>.symm
  exact congrArg Inv.inv (congrArg MulOpposite.unop hopp.symm)

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
