/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# A homology-isomorphism criterion from cycle lifts

For a map of cochain complexes of abelian groups, exact lifts of closed representatives give
surjectivity on positive-degree homology, while detection of actual boundaries gives injectivity.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.HomologicalComplex

private def shortCycleClass (S : ShortComplex AddCommGrpCat.{0}) (z : S.X₂)
    (hz : S.g z = 0) : S.homology :=
  S.homologyπ (S.abCyclesIso.inv ⟨z, hz⟩)

private theorem shortHomologyMap_cycleClass {S T : ShortComplex AddCommGrpCat.{0}}
    (f : S ⟶ T) (z : S.X₂) (hz : S.g z = 0) (hfz : T.g (f.τ₂ z) = 0) :
    ShortComplex.homologyMap f (shortCycleClass S z hz) =
      shortCycleClass T (f.τ₂ z) hfz := by
  have hc : ShortComplex.cyclesMap f (S.abCyclesIso.inv ⟨z, hz⟩) =
      T.abCyclesIso.inv ⟨f.τ₂ z, hfz⟩ := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, ShortComplex.abCyclesIso_inv_apply_iCycles,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
  unfold shortCycleClass
  rw [← ConcreteCategory.comp_apply, ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hc]

private theorem shortCycleClass_surjective (S : ShortComplex AddCommGrpCat.{0})
    (x : S.homology) : ∃ (z : S.X₂) (hz : S.g z = 0),
      shortCycleClass S z hz = x := by
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  let z := S.abCyclesIso.hom y
  refine ⟨z.val, z.property, ?_⟩
  exact congrArg S.homologyπ
    (S.abCyclesIso.addCommGroupIsoToAddEquiv.symm_apply_apply y)

private theorem shortCycleClass_quotient (S : ShortComplex AddCommGrpCat.{0})
    (z : S.X₂) (hz : S.g z = 0) :
    S.abHomologyIso.hom (shortCycleClass S z hz) =
      QuotientAddGroup.mk' S.abToCycles.range ⟨z, hz⟩ := by
  have h : S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) := by
    change S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
      S.abLeftHomologyData.homologyIso.hom = S.abLeftHomologyData.π
    rw [S.abLeftHomologyData.homologyπ_comp_homologyIso_hom,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact ConcreteCategory.congr_hom h ⟨z, hz⟩

private theorem shortCycleClass_eq_zero_iff (S : ShortComplex AddCommGrpCat.{0})
    (z : S.X₂) (hz : S.g z = 0) :
    shortCycleClass S z hz = 0 ↔ ∃ b : S.X₁, S.f b = z := by
  constructor
  · intro h
    have hq : QuotientAddGroup.mk' S.abToCycles.range ⟨z, hz⟩ = 0 :=
      (shortCycleClass_quotient S z hz).symm.trans
        ((congrArg S.abHomologyIso.hom h).trans S.abHomologyIso.hom.hom.map_zero)
    have hb : (⟨z, hz⟩ : S.g.hom.ker) ∈ S.abToCycles.range :=
      (QuotientAddGroup.eq_zero_iff _).mp hq
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hq : QuotientAddGroup.mk' S.abToCycles.range ⟨z, hz⟩ = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨b, Subtype.ext hb⟩
    apply (AddCommGrpCat.mono_iff_injective S.abHomologyIso.hom).mp inferInstance
    exact ((shortCycleClass_quotient S z hz).trans hq).trans
      S.abHomologyIso.hom.hom.map_zero.symm

private theorem shortHomologyMap_surjective_of_cycle_lifts
    {S T : ShortComplex AddCommGrpCat.{0}} (f : S ⟶ T)
    (hlift : ∀ (z : T.X₂), T.g z = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ f.τ₂ x = z) :
    Function.Surjective (ShortComplex.homologyMap f) := by
  intro a
  obtain ⟨z, hz, rfl⟩ := shortCycleClass_surjective T a
  obtain ⟨x, hx, rfl⟩ := hlift z hz
  exact ⟨shortCycleClass S x hx, shortHomologyMap_cycleClass f x hx hz⟩

private theorem shortHomologyMap_injective_of_boundary_detection
    {S T : ShortComplex AddCommGrpCat.{0}} (f : S ⟶ T)
    (hdetect : ∀ (x : S.X₂), S.g x = 0 →
      (∃ b : T.X₁, T.f b = f.τ₂ x) → ∃ a : S.X₁, S.f a = x) :
    Function.Injective (ShortComplex.homologyMap f) := by
  apply (injective_iff_map_eq_zero (ShortComplex.homologyMap f).hom).mpr
  intro a ha
  obtain ⟨x, hx, rfl⟩ := shortCycleClass_surjective S a
  have hfx : T.g (f.τ₂ x) = 0 :=
    (ConcreteCategory.congr_hom f.comm₂₃ x).trans (by
      change f.τ₃ (S.g x) = 0
      rw [hx]
      exact f.τ₃.hom.map_zero)
  rw [shortHomologyMap_cycleClass f x hx hfx] at ha
  exact (shortCycleClass_eq_zero_iff S x hx).mpr
    (hdetect x hx ((shortCycleClass_eq_zero_iff T (f.τ₂ x) hfx).mp ha))

private theorem sc_closed_iff (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n : ℕ) (x : K.X (n + 1)) :
    (K.sc (n + 1)).g x = 0 ↔ K.d (n + 1) (n + 2) x = 0 := by
  change K.d (n + 1) ((ComplexShape.up ℕ).next (n + 1)) x = 0 ↔ _
  rw [CochainComplex.next]
  rfl

private theorem sc_boundary_iff (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n : ℕ) (x : K.X (n + 1)) :
    (∃ a : (K.sc (n + 1)).X₁, (K.sc (n + 1)).f a = x) ↔
      ∃ a : K.X n, K.d n (n + 1) a = x := by
  change (∃ a : K.X ((ComplexShape.up ℕ).prev (n + 1)),
    K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) a = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

/-- Exact lifts of closed cochains and detection of actual boundaries make a positive-degree
homology map an isomorphism. -/
theorem isIso_homologyMap_succ_of_cycle_lifts
    {K L : CochainComplex AddCommGrpCat.{0} ℕ} (f : K ⟶ L) (n : ℕ)
    (hlift : ∀ (z : L.X (n + 1)), L.d (n + 1) (n + 2) z = 0 →
      ∃ x : K.X (n + 1), K.d (n + 1) (n + 2) x = 0 ∧ f.f (n + 1) x = z)
    (hdetect : ∀ (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      (∃ b : L.X n, L.d n (n + 1) b = f.f (n + 1) x) →
        ∃ a : K.X n, K.d n (n + 1) a = x) :
    IsIso (HomologicalComplex.homologyMap f (n + 1)) := by
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat
    (ComplexShape.up ℕ) (n + 1)).map f
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨shortHomologyMap_injective_of_boundary_detection φ (by
      intro x hx hb
      exact (sc_boundary_iff K n x).mpr
        (hdetect x ((sc_closed_iff K n x).mp hx)
          ((sc_boundary_iff L n (f.f (n + 1) x)).mp hb))),
    shortHomologyMap_surjective_of_cycle_lifts φ (by
      intro z hz
      obtain ⟨x, hx, hfx⟩ := hlift z ((sc_closed_iff L n z).mp hz)
      exact ⟨x, (sc_closed_iff K n x).mpr hx, hfx⟩)⟩

end CategoryTheory.HomologicalComplex
