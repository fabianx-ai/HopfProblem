/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Explicit cycle classes in the homology of a short complex of abelian groups

Cycles modulo boundaries: for a short complex `S` of abelian groups, a cocycle `z : S.X₂` with
`S.g z = 0` represents a class `ShortComplex.shortCycleClass S z hz : S.homology`, every class
arises this way, the class is natural in maps of short complexes, and it vanishes exactly when
`z` is a boundary.  This is the elementwise description of `ShortComplex.abHomologyIso`.

## References

* [A. Hatcher, *Algebraic topology*][hatcher02], §2.1 (cycles modulo boundaries).
* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §1.1; compare
  `ShortComplex.ab_exact_iff` in Mathlib.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe v

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Element-free compatibility missing beside `ShortComplex.abHomologyIso`. -/
theorem ab_homologyπ_comp_abHomologyIso_hom
    (S : ShortComplex AddCommGrpCat.{v}) :
    S.homologyπ ≫ S.abHomologyIso.hom =
      S.abCyclesIso.hom ≫
        AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) := by
  exact S.abLeftHomologyData.homologyπ_comp_homologyIso_hom

/-- An explicit cocycle class in the categorical homology of a short
complex of abelian groups. -/
def shortCycleClass (S : ShortComplex AddCommGrpCat.{v}) (z : S.X₂)
    (hz : S.g z = 0) : S.homology :=
  S.homologyπ (S.abCyclesIso.inv ⟨z, hz⟩)

/-- Homology maps preserve explicit cocycle representatives. -/
theorem shortHomologyMap_cycleClass {S T : ShortComplex AddCommGrpCat.{v}}
    (φ : S ⟶ T) (z : S.X₂) (hz : S.g z = 0) (hφz : T.g (φ.τ₂ z) = 0) :
    ShortComplex.homologyMap φ (shortCycleClass S z hz) =
      shortCycleClass T (φ.τ₂ z) hφz := by
  have hc : ShortComplex.cyclesMap φ (S.abCyclesIso.inv ⟨z, hz⟩) =
      T.abCyclesIso.inv ⟨φ.τ₂ z, hφz⟩ := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, ShortComplex.abCyclesIso_inv_apply_iCycles,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
  unfold shortCycleClass
  rw [← ConcreteCategory.comp_apply, ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hc]

/-- Every homology class of a short complex of abelian groups has a cocycle representative. -/
theorem shortCycleClass_surjective (S : ShortComplex AddCommGrpCat.{v})
    (x : S.homology) : ∃ (z : S.X₂) (hz : S.g z = 0),
      shortCycleClass S z hz = x := by
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  let z := S.abCyclesIso.hom y
  refine ⟨z.val, z.property, ?_⟩
  exact congrArg S.homologyπ
    (S.abCyclesIso.addCommGroupIsoToAddEquiv.symm_apply_apply y)

/-- Under `abHomologyIso`, the cocycle class is the class of the cocycle in cycles modulo
boundaries. -/
theorem shortCycleClass_quotient (S : ShortComplex AddCommGrpCat.{v})
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

/-- A cocycle class vanishes exactly when the cocycle is a boundary. -/
theorem shortCycleClass_eq_zero_iff (S : ShortComplex AddCommGrpCat.{v})
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

end CategoryTheory.ShortComplex
