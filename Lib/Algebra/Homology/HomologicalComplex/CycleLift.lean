/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.ShortComplex.AbCycleClass
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# A homology-isomorphism criterion from cycle lifts

For a map of cochain complexes of abelian groups, exact lifts of closed representatives give
surjectivity on positive-degree homology, while detection of actual boundaries gives injectivity.

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

namespace CategoryTheory.HomologicalComplex

universe w


private theorem shortHomologyMap_surjective_of_cycle_lifts
    {S T : ShortComplex AddCommGrpCat.{w}} (f : S ⟶ T)
    (hlift : ∀ (z : T.X₂), T.g z = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ f.τ₂ x = z) :
    Function.Surjective (ShortComplex.homologyMap f) := by
  intro a
  obtain ⟨z, hz, rfl⟩ := ShortComplex.shortCycleClass_surjective T a
  obtain ⟨x, hx, rfl⟩ := hlift z hz
  exact ⟨ShortComplex.shortCycleClass S x hx, ShortComplex.shortHomologyMap_cycleClass f x hx hz⟩

private theorem shortHomologyMap_injective_of_boundary_detection
    {S T : ShortComplex AddCommGrpCat.{w}} (f : S ⟶ T)
    (hdetect : ∀ (x : S.X₂), S.g x = 0 →
      (∃ b : T.X₁, T.f b = f.τ₂ x) → ∃ a : S.X₁, S.f a = x) :
    Function.Injective (ShortComplex.homologyMap f) := by
  apply (injective_iff_map_eq_zero (ShortComplex.homologyMap f).hom).mpr
  intro a ha
  obtain ⟨x, hx, rfl⟩ := ShortComplex.shortCycleClass_surjective S a
  have hfx : T.g (f.τ₂ x) = 0 :=
    (ConcreteCategory.congr_hom f.comm₂₃ x).trans (by
      change f.τ₃ (S.g x) = 0
      rw [hx]
      exact f.τ₃.hom.map_zero)
  rw [ShortComplex.shortHomologyMap_cycleClass f x hx hfx] at ha
  exact (ShortComplex.shortCycleClass_eq_zero_iff S x hx).mpr
    (hdetect x hx ((ShortComplex.shortCycleClass_eq_zero_iff T (f.τ₂ x) hfx).mp ha))

private theorem sc_closed_iff (K : CochainComplex AddCommGrpCat.{w} ℕ)
    (n : ℕ) (x : K.X (n + 1)) :
    (K.sc (n + 1)).g x = 0 ↔ K.d (n + 1) (n + 2) x = 0 := by
  change K.d (n + 1) ((ComplexShape.up ℕ).next (n + 1)) x = 0 ↔ _
  rw [CochainComplex.next]
  rfl

private theorem sc_boundary_iff (K : CochainComplex AddCommGrpCat.{w} ℕ)
    (n : ℕ) (x : K.X (n + 1)) :
    (∃ a : (K.sc (n + 1)).X₁, (K.sc (n + 1)).f a = x) ↔
      ∃ a : K.X n, K.d n (n + 1) a = x := by
  change (∃ a : K.X ((ComplexShape.up ℕ).prev (n + 1)),
    K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) a = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

/-- Exact lifts of closed cochains and detection of actual boundaries make a positive-degree
homology map an isomorphism. -/
theorem isIso_homologyMap_succ_of_cycle_lifts
    {K L : CochainComplex AddCommGrpCat.{w} ℕ} (f : K ⟶ L) (n : ℕ)
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
