/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Degree-two Ext across a short exact sequence with acyclic quotient

For a short exact sequence `0 ⟶ F ⟶ G ⟶ Q ⟶ 0`, the covariant long exact
Ext sequence shows that `Ext²(P,F) ⟶ Ext²(P,G)` is an isomorphism whenever
`Ext¹(P,Q)` and `Ext²(P,Q)` vanish.  This is the degree-two form of the
standard acyclic-quotient comparison.

The construction below is the literal map induced by `F ⟶ G`; it does not
choose an unrelated equivalence between the two Ext groups.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- In degree two, inclusion of the subobject in a short exact sequence is
bijective on Ext when the quotient is acyclic in degrees one and two. -/
theorem postcomp_f_two_bijective_of_subsingleton_quotient
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₃ 1)] [Subsingleton (Ext P S.X₃ 2)] :
    Function.Bijective ((mk₀ S.f).postcomp P (add_zero 2)) := by
  constructor
  · intro x y hxy
    change x.comp (mk₀ S.f) (add_zero 2) =
      y.comp (mk₀ S.f) (add_zero 2) at hxy
    have hzero :
        (x - y).comp (mk₀ S.f) (add_zero 2) = 0 := by
      simp only [sub_eq_add_neg, add_comp, neg_comp, hxy, add_neg_cancel]
    obtain ⟨q, hq⟩ :=
      covariant_sequence_exact₁ P hS (x - y) hzero (n₀ := 1) rfl
    have hqzero : q = 0 := Subsingleton.elim _ _
    rw [hqzero, zero_comp] at hq
    exact sub_eq_zero.mp hq.symm
  · intro x
    have hzero : x.comp (mk₀ S.g) (add_zero 2) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := covariant_sequence_exact₂ P hS x hzero
    exact ⟨y, hy⟩

/-- Canonical degree-two Ext equivalence induced by the inclusion in a short
exact sequence whose quotient is acyclic in degrees one and two. -/
def extTwoEquivMiddleOfSubsingletonQuotient
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₃ 1)] [Subsingleton (Ext P S.X₃ 2)] :
    Ext P S.X₁ 2 ≃+ Ext P S.X₂ 2 :=
  AddEquiv.ofBijective ((mk₀ S.f).postcomp P (add_zero 2))
    (postcomp_f_two_bijective_of_subsingleton_quotient P hS)

@[simp]
theorem extTwoEquivMiddleOfSubsingletonQuotient_apply
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₃ 1)] [Subsingleton (Ext P S.X₃ 2)]
    (x : Ext P S.X₁ 2) :
    extTwoEquivMiddleOfSubsingletonQuotient P hS x =
      x.comp (mk₀ S.f) (add_zero 2) :=
  rfl

end CategoryTheory.Abelian.Ext

end
