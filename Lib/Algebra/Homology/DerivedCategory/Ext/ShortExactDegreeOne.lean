/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Degree-one cohomology from a short exact sequence

For a short exact sequence `0 ⟶ F ⟶ G ⟶ Q ⟶ 0`, the covariant long exact
`Ext` sequence identifies `Ext¹(P, F)` with the cokernel of
`Ext⁰(P, G) ⟶ Ext⁰(P, Q)` whenever `Ext¹(P, G)` vanishes.  This is the low-degree
counterpart of the usual acyclic-quotient comparison in degrees at least two.

The result is useful for a constructible sheaf included in an ambient extension whose quotient
is a sum of skyscraper sheaves: after the ambient degree-one group has been computed, the remaining
calculation is the explicit degree-zero specialization matrix.

This FREE owner proves only the abstract kernel, quotient, and vanishing criteria supplied by the
covariant Ext long exact sequence. It introduces no sheaf, constructibility, spectral-sequence,
geometric, or application-specific assertion.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

universe w v u

namespace CategoryTheory.Abelian.Ext

open CategoryTheory CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The degree-zero map into the middle object, with codomain restricted to the kernel of the
degree-zero quotient map. -/
def postcompFZeroToKerPostcompG
    (P : C) (S : ShortComplex C) :
    Ext P S.X₁ 0 →+
      ((mk₀ S.g).postcomp P (add_zero 0)).ker :=
  ((mk₀ S.f).postcomp P (add_zero 0)).codRestrict
    ((mk₀ S.g).postcomp P (add_zero 0)).ker (fun x ↦ by
      change
        (x.comp (mk₀ S.f) (add_zero 0)).comp
            (mk₀ S.g) (add_zero 0) = 0
      simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀,
        S.zero, mk₀_zero, comp_zero])

/-- Exactness in degree zero identifies the subobject's `Ext⁰` with the kernel of the
degree-zero quotient map. -/
theorem postcompFZeroToKerPostcompG_bijective
    (P : C) {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Bijective (postcompFZeroToKerPostcompG P S) := by
  let _ : Mono S.f := hS.mono_f
  constructor
  · intro x y hxy
    apply postcomp_mk₀_injective_of_mono P S.f
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ :=
      covariant_sequence_exact₂ P hS y.1 y.2
    exact ⟨x, Subtype.ext hx⟩

/-- Canonical kernel coordinate for the degree-zero group of the subobject in a short exact
sequence. -/
noncomputable def extZeroEquivKerPostcompG
    (P : C) {S : ShortComplex C} (hS : S.ShortExact) :
    Ext P S.X₁ 0 ≃+
      ((mk₀ S.g).postcomp P (add_zero 0)).ker :=
  AddEquiv.ofBijective (postcompFZeroToKerPostcompG P S)
    (postcompFZeroToKerPostcompG_bijective P hS)

/-- The kernel coordinate of `Ext⁰(P, X₁)` is postcomposition with the class of `S.f`. -/
@[simp]
theorem extZeroEquivKerPostcompG_apply
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    (x : Ext P S.X₁ 0) :
    (extZeroEquivKerPostcompG P hS x).1 =
      x.comp (mk₀ S.f) (add_zero 0) := rfl

/-- Exactness at `Ext⁰(P, Q)`: the image of the degree-zero quotient map is the kernel of the
connecting map to `Ext¹(P, F)`. -/
theorem range_postcomp_g_zero_eq_ker_connecting
    (P : C) {S : ShortComplex C} (hS : S.ShortExact) :
    ((mk₀ S.g).postcomp P (add_zero 0)).range =
      (hS.extClass.postcomp P (show 0 + 1 = 1 by rfl)).ker := by
  ext x
  change
    (x ∈ Set.range ((mk₀ S.g).postcomp P (add_zero 0))) ↔
      hS.extClass.postcomp P (show 0 + 1 = 1 by rfl) x = 0
  have h := covariant_sequence_exact₃' P hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact (h x).symm

/-- If `Ext¹(P, G)` vanishes, the connecting map `Ext⁰(P, Q) ⟶ Ext¹(P, F)` is
surjective. -/
theorem connecting_zero_one_surjective_of_subsingleton_middle
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₂ 1)] :
    Function.Surjective
      (hS.extClass.postcomp P (show 0 + 1 = 1 by rfl)) := by
  intro y
  have hy : y.comp (mk₀ S.f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨q, hq⟩ :=
    covariant_sequence_exact₁ (n₀ := 0) P hS y hy rfl
  exact ⟨q, hq⟩

/-- The degree-one group of the subobject is the quotient of the quotient object's degree-zero
group by the image of the middle object's degree-zero group. -/
noncomputable def quotientRangePostcompGEquivExtOne
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₂ 1)] :
    Ext P S.X₃ 0 ⧸ ((mk₀ S.g).postcomp P (add_zero 0)).range ≃+
      Ext P S.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (range_postcomp_g_zero_eq_ker_connecting P hS)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (hS.extClass.postcomp P (show 0 + 1 = 1 by rfl))
      (connecting_zero_one_surjective_of_subsingleton_middle P hS))

/-- On a quotient class, the degree-one equivalence is the connecting homomorphism. -/
@[simp]
theorem quotientRangePostcompGEquivExtOne_mk
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₂ 1)] (q : Ext P S.X₃ 0) :
    quotientRangePostcompGEquivExtOne P hS
        (QuotientAddGroup.mk q) =
      q.comp hS.extClass (show 0 + 1 = 1 by rfl) := rfl

/-- Under the same degree-one vanishing hypothesis on the middle object, the subobject's
degree-one group vanishes exactly when the degree-zero map from the middle object to the quotient
is surjective.  This is the precise low-column criterion used in constructible-sheaf page
computations. -/
theorem subsingleton_ext_one_iff_postcomp_g_zero_surjective
    (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₂ 1)] :
    Subsingleton (Ext P S.X₁ 1) ↔
      Function.Surjective ((mk₀ S.g).postcomp P (add_zero 0)) := by
  exact
    (Equiv.subsingleton_congr
      (quotientRangePostcompGEquivExtOne P hS).toEquiv).symm.trans
      (QuotientAddGroup.subsingleton_iff.trans AddMonoidHom.range_eq_top)

end CategoryTheory.Abelian.Ext
