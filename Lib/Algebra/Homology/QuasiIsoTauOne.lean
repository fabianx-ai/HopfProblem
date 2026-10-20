/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The first term of a morphism of short exact sequences of complexes

Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃` says that for a morphism
`φ : S₁ ⟶ S₂` of short exact short complexes of homological complexes, if `φ.τ₁` and `φ.τ₂` are
quasi-isomorphisms then so is `φ.τ₃` (its docstring announces the other cases as future work).
This file supplies the companion for the *first* term: if `φ.τ₂` and `φ.τ₃` are
quasi-isomorphisms then so is `φ.τ₁` (`quasiIso_τ₁`), by the same four-lemma arguments on the
windows `H_i X₂ → H_i X₃ → H_j X₁ → H_j X₂` and `H_i X₃ → H_j X₁ → H_j X₂ → H_j X₃` of the two long
exact sequences (`c.Rel i j`), and on `0 → H_j X₁ → H_j X₂ → H_j X₃` when `j` has no predecessor.

It is used for cohomological excision: the dual of a short exact sequence of chain complexes
`0 → C(A) → C(X) → C(X, A) → 0` has the relative cochains as its *first* term.

## Main results

* `HomologicalComplex.HomologySequence.mono_homologyMap_τ₁`, `epi_homologyMap_τ₁`,
  `isIso_homologyMap_τ₁`, `quasiIso_τ₁`.

## References

* `Mathlib/Algebra/Homology/HomologySequenceLemmas.lean` (the `τ₃` versions)

## Tags

five lemma, long exact sequence, quasi-isomorphism
-/

@[expose] public section

open CategoryTheory ComposableArrows Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex

namespace HomologySequence

include hS₁ hS₂

/-- If `H_i(φ.τ₂)` is an epimorphism and `H_i(φ.τ₃)`, `H_j(φ.τ₂)` are monomorphisms for every
`i` with `c.Rel i j`, then `H_j(φ.τ₁)` is a monomorphism. -/
lemma mono_homologyMap_τ₁ (j : ι)
    (h₂ : Mono (homologyMap φ.τ₂ j))
    (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₂ i))
    (h₄ : ∀ i, c.Rel i j → Mono (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₁ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δlast
    · exact h₃ i hij
    · exact h₄ i hij
    · exact h₂
  · have := hS₁.mono_f
    have hmono : Mono (homologyMap S₁.f j) := mono_homologyMap_of_mono_of_not_rel S₁.f j (by
      intro i hi
      exact hj ⟨i, hi⟩)
    have eq : homologyMap φ.τ₁ j ≫ homologyMap S₂.f j = homologyMap S₁.f j ≫ homologyMap φ.τ₂ j := by
      rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₁₂]
    have : Mono (homologyMap S₁.f j ≫ homologyMap φ.τ₂ j) := mono_comp _ _
    rw [← eq] at this
    exact mono_of_mono (homologyMap φ.τ₁ j) (homologyMap S₂.f j)

set_option backward.defeqAttrib.useBackward true in
/-- If `H_j(φ.τ₂)` is an epimorphism, `H_j(φ.τ₃)` a monomorphism and `H_i(φ.τ₃)` an epimorphism
for every `i` with `c.Rel i j`, then `H_j(φ.τ₁)` is an epimorphism. -/
lemma epi_homologyMap_τ₁ (j : ι)
    (h₂ : Epi (homologyMap φ.τ₂ j))
    (h₃ : Mono (homologyMap φ.τ₃ j))
    (h₄ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i)) :
    Epi (homologyMap φ.τ₁ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₄ i hij
    · exact h₂
    · exact h₃
  · have := hS₂.mono_f
    have hmono : Mono (homologyMap S₂.f j) := mono_homologyMap_of_mono_of_not_rel S₂.f j (by
      intro i hi
      exact hj ⟨i, hi⟩)
    refine ShortComplex.epi_of_mono_of_epi_of_mono
      ((homologyFunctor C _ j).mapShortComplex.map φ) (hS₁.homology_exact₂ j) hmono h₂ h₃

/-- If `H_j(φ.τ₂)` is an isomorphism, `H_j(φ.τ₃)` a monomorphism, and `H_i(φ.τ₂)` an epimorphism
and `H_i(φ.τ₃)` an isomorphism for every `i` with `c.Rel i j`, then `H_j(φ.τ₁)` is an
isomorphism. -/
lemma isIso_homologyMap_τ₁ (j : ι)
    (h₂ : IsIso (homologyMap φ.τ₂ j))
    (h₃ : Mono (homologyMap φ.τ₃ j))
    (h₄ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₂ i))
    (h₅ : ∀ i, c.Rel i j → IsIso (homologyMap φ.τ₃ i)) :
    IsIso (homologyMap φ.τ₁ j) := by
  have := mono_homologyMap_τ₁ φ hS₁ hS₂ j (IsIso.mono_of_iso _) h₄ (fun i hij => by
    have := h₅ i hij
    infer_instance)
  have := epi_homologyMap_τ₁ φ hS₁ hS₂ j inferInstance h₃ (fun i hij => by
    have := h₅ i hij
    infer_instance)
  apply isIso_of_mono_of_epi

/-- **Two out of three for the first term**: if `φ.τ₂` and `φ.τ₃` are quasi-isomorphisms, so is
`φ.τ₁`. -/
lemma quasiIso_τ₁ (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_τ₁ φ hS₁ hS₂ j inferInstance inferInstance
    (fun i _ => inferInstance) (fun i _ => inferInstance)

end HomologySequence

end HomologicalComplex
