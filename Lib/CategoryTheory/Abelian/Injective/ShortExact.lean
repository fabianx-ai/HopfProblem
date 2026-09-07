/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Embedding short exact sequences into injective biproduct rows

Specified embeddings of the endpoints into injectives extend to a compatible
embedding of the middle object into their biproduct.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory CategoryTheory.Limits

/-- Extend the specified left endpoint embedding across the first arrow, and pair
that extension with the right endpoint embedding composed with the second arrow.
Both sequence squares commute. To prove the resulting middle map monic, project
a map in its kernel onto the right summand and cancel the right embedding. Exactness
then factors it through the first arrow. Projection onto the left summand and the
extension equation allow cancellation of the left embedding, so the original map
is zero. This is the specified-endpoint construction of PD-L05. -/
theorem exists_injective_biprod_embedding
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    {I K : C} [Injective I] [Injective K]
    (α : S.X₁ ⟶ I) [Mono α] (γ : S.X₃ ⟶ K) [Mono γ] :
    ∃ (x : S.X₂ ⟶ I) (β : S.X₂ ⟶ I ⊞ K),
      S.f ≫ x = α ∧
      β = biprod.lift x (S.g ≫ γ) ∧
      S.f ≫ β = α ≫ biprod.inl ∧
      β ≫ biprod.snd = S.g ≫ γ ∧
      Mono β := by
  let : Mono S.f := hS.mono_f
  let x : S.X₂ ⟶ I := Injective.factorThru α S.f
  have hx : S.f ≫ x = α := Injective.comp_factorThru α S.f
  let β : S.X₂ ⟶ I ⊞ K := biprod.lift x (S.g ≫ γ)
  have hfst : β ≫ biprod.fst = x := biprod.lift_fst x (S.g ≫ γ)
  have hsnd : β ≫ biprod.snd = S.g ≫ γ := biprod.lift_snd x (S.g ≫ γ)
  have hleft : S.f ≫ β = α ≫ biprod.inl := by
    apply biprod.hom_ext
    · simp only [Category.assoc, hfst, biprod.inl_fst, Category.comp_id, hx]
    · simp only [Category.assoc, hsnd, biprod.inl_snd, comp_zero]
      rw [← Category.assoc, S.zero, zero_comp]
  have hmono : Mono β := by
    apply Preadditive.mono_of_cancel_zero
    intro T t ht
    have htγ : (t ≫ S.g) ≫ γ = 0 := by
      calc
        (t ≫ S.g) ≫ γ = (t ≫ β) ≫ biprod.snd := by
          rw [Category.assoc, Category.assoc, hsnd]
        _ = 0 := by rw [ht, zero_comp]
    have htg : t ≫ S.g = 0 := zero_of_comp_mono γ htγ
    let s : T ⟶ S.X₁ := hS.exact.lift t htg
    have hs : s ≫ S.f = t := hS.exact.lift_f t htg
    have htx : t ≫ x = 0 := by
      calc
        t ≫ x = (t ≫ β) ≫ biprod.fst := by rw [Category.assoc, hfst]
        _ = 0 := by rw [ht, zero_comp]
    have hsα : s ≫ α = 0 := by
      rw [← hx, ← Category.assoc, hs, htx]
    have hs0 : s = 0 := zero_of_comp_mono α hsα
    rw [← hs, hs0, zero_comp]
  exact ⟨x, β, hx, rfl, hleft, hsnd, hmono⟩

end CategoryTheory.ShortComplex.ShortExact
