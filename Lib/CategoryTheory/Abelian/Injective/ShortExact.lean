/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The split target row of a specified componentwise monic embedding has injective
middle term. Its three component cokernels, with the arrows induced by the standard
biproduct inclusion and projection, form a short exact successor sequence.

Assemble the component cokernel universal properties into the lower row of the
snake diagram. The snake lemma gives middle exactness and the final epimorphism.
The preceding kernel is a kernel of the monic right endpoint embedding, hence zero;
the snake exactness at the first cokernel therefore gives the initial monomorphism.
The actual cokernel maps and both quotient squares are retained. This is PD-L06. -/
theorem injective_biprod_cokernel_successor
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    {I K : C} [Injective I] [Injective K]
    (α : S.X₁ ⟶ I) [Mono α] (γ : S.X₃ ⟶ K) [Mono γ]
    (β : S.X₂ ⟶ I ⊞ K) [Mono β]
    (hl : S.f ≫ β = α ≫ biprod.inl)
    (hr : β ≫ biprod.snd = S.g ≫ γ) :
    Injective (I ⊞ K) ∧
    (ShortComplex.mk (biprod.inl : I ⟶ I ⊞ K)
      (biprod.snd : I ⊞ K ⟶ K) biprod.inl_snd).ShortExact ∧
    ∃ (a : cokernel α ⟶ cokernel β) (b : cokernel β ⟶ cokernel γ),
      a = cokernel.map α β S.f biprod.inl hl.symm ∧
      b = cokernel.map β γ S.g biprod.snd hr ∧
      cokernel.π α ≫ a = biprod.inl ≫ cokernel.π β ∧
      cokernel.π β ≫ b = biprod.snd ≫ cokernel.π γ ∧
      ∃ (hab : a ≫ b = 0), (ShortComplex.mk a b hab).ShortExact := by
  let a : cokernel α ⟶ cokernel β := cokernel.map α β S.f biprod.inl hl.symm
  let b : cokernel β ⟶ cokernel γ := cokernel.map β γ S.g biprod.snd hr
  have ha : cokernel.π α ≫ a = biprod.inl ≫ cokernel.π β := cokernel.π_desc _ _ _
  have hb : cokernel.π β ≫ b = biprod.snd ≫ cokernel.π γ := cokernel.π_desc _ _ _
  have hab : a ≫ b = 0 := by
    apply (cancel_epi (cokernel.π α)).1
    rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc,
      biprod.inl_snd, zero_comp, comp_zero]
  let Q : ShortComplex C := ShortComplex.mk a b hab
  let E : ShortComplex C := ShortComplex.mk (biprod.inl : I ⟶ I ⊞ K)
    (biprod.snd : I ⊞ K ⟶ K) biprod.inl_snd
  let φ : S ⟶ E := ShortComplex.homMk α β γ hl.symm hr
  let q : E ⟶ Q :=
    ShortComplex.homMk (cokernel.π α) (cokernel.π β) (cokernel.π γ) ha hb
  have w : φ ≫ q = 0 := by
    ext
    · exact cokernel.condition α
    · exact cokernel.condition β
    · exact cokernel.condition γ
  have hq : IsColimit (CokernelCofork.ofπ q w) := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ w).symm
        (cokernelIsCokernel α)
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ w).symm
        (cokernelIsCokernel β)
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ w).symm
        (cokernelIsCokernel γ)
  let D : ShortComplex.SnakeInput C :=
    { L₀ := kernel φ
      L₁ := S
      L₂ := E
      L₃ := Q
      v₀₁ := kernel.ι φ
      v₁₂ := φ
      v₂₃ := q
      w₀₂ := kernel.condition φ
      w₁₃ := w
      h₀ := kernelIsKernel φ
      h₃ := hq
      L₁_exact := hS.exact
      epi_L₁_g := hS.epi_g
      L₂_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct I K).shortExact.exact
      mono_L₂_f := (inferInstance : Mono (biprod.inl : I ⟶ I ⊞ K)) }
  have hExact : Q.Exact := D.L₃_exact
  have hEpi : Epi Q.g := by
    let : Epi D.L₂.g := (inferInstance : Epi (biprod.snd : I ⊞ K ⟶ K))
    change Epi D.L₃.g
    infer_instance
  have hMono : Mono Q.f := by
    let : Mono D.v₁₂.τ₃ := (inferInstance : Mono γ)
    have hz : IsZero D.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono D.h₀τ₃
    exact D.L₂'_exact.mono_g (hz.eq_of_src _ _)
  have hQ : Q.ShortExact := { exact := hExact, mono_f := hMono, epi_g := hEpi }
  exact ⟨inferInstance, (ShortComplex.Splitting.ofHasBinaryBiproduct I K).shortExact,
    a, b, rfl, rfl, ha, hb, hab, hQ⟩

end CategoryTheory.ShortComplex.ShortExact
