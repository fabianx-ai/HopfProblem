/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Functoriality of Ext under exact functors

This file proves three textbook coherence laws for Mathlib's native `Ext` maps in every degree:
mapping through a composite functor is sequential mapping, mapping through the identity is the
identity, and a natural transformation between exact functors induces the expected endpoint square.

The proof uses dimension shifting through an injective presentation.  Only the source category
needs enough injectives.  No sheaf, spectral-sequence, or proof-specific data occur here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.DerivedCategory

universe w w' w'' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Abelian.Ext

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] HasDerivedCategory.standard

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w'} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w''} E]

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping an Ext class through two exact additive functors agrees with mapping it through their
composite.  This holds in every degree and requires enough injectives only in the source. -/
theorem mapExactFunctor_compFunctor
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [EnoughInjectives C] {A B : C} {n : ℕ} (α : Ext.{w} B A n) :
    (α.mapExactFunctor F).mapExactFunctor G = α.mapExactFunctor (F ⋙ G) := by
  induction n generalizing A with
  | zero =>
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective B A).surjective α
      simp only [Ext.mapExactFunctor_mk₀]
      rfl
  | succ n ih =>
      let I : InjectivePresentation A := Classical.arbitrary _
      have : Injective I.J := I.injective
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      have hz : α.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := by
        change α.comp (Ext.mk₀ I.f) (add_zero (n + 1)) = 0
        exact Ext.eq_zero_of_injective _
      obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₁ B hS α hz rfl
      rw [← hβ]
      have hExt :
          (hS.map_of_exact F).extClass.mapExactFunctor G =
            (hS.map_of_exact (F ⋙ G)).extClass := by
        rw [Ext.mapExactFunctor_extClass]
        exact congrArg (fun h : (S.map (F ⋙ G)).ShortExact ↦ h.extClass)
          (Subsingleton.elim _ _)
      simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih β]
      exact congrArg (fun e ↦ (β.mapExactFunctor (F ⋙ G)).comp e rfl) hExt

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping through the identity exact functor fixes every Ext class in every degree. -/
theorem mapExactFunctor_id [EnoughInjectives C] {A B : C} {n : ℕ} (α : Ext.{w} B A n) :
    α.mapExactFunctor (Functor.id C) = α := by
  induction n generalizing A with
  | zero =>
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective B A).surjective α
      simp only [Ext.mapExactFunctor_mk₀]
      rfl
  | succ n ih =>
      let I : InjectivePresentation A := Classical.arbitrary _
      have : Injective I.J := I.injective
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      have hz : α.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := by
        change α.comp (Ext.mk₀ I.f) (add_zero (n + 1)) = 0
        exact Ext.eq_zero_of_injective _
      obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₁ B hS α hz rfl
      rw [← hβ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih β]
      have hExt : (hS.map_of_exact (Functor.id C)).extClass = hS.extClass := by
        exact congrArg (fun h : S.ShortExact ↦ h.extClass) (Subsingleton.elim _ _)
      exact congrArg (fun e ↦ β.comp e rfl) hExt

set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation between exact additive functors induces the usual endpoint square on
Ext in every degree.  This is the derived-functor naturality identity expressed using degree-zero
Ext classes of the transformation components. -/
theorem mapExactFunctor_natTrans
    (F G : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : F ⟶ G) [EnoughInjectives C] {A B : C} {n : ℕ} (α : Ext.{w} B A n) :
    (α.mapExactFunctor F).comp (Ext.mk₀ (η.app A)) (add_zero n) =
      (Ext.mk₀ (η.app B)).comp (α.mapExactFunctor G) (zero_add n) := by
  induction n generalizing A with
  | zero =>
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective B A).surjective α
      simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
      exact congrArg Ext.mk₀ (η.naturality f)
  | succ n ih =>
      let I : InjectivePresentation A := Classical.arbitrary _
      have : Injective I.J := I.injective
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      have hz : α.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := by
        change α.comp (Ext.mk₀ I.f) (add_zero (n + 1)) = 0
        exact Ext.eq_zero_of_injective _
      obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₁ B hS α hz rfl
      dsimp only [S] at hS β hβ ⊢
      rw [← hβ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
        Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      have hExt := (hS.map_of_exact F).extClass_naturality
        (hS.map_of_exact G) (S.mapNatTrans η)
      simp only [ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₃] at hExt
      dsimp only [S] at hExt
      rw [Ext.comp_assoc_of_third_deg_zero]
      calc
        (β.mapExactFunctor F).comp
            ((hS.map_of_exact F).extClass.comp (Ext.mk₀ (η.app A))
              (add_zero 1)) rfl =
            (β.mapExactFunctor F).comp
              ((Ext.mk₀ (η.app (cokernel I.f))).comp
                (hS.map_of_exact G).extClass (zero_add 1)) rfl :=
          congrArg (fun e ↦ (β.mapExactFunctor F).comp e rfl) hExt
        _ = (((β.mapExactFunctor F).comp
              (Ext.mk₀ (η.app (cokernel I.f))) (add_zero n)).comp
                (hS.map_of_exact G).extClass rfl) := by
          exact (Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega)).symm
        _ = (((Ext.mk₀ (η.app B)).comp
              (β.mapExactFunctor G) (zero_add n)).comp
                (hS.map_of_exact G).extClass rfl) :=
          congrArg (fun e ↦ e.comp (hS.map_of_exact G).extClass rfl) (ih β)
        _ = (Ext.mk₀ (η.app B)).comp
              ((β.mapExactFunctor G).comp
                (hS.map_of_exact G).extClass rfl) (zero_add (n + 1)) := by
          exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)

end CategoryTheory.Abelian.Ext
