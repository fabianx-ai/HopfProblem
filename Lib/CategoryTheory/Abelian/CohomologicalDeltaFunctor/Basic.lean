/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Cohomological delta functors

A reusable interface for a sequence of additive functors equipped with natural connecting
morphisms and the three recurring exactness conditions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A cohomological delta functor between abelian categories. -/
structure CohomologicalDeltaFunctor
    (C : Type u₁) [Category.{v₁} C] [Abelian C]
    (D : Type u₂) [Category.{v₂} D] [Abelian D] where
  T : ℕ → AdditiveFunctor C D
  δ : ∀ {S : ShortComplex C}, S.ShortExact → ∀ n,
    (T n).obj.obj S.X₃ ⟶ (T (n + 1)).obj.obj S.X₁
  naturality : ∀ {S S' : ShortComplex C} (hS : S.ShortExact)
      (hS' : S'.ShortExact) (φ : S ⟶ S') (n : ℕ),
    (T n).obj.map φ.τ₃ ≫ δ hS' n =
      δ hS n ≫ (T (n + 1)).obj.map φ.τ₁
  exact₁ : ∀ {S : ShortComplex C}, S.ShortExact → ∀ n,
    (S.map (T n).obj).Exact
  comp₂ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    (T n).obj.map S.g ≫ δ hS n = 0
  exact₂ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((T n).obj.map S.g) (δ hS n) (comp₂ hS n)).Exact
  comp₃ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    δ hS n ≫ (T (n + 1)).obj.map S.f = 0
  exact₃ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ hS n) ((T (n + 1)).obj.map S.f) (comp₃ hS n)).Exact

end CategoryTheory
