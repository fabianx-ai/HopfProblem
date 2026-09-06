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

namespace CohomologicalDeltaFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A morphism of cohomological delta functors: degreewise natural transformations commuting
with connecting morphisms. This is the formal image of textbook coordinate L-H1, equation (U4). -/
structure Hom (T S : CohomologicalDeltaFunctor C D) where
  app : ∀ n : ℕ, (T.T n).obj ⟶ (S.T n).obj
  comm : ∀ {X : ShortComplex C} (hX : X.ShortExact) (n : ℕ),
    T.δ hX n ≫ (app (n + 1)).app X.X₁ = (app n).app X.X₃ ≫ S.δ hX n

/-- Morphisms of cohomological delta functors are determined degreewise (L-H2). -/
@[ext]
theorem Hom.ext {T S : CohomologicalDeltaFunctor C D} {η η' : Hom T S}
    (h : ∀ n, η.app n = η'.app n) : η = η' := by
  cases η
  cases η'
  congr
  funext n
  exact h n

/-- The identity morphism of a cohomological delta functor (L-H3). -/
def Hom.id (T : CohomologicalDeltaFunctor C D) : Hom T T where
  app n := 𝟙 _
  comm hX n := by
    rw [NatTrans.id_app, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- Composition of morphisms of cohomological delta functors (L-H4). -/
def Hom.comp {T S R : CohomologicalDeltaFunctor C D} (η : Hom T S) (θ : Hom S R) :
    Hom T R where
  app n := η.app n ≫ θ.app n
  comm hX n := by
    rw [NatTrans.comp_app, NatTrans.comp_app, ← Category.assoc, η.comm hX n,
      Category.assoc, θ.comm hX n, Category.assoc]

/-- The degree-`n` component of the identity morphism (L-H5). -/
theorem Hom.id_app (T : CohomologicalDeltaFunctor C D) (n : ℕ) :
    (Hom.id T).app n = 𝟙 (T.T n).obj := rfl

/-- The degree-`n` component of a composite morphism (L-H6). -/
theorem Hom.comp_app {T S R : CohomologicalDeltaFunctor C D} (η : Hom T S) (θ : Hom S R)
    (n : ℕ) : (Hom.comp η θ).app n = η.app n ≫ θ.app n := rfl

end CohomologicalDeltaFunctor

end CategoryTheory
