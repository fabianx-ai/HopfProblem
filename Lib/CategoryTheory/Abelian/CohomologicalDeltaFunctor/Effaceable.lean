/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Effaceable and universal cohomological delta functors

Reusable definitions of effaceability and the universal extension property for cohomological
delta functors.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A delta functor is effaceable at degree `n` when every object embeds into one on which the
induced degree-`n` map vanishes (L-E1). -/
def EffaceableAt (T : CohomologicalDeltaFunctor C D) (n : ℕ) : Prop :=
  ∀ A : C, ∃ (M : C) (i : A ⟶ M), Mono i ∧ (T.T n).obj.map i = 0

/-- A delta functor is effaceable when it is effaceable in every positive degree (L-E2). -/
def Effaceable (T : CohomologicalDeltaFunctor C D) : Prop :=
  ∀ n : ℕ, 0 < n → T.EffaceableAt n

/-- Universality is the unique extension of every degree-zero natural transformation to a
morphism of delta functors (L-U1). -/
def IsUniversal (T : CohomologicalDeltaFunctor C D) : Prop :=
  ∀ (S : CohomologicalDeltaFunctor C D) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj),
    ∃! η : Hom T S, η.app 0 = η₀

/-- The universal extension selected from the unique-existence property (L-U2). -/
def IsUniversal.extend {T : CohomologicalDeltaFunctor C D} (h : T.IsUniversal)
    (S : CohomologicalDeltaFunctor C D) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) : Hom T S :=
  (h S η₀).exists.choose

/-- The selected universal extension has the prescribed degree-zero component (L-U3). -/
theorem IsUniversal.extend_app_zero {T : CohomologicalDeltaFunctor C D} (h : T.IsUniversal)
    (S : CohomologicalDeltaFunctor C D) (η₀ : (T.T 0).obj ⟶ (S.T 0).obj) :
    (h.extend S η₀).app 0 = η₀ :=
  (h S η₀).exists.choose_spec

/-- Universal morphisms agreeing in degree zero agree in every degree (L-U4). -/
theorem IsUniversal.hom_ext {T : CohomologicalDeltaFunctor C D} (h : T.IsUniversal)
    {S : CohomologicalDeltaFunctor C D} {η η' : Hom T S}
    (h0 : η.app 0 = η'.app 0) : η = η' :=
  (h S (η.app 0)).unique rfl h0.symm

end CategoryTheory.CohomologicalDeltaFunctor
