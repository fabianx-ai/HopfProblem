/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Effaceable
public import Lib.CategoryTheory.Abelian.RightDerived
public import Lib.CategoryTheory.Abelian.RightDerived.Connecting
/-!
# The cohomological delta functor of a derived family

For an additive functor `F` on an abelian category with enough injectives, the family
`n ↦ Rⁿ F` with the connecting morphisms of the long exact sequence is a cohomological
delta functor, and it is universal because `Rⁿ⁺¹ F` vanishes on injectives. This is
Weibel, *An Introduction to Homological Algebra*, Theorem 2.4.6 (see also
Hartshorne, *Algebraic Geometry* III.1.1A).

The degree-zero identification `Functor.rightDerivedZeroIsoSelf` (under preservation of
finite limits), the injection `Functor.rightDerived_zero_injective` and the vanishing
`Functor.isZero_rightDerived_obj_injective_succ` remain separate theorems rather than
fields of the delta-functor structure.
-/

public section
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- Assemble the existing additive derived degrees, positive boundary,
naturality and all exactness/zero laws into the cohomological delta functor
`n ↦ Rⁿ F` (Weibel 2.4.6(b)). -/
@[expose] def ofRightDerived (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    CohomologicalDeltaFunctor C AddCommGrpCat.{w} where
  T n := AdditiveFunctor.of (F.rightDerived n)
  δ hS n := F.rightDerivedConnecting hS n
  naturality hS hS' f n := F.rightDerivedConnecting_naturality hS hS' f n
  exact₁ hS n := F.rightDerived_exact₁ hS n
  comp₂ hS n := F.comp_rightDerivedConnecting hS n
  exact₂ hS n := F.rightDerived_exact₂ hS n
  comp₃ hS n := F.rightDerivedConnecting_comp hS n
  exact₃ hS n := F.rightDerived_exact₃ hS n

/-- The degree-`n` functor of `ofRightDerived F` is the right derived functor `Rⁿ F`. -/
theorem ofRightDerived_T_obj (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (n : ℕ) :
    ((ofRightDerived F).T n).obj = F.rightDerived n := rfl

/-- The connecting morphism of `ofRightDerived F` is the boundary
`Rⁿ F(X₃) ⟶ Rⁿ⁺¹ F(X₁)` of the long exact sequence of right derived functors. -/
theorem ofRightDerived_δ (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ofRightDerived F).δ hS n = F.rightDerivedConnecting hS n := rfl

/-- `Rⁿ F` is effaceable in every positive degree: every object embeds into an injective
object `I`, and `Rⁿ F(I) = 0` for `n > 0` (Weibel 2.4.6(c)). -/
theorem ofRightDerived_effaceable (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    (ofRightDerived F).Effaceable := by
  intro n hn
  rw [← Nat.sub_add_cancel hn]
  intro A
  refine ⟨Injective.under A, Injective.ι A, inferInstance, ?_⟩
  exact (F.isZero_rightDerived_obj_injective_succ (n-1) (Injective.under A)).eq_of_tgt _ _

/-- `n ↦ Rⁿ F` is a universal cohomological delta functor: every natural transformation
out of its degree-zero part extends uniquely to a morphism of delta functors
(Weibel Theorem 2.4.6(c); Hartshorne III.1.1A). -/
theorem ofRightDerived_isUniversal (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    (ofRightDerived F).IsUniversal :=
  (ofRightDerived_effaceable F).isUniversal

end CategoryTheory.CohomologicalDeltaFunctor

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]

/-- A natural isomorphism `α : F ≅ G` induces a morphism of delta functors
`ofRightDerived F ⟶ ofRightDerived G` whose degree-`n` component is `Rⁿ α`
(Weibel 2.4.6, Exercise 2.4.3). -/
noncomputable def ofRightDerivedHom
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) : Hom (ofRightDerived F) (ofRightDerived G) where
  app i := (NatIso.rightDerived α i).hom
  comm hX i := NatIso.rightDerived_hom_connecting α hX i

/-- The inverse of `α : F ≅ G` induces the reverse morphism of delta functors
`ofRightDerived G ⟶ ofRightDerived F`, with degree-`n` component `(Rⁿ α)⁻¹`. -/
noncomputable def ofRightDerivedInv
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) : Hom (ofRightDerived G) (ofRightDerived F) where
  app i := (NatIso.rightDerived α i).inv
  comm hX i := NatIso.rightDerived_inv_connecting α hX i

/-- The degree-`n` component of `ofRightDerivedHom α` is the forward map of `Rⁿ α`. -/
theorem ofRightDerivedHom_app
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) (n : ℕ) :
    (ofRightDerivedHom α).app n = (NatIso.rightDerived α n).hom := by
  unfold ofRightDerivedHom
  rfl

/-- The degree-`n` component of `ofRightDerivedInv α` is the inverse map of `Rⁿ α`. -/
theorem ofRightDerivedInv_app
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) (n : ℕ) :
    (ofRightDerivedInv α).app n = (NatIso.rightDerived α n).inv := by
  unfold ofRightDerivedInv
  rfl

/-- `ofRightDerivedHom α` followed by `ofRightDerivedInv α` is the identity morphism of
delta functors on `ofRightDerived F`. -/
theorem ofRightDerivedHom_comp_inv
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) :
    Hom.comp (ofRightDerivedHom α) (ofRightDerivedInv α) = Hom.id (ofRightDerived F) := by
  apply Hom.ext
  intro n
  rw [Hom.comp_app, Hom.id_app, ofRightDerivedHom_app, ofRightDerivedInv_app]
  exact (NatIso.rightDerived α n).hom_inv_id

/-- `ofRightDerivedInv α` followed by `ofRightDerivedHom α` is the identity morphism of
delta functors on `ofRightDerived G`. -/
theorem ofRightDerivedInv_comp_hom
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) :
    Hom.comp (ofRightDerivedInv α) (ofRightDerivedHom α) = Hom.id (ofRightDerived G) := by
  apply Hom.ext
  intro n
  rw [Hom.comp_app, Hom.id_app, ofRightDerivedInv_app, ofRightDerivedHom_app]
  exact (NatIso.rightDerived α n).inv_hom_id

end CategoryTheory.CohomologicalDeltaFunctor
