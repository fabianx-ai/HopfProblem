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

This is the final assembly of the fixed injectively computed degree functors
and their positive connecting morphisms (TEXTBOOK 1589–1598).
The existing canonical `Functor.rightDerivedZeroIsoSelf`, under preservation
of finite limits, identifies the first three terms and both arrows with the
original functor. `InjectiveResolution.toRightDerivedZero_eq` and
`InjectiveResolution.toRightDerivedZero'_comp_iCycles` retain agreement with
every auxiliary resolution's augmentation.
The initial injection `Functor.rightDerived_zero_injective` and positive
injective vanishing `Functor.isZero_rightDerived_obj_injective_succ` apply to
these same degree functors. They remain separate existing receipts, not new
fields of the delta-functor structure.
-/

public section
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- Assemble the existing additive derived degrees, positive boundary,
naturality and all exactness/zero laws into the cohomological delta functor.
No degree object, coefficient map or boundary is replaced (TEXTBOOK 1596–1598). -/
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

/-- The entire degree functor is the fixed right-derived computation, so the
canonical degree-zero identification and positive injective vanishing apply
without a change of model (TEXTBOOK 1589–1595). -/
theorem ofRightDerived_T_obj (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (n : ℕ) :
    ((ofRightDerived F).T n).obj = F.rightDerived n := rfl

/-- The packaged boundary is exactly the established positive connecting
morphism, retaining its computation by every compatible resolution choice
(TEXTBOOK 1596–1598 and the preceding fixed-family construction). -/
theorem ofRightDerived_δ (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ofRightDerived F).δ hS n = F.rightDerivedConnecting hS n := rfl

/-- Positive derived degrees are effaceable: embed each object into its chosen
injective object. The same derived degree of that target is zero, so the
induced map is zero. This is the generic injective-effacement argument of
M00-D (TEXTBOOK 1606–1607, before “Thus both”). -/
theorem ofRightDerived_effaceable (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    (ofRightDerived F).Effaceable := by
  intro n hn
  rw [← Nat.sub_add_cancel hn]
  intro A
  refine ⟨Injective.under A, Injective.ι A, inferInstance, ?_⟩
  exact (F.isZero_rightDerived_obj_injective_succ (n-1) (Injective.under A)).eq_of_tgt _ _

/-- The same derived delta functor is universal as a source: apply the existing
effaceability-implies-universality theorem to its injective effacements.
This is M00-D's oriented CD05L consequence, without any sheaf or comparison
assumptions and without a new universality proof. -/
theorem ofRightDerived_isUniversal (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    (ofRightDerived F).IsUniversal :=
  (ofRightDerived_effaceable F).isUniversal

end CategoryTheory.CohomologicalDeltaFunctor

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]

/-- A natural isomorphism induces a forward morphism of derived delta functors.
Its degrees are the original derived natural transformations. Their established
boundary squares come from applying the isomorphism to the same compatible
resolutions, with the positive convention `j(a) = db`. Thus these fields assemble
the existing maps without a new choice of comparison (TEXTBOOK M10, 1820–1826). -/
noncomputable def ofRightDerivedHom
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) : Hom (ofRightDerived F) (ofRightDerived G) where
  app i := (NatIso.rightDerived α i).hom
  comm hX i := NatIso.rightDerived_hom_connecting α hX i

/-- The original inverse derived maps form the reverse delta morphism.
The inverse boundary square uses the same compatible resolutions and positive
lift convention as the forward square, with no independent sign choice
(TEXTBOOK M10, 1819–1826). -/
noncomputable def ofRightDerivedInv
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) : Hom (ofRightDerived G) (ofRightDerived F) where
  app i := (NatIso.rightDerived α i).inv
  comm hX i := NatIso.rightDerived_inv_connecting α hX i

/-- The whole forward degree transformation is the fixed derived isomorphism's
forward map, retaining its coefficient naturality (TEXTBOOK M10, 1820–1826). -/
theorem ofRightDerivedHom_app
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) (n : ℕ) :
    (ofRightDerivedHom α).app n = (NatIso.rightDerived α n).hom := by
  unfold ofRightDerivedHom
  rfl

/-- The whole reverse degree transformation is the same derived isomorphism's
inverse map, not a separately selected equivalence (TEXTBOOK M10, 1819–1826). -/
theorem ofRightDerivedInv_app
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) (n : ℕ) :
    (ofRightDerivedInv α).app n = (NatIso.rightDerived α n).inv := by
  unfold ofRightDerivedInv
  rfl

/-- Forward transport followed by inverse transport is the identity delta
morphism on the source derived family. Composition is degreewise, where the
two maps are inverse; extensionality gives equality of entire delta morphisms,
not merely objectwise bijections (TEXTBOOK M10, 1820–1826). -/
theorem ofRightDerivedHom_comp_inv
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) :
    Hom.comp (ofRightDerivedHom α) (ofRightDerivedInv α) = Hom.id (ofRightDerived F) := by
  apply Hom.ext
  intro n
  rw [Hom.comp_app, Hom.id_app, ofRightDerivedHom_app, ofRightDerivedInv_app]
  exact (NatIso.rightDerived α n).hom_inv_id

/-- Inverse transport followed by forward transport is independently the
identity delta morphism on the target derived family. The reverse inverse law
in every degree and extensionality give this second whole-morphism identity
(TEXTBOOK M10, 1820–1826). -/
theorem ofRightDerivedInv_comp_hom
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ≅ G) :
    Hom.comp (ofRightDerivedInv α) (ofRightDerivedHom α) = Hom.id (ofRightDerived G) := by
  apply Hom.ext
  intro n
  rw [Hom.comp_app, Hom.id_app, ofRightDerivedInv_app, ofRightDerivedHom_app]
  exact (NatIso.rightDerived α n).inv_hom_id

end CategoryTheory.CohomologicalDeltaFunctor
