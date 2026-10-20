/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Degree-zero Ext coordinates in the derived category

This file records the exact compatibility between Mathlib's degree-zero Ext equivalence and the
fully faithful degree-zero single functor.  The target of `Ext.hom` is shifted by zero, so the
canonical `shiftFunctorZero` component remains visible.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace CategoryTheory.Abelian.Ext

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]

attribute [local instance] HasDerivedCategory.standard

/-- Mapping the degree-zero morphism represented by an Ext class into the derived category gives
its `Ext.hom`, followed by the canonical identification of the zero shift with the identity. -/
lemma singleFunctor_map_addEquiv₀ (X Y : C) (α : Ext.{w} X Y 0) :
    (DerivedCategory.singleFunctor C 0).map (addEquiv₀ α) =
      α.hom ≫ (shiftFunctorZero (DerivedCategory C) ℤ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj Y) := by
  have h := congrArg Ext.hom (mk₀_homEquiv₀_apply α)
  simp only [mk₀_hom] at h
  have h' : (DerivedCategory.singleFunctor C 0).map (addEquiv₀ α) ≫
        (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
          ((DerivedCategory.singleFunctor C 0).obj Y) = α.hom := by
    simpa [ShiftedHom.mk₀, addEquiv₀, shiftFunctorZero'] using h
  rw [← cancel_mono
    ((shiftFunctorZero (DerivedCategory C) ℤ).inv.app
      ((DerivedCategory.singleFunctor C 0).obj Y))]
  rw [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact h'

/-- The degree-zero coordinate formula specialized to a class supplied through
`Ext.homAddEquiv.symm`. -/
lemma singleFunctor_map_addEquiv₀_homAddEquiv_symm
    (X Y : C)
    (g : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
      ((DerivedCategory.singleFunctor C 0).obj Y) 0) :
    (DerivedCategory.singleFunctor C 0).map
        (addEquiv₀ ((homAddEquiv (X := X) (Y := Y) (n := 0)).symm g)) =
      g ≫ (shiftFunctorZero (DerivedCategory C) ℤ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj Y) := by
  rw [singleFunctor_map_addEquiv₀]
  have h := (homAddEquiv (X := X) (Y := Y) (n := 0)).apply_symm_apply g
  simpa only [homAddEquiv_apply] using congrArg
    (fun t ↦ t ≫ (shiftFunctorZero (DerivedCategory C) ℤ).hom.app
      ((DerivedCategory.singleFunctor C 0).obj Y)) h

end CategoryTheory.Abelian.Ext
