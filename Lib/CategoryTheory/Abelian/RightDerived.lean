/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Additivity of the computed right-derived functors

The usual injective-resolution computation gives additive degree functors.
This module retains the existing derived objects and coefficient maps.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory
open HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Functor

/-- Each right-derived degree of an additive abelian-group-valued functor is additive.

Choose the same source and target injective resolutions for two coefficient maps.
The sum of their comparisons extends the sum of the coefficient maps. Compute all
three derived maps using these comparisons; additivity of complex homology and
bilinearity of composition give the sum law on the existing derived family.
Identity and composition are existing functor laws; zero and negatives follow
from this additive instance. This is the PD-L04 comparison-sum argument.
-/
instance rightDerived_additive {A : Type u} [Category.{v} A] [Abelian A]
    [HasInjectiveResolutions A] (F : A ⥤ AddCommGrpCat.{w}) [F.Additive]
    (n : ℕ) : (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    let s := InjectiveResolution.desc f J I
    let t := InjectiveResolution.desc g J I
    have hs : I.ι ≫ s = (CochainComplex.single₀ A).map f ≫ J.ι :=
      InjectiveResolution.desc_commutes f J I
    have ht : I.ι ≫ t = (CochainComplex.single₀ A).map g ≫ J.ι :=
      InjectiveResolution.desc_commutes g J I
    have hsum : I.ι ≫ (s + t) =
        (CochainComplex.single₀ A).map (f + g) ≫ J.ι := by
      simp [Preadditive.comp_add, Preadditive.add_comp, hs, ht]
    rw [F.rightDerived_map_eq n (f + g) (s + t) hsum,
      F.rightDerived_map_eq n f s hs, F.rightDerived_map_eq n g t ht]
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

end CategoryTheory.Functor
