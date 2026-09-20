/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension under equivalence

An additive equivalence of abelian categories preserves projective-dimension bounds.  The proof
uses the induced bijection on `Ext`, with essential surjectivity handling the coefficient object.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory.Abelian CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- An additive equivalence sends an object of projective dimension less than `n` to another such
object. -/
theorem hasProjectiveDimensionLT_functor_obj (E : C ≌ D) [E.functor.Additive]
    [EnoughInjectives C] [EnoughInjectives D] (X : C) (n : ℕ)
    (hX : HasProjectiveDimensionLT X n) :
    HasProjectiveDimensionLT (E.functor.obj X) n := by
  let _ := HasExt.standard C
  let _ := HasExt.standard D
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  let Y' : C := E.inverse.obj Y
  let ε : E.functor.obj Y' ≅ Y := E.counitIso.app Y
  let e' : Ext (E.functor.obj X) (E.functor.obj Y') i :=
    e.comp (Ext.mk₀ ε.inv) (add_zero i)
  obtain ⟨x, hx⟩ :=
    (E.functor.mapExt_bijective_of_preservesInjectiveObjects X Y' i).surjective e'
  have hx0 : x = 0 := by
    let _ : HasProjectiveDimensionLT X n := hX
    exact Ext.eq_zero_of_hasProjectiveDimensionLT x n hi
  have he'0 : e' = 0 := by
    rw [← hx, hx0]
    exact map_zero (E.functor.mapExtAddHom X Y' i)
  have hpost := congrArg
    (fun z : Ext (E.functor.obj X) (E.functor.obj Y') i =>
      z.comp (Ext.mk₀ ε.hom) (add_zero i)) he'0
  simpa [e', Ext.comp_assoc_of_second_deg_zero] using hpost

/-- Projective-dimension bounds are invariant under an additive equivalence of abelian
categories. -/
theorem hasProjectiveDimensionLT_functor_obj_iff (E : C ≌ D) [E.functor.Additive]
    [E.inverse.Additive] [EnoughInjectives C] [EnoughInjectives D] (X : C) (n : ℕ) :
    HasProjectiveDimensionLT (E.functor.obj X) n ↔ HasProjectiveDimensionLT X n := by
  constructor
  · intro hFX
    let _ : E.symm.functor.Additive := inferInstanceAs E.inverse.Additive
    have hGFX : HasProjectiveDimensionLT (E.inverse.obj (E.functor.obj X)) n :=
      hasProjectiveDimensionLT_functor_obj E.symm (E.functor.obj X) n hFX
    let _ : HasProjectiveDimensionLT ((E.functor ⋙ E.inverse).obj X) n := hGFX
    exact hasProjectiveDimensionLT_of_iso (E.unitIso.app X).symm n
  · exact hasProjectiveDimensionLT_functor_obj E X n

end CategoryTheory.Equivalence
