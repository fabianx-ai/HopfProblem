/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# Flasque sheaves of dependent additive functions

For a family of additive commutative groups `A : X → AddCommGrpCat`, sections over an open
`U` are arbitrary dependent functions `x : U ↦ A x`.  Restriction is precomposition with an
inclusion of opens.  Extension by zero proves that this is a flasque sheaf.

The constant-family specialization is the usual sheaf of arbitrary functions.  The dependent
version is the natural ambient flasque sheaf for the Godement germ embedding, whose fibre at
`x` is the stalk of the original sheaf at `x`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.DependentFunctionSheaf

universe u

/-- The presheaf of arbitrary dependent additive functions. -/
def presheaf (X : TopCat.{u}) (A : X → AddCommGrpCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of ((x : U.unop) → A x.1)
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun := fun f x => f (i.unop x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    ext f x
    rfl
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl

@[simp]
theorem presheaf_obj (X : TopCat.{u}) (A : X → AddCommGrpCat.{u})
    (U : (Opens X)ᵒᵖ) :
    (presheaf X A).obj U = AddCommGrpCat.of ((x : U.unop) → A x.1) := rfl

@[simp]
theorem presheaf_map_apply (X : TopCat.{u}) (A : X → AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : (x : U.unop) → A x.1) (x : V.unop) :
    (presheaf X A).map i f x = f (i.unop x) := rfl

/-- Forgetting addition recovers Mathlib's presheaf of arbitrary dependent functions. -/
def forgetIso (X : TopCat.{u}) (A : X → AddCommGrpCat.{u}) :
    presheaf X A ⋙ forget AddCommGrpCat.{u} ≅
      TopCat.presheafToTypes X (fun x => A x) where
  hom :=
    { app := fun _ => 𝟙 _
      naturality := by intros; rfl }
  inv :=
    { app := fun _ => 𝟙 _
      naturality := by intros; rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Arbitrary dependent additive functions satisfy the sheaf condition. -/
theorem isSheaf (X : TopCat.{u}) (A : X → AddCommGrpCat.{u}) :
    (presheaf X A).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget AddCommGrpCat.{u}) (presheaf X A)).mpr
  exact (TopCat.Presheaf.isSheaf_iso_iff (forgetIso X A)).mpr
    (TopCat.Presheaf.toTypes_isSheaf X (fun x => A x))

/-- The sheaf of arbitrary dependent additive functions. -/
def sheaf (X : TopCat.{u}) (A : X → AddCommGrpCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨presheaf X A, isSheaf X A⟩

/-- Extension by zero along an inclusion of opens. -/
def extendByZero (X : TopCat.{u}) (A : X → AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (_i : U ⟶ V)
    (s : (x : V.unop) → A x.1) : (x : U.unop) → A x.1 := by
  classical
  intro x
  exact if hx : x.1 ∈ V.unop then s ⟨x.1, hx⟩ else 0

@[simp]
theorem restrict_extendByZero (X : TopCat.{u}) (A : X → AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : (x : V.unop) → A x.1) (x : V.unop) :
    (presheaf X A).map i (extendByZero X A i s) x = s x := by
  change extendByZero X A i s ⟨x.1, _⟩ = s x
  rw [extendByZero, dif_pos x.2]

/-- The arbitrary dependent-function sheaf is flasque. -/
instance sheaf_isFlasque (X : TopCat.{u}) (A : X → AddCommGrpCat.{u}) :
    (sheaf X A).IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    exact ⟨extendByZero X A i s, by
      funext x
      exact restrict_extendByZero X A i s x⟩

end TopCat.DependentFunctionSheaf
