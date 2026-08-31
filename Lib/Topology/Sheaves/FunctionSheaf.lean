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
# The flasque sheaf of arbitrary additive-group-valued functions

Restriction is ordinary precomposition along inclusions of opens.  Every local function extends
by zero, so the resulting sheaf is flasque without a finiteness or separation hypothesis.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.FunctionSheaf

universe u

/-- The presheaf of arbitrary additive-group-valued functions. -/
def presheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (U.unop → A)
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
theorem presheaf_obj (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (U : (Opens X)ᵒᵖ) :
    (presheaf X A).obj U = AddCommGrpCat.of (U.unop → A) := rfl

@[simp]
theorem presheaf_map_apply (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : U.unop → A) (x : V.unop) :
    (presheaf X A).map i f x = f (i.unop x) := rfl

/-- Forgetting addition recovers Mathlib's presheaf of arbitrary functions. -/
def forgetIso (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    presheaf X A ⋙ forget AddCommGrpCat.{u} ≅ TopCat.presheafToType X A where
  hom :=
    { app := fun _ => 𝟙 _
      naturality := by intros; rfl }
  inv :=
    { app := fun _ => 𝟙 _
      naturality := by intros; rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Arbitrary additive-group-valued functions satisfy the sheaf condition. -/
theorem isSheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    (presheaf X A).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget AddCommGrpCat.{u}) (presheaf X A)).mpr
  exact (TopCat.Presheaf.isSheaf_iso_iff (forgetIso X A)).mpr
    (TopCat.Presheaf.toType_isSheaf X A)

/-- The sheaf of arbitrary additive-group-valued functions. -/
def sheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨presheaf X A, isSheaf X A⟩

/-- Extension by zero along an inclusion of opens. -/
def extendByZero (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (_i : U ⟶ V) (s : V.unop → A) : U.unop → A := by
  classical
  intro x
  exact if hx : x.1 ∈ V.unop then s ⟨x.1, hx⟩ else 0

@[simp]
theorem restrict_extendByZero (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : V.unop → A) (x : V.unop) :
    (presheaf X A).map i (extendByZero X A i s) x = s x := by
  change extendByZero X A i s ⟨x.1, _⟩ = s x
  rw [extendByZero, dif_pos x.2]

/-- The arbitrary-function sheaf is flasque. -/
instance sheaf_isFlasque (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    (sheaf X A).IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    exact ⟨extendByZero X A i s, by
      funext x
      exact restrict_extendByZero X A i s x⟩

end TopCat.FunctionSheaf
