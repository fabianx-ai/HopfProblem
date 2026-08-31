/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains
public import Lib.Topology.Sheaves.ConstantPushforward
public import Mathlib.Topology.Sheaves.Abelian

/-!
# The presheaf of native singular cochains

This restricts Mathlib-native additive singular cochains to open subspaces.  Restrictions are
literal pullback along open inclusions.  The construction is independent of any sheaf-cohomology
comparison.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

/-- Native singular cochains as a contravariant functor of spaces. -/
def cochainFunctor (A : AddCommGrpCat.{0}) :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj X := AlgebraicTopology.SingularCochains.complex X.unop A
  map f := AlgebraicTopology.SingularCochains.pullback A f.unop.hom
  map_id X := AlgebraicTopology.SingularCochains.pullback_id X.unop A
  map_comp f g := AlgebraicTopology.SingularCochains.pullback_comp A g.unop.hom f.unop.hom

/-- The degree-`n` presheaf of native singular cochains on open subspaces of `X`. -/
def presheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Opens.toTopCat X).op ⋙ cochainFunctor A ⋙
    HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.up ℕ) n

@[simp]
theorem presheaf_obj (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)
    (U : Opens X) :
    (presheaf X A n).obj (op U) =
      (AlgebraicTopology.SingularCochains.complex U A).X n := rfl

/-- The native cochain differential, natural in the open subspace. -/
def differential (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :
    presheaf X A i ⟶ presheaf X A j where
  app U := (AlgebraicTopology.SingularCochains.complex U.unop A).d i j
  naturality _ _ f :=
    (AlgebraicTopology.SingularCochains.pullback A
      ((Opens.toTopCat X).map f.unop).hom).comm i j

@[simp]
theorem differential_app (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (i j : ℕ) (U : Opens X) :
    (differential X A i j).app (op U) =
      (AlgebraicTopology.SingularCochains.complex U A).d i j := rfl

/-- The native singular cochain complex assembled as a complex of presheaves. -/
def complex (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ where
  X n := presheaf X A n
  d i j := differential X A i j
  shape i j hij := by
    apply NatTrans.ext
    funext U
    exact (AlgebraicTopology.SingularCochains.complex U.unop A).shape i j hij
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact (AlgebraicTopology.SingularCochains.complex U.unop A).d_comp_d i j k

@[simp]
theorem complex_X (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    (complex X A).X n = presheaf X A n := rfl

@[simp]
theorem complex_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :
    (complex X A).d i j = differential X A i j := rfl

end TopCat.SingularCochainSheaf
