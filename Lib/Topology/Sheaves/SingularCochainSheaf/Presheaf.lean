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
# The presheaf of singular cochains

The presheaf `U ↦ S^n(U; A)` on a topological space `X`, with restriction maps given by pullback
of cochains along the inclusions of open sets (Bredon, *Sheaf Theory* III.1).

## Main definitions

* `TopCat.SingularCochainSheaf.presheaf`: the degree-`n` presheaf `U ↦ S^n(U; A)`.
* `TopCat.SingularCochainSheaf.complex`: the singular-cochain complex of presheaves.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

/-- Singular cochains with coefficients in `A` as a contravariant functor of spaces. -/
def cochainFunctor (A : AddCommGrpCat.{0}) :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj X := AlgebraicTopology.SingularCochains.complex X.unop A
  map f := AlgebraicTopology.SingularCochains.pullback A f.unop.hom
  map_id X := AlgebraicTopology.SingularCochains.pullback_id X.unop A
  map_comp f g := AlgebraicTopology.SingularCochains.pullback_comp A g.unop.hom f.unop.hom

/-- The degree-`n` presheaf `U ↦ S^n(U; A)` of singular cochains on the open subsets of `X`. -/
def presheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Opens.toTopCat X).op ⋙ cochainFunctor A ⋙
    HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.up ℕ) n

/-- The sections of the degree-`n` singular-cochain presheaf over `U` are the degree-`n` singular
cochains of `U`. -/
@[simp]
theorem presheaf_obj (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)
    (U : Opens X) :
    (presheaf X A n).obj (op U) =
      (AlgebraicTopology.SingularCochains.complex U A).X n := rfl

/-- The singular-cochain coboundary `S^i(U; A) → S^j(U; A)`, natural in the open set `U`. -/
def differential (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :
    presheaf X A i ⟶ presheaf X A j where
  app U := (AlgebraicTopology.SingularCochains.complex U.unop A).d i j
  naturality _ _ f :=
    (AlgebraicTopology.SingularCochains.pullback A
      ((Opens.toTopCat X).map f.unop).hom).comm i j

/-- Over an open set `U`, the coboundary of the presheaf is the coboundary of the singular-cochain
complex of `U`. -/
@[simp]
theorem differential_app (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (i j : ℕ) (U : Opens X) :
    (differential X A i j).app (op U) =
      (AlgebraicTopology.SingularCochains.complex U A).d i j := rfl

/-- The singular-cochain complex `U ↦ S^•(U; A)` as a cochain complex of presheaves on `X`. -/
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

/-- The degree-`n` term of the complex of presheaves is the degree-`n` singular-cochain
presheaf. -/
@[simp]
theorem complex_X (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    (complex X A).X n = presheaf X A n := rfl

/-- The differential of the complex of presheaves is the singular-cochain coboundary. -/
@[simp]
theorem complex_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :

    (complex X A).d i j = differential X A i j := rfl

end TopCat.SingularCochainSheaf
