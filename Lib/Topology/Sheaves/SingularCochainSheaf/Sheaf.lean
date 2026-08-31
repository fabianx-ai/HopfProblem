/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.Presheaf
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafified native singular cochains

The native sheafification functor is applied degreewise to the presheaf complex of singular
cochains.  The sheafification unit is retained as a map of complexes; no local exactness or
cohomological acyclicity is asserted here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

/-- Native sheafification on the open-set site of `X`. -/
abbrev sheafification (X : TopCat.{0}) :
    TopCat.Presheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

instance sheafification_additive (X : TopCat.{0}) : (sheafification X).Additive :=
  inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).Additive

/-- The sheaf of germs of native singular `n`-cochains. -/
abbrev sheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  (sheafification X).obj (presheaf X A n)

/-- The differential induced by the native singular boundary. -/
def sheafDifferential (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :
    sheaf X A i ⟶ sheaf X A j :=
  (sheafification X).map (differential X A i j)

/-- The degreewise sheafification of the native singular cochain complex. -/
abbrev complexSheaf (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((sheafification X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex X A)

@[simp]
theorem complexSheaf_X (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    (complexSheaf X A).X n = sheaf X A n := rfl

@[simp]
theorem complexSheaf_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :
    (complexSheaf X A).d i j = sheafDifferential X A i j := rfl

/-- The sheafification unit in degree `n`. -/
def unit (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    presheaf X A n ⟶ (sheaf X A n).obj :=
  toSheafify (Opens.grothendieckTopology X) (presheaf X A n)

/-- The sheafification units commute with the native cochain differential. -/
@[reassoc]
theorem unit_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (i j : ℕ) :
    unit X A i ≫ (sheafDifferential X A i j).hom =
      differential X A i j ≫ unit X A j :=
  (toSheafify_naturality (Opens.grothendieckTopology X)
    (differential X A i j)).symm

/-- The sheafification unit as a map of full presheaf complexes. -/
def unitComplex (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    complex X A ⟶
      ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (complexSheaf X A) where
  f n := unit X A n
  comm' i j _ := unit_d X A i j

end TopCat.SingularCochainSheaf
