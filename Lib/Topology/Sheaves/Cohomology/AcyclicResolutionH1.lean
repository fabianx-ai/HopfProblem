/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup
public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
public import Lib.Topology.Sheaves.GlobalSections

/-!
# Sheaf H¹ from an acyclic resolution

For a short exact sequence `0 → F → A → B → 0` of abelian sheaves whose middle term is acyclic,
the first cohomology group `H¹(X, F)` is the homology of the three-term complex of global
sections.  This is the degree-one case of "acyclic resolutions compute sheaf cohomology".

The file also records the identification of degree-zero sheaf cohomology with global sections,
`H⁰(X, F) ≅ Γ(X, F)`, and its naturality in `F`.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 1.2A
* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.4.7
* C. Weibel, *An Introduction to Homological Algebra*, Theorem 2.4.6
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace TopCat.SheafH1

variable {X : TopCat.{u}}

/-- The canonical identification of degree-zero sheaf cohomology with global sections. -/
def h0GlobalIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} F 0) ≅
      (TopCat.Sheaf.globalSectionsFunctor X).obj F :=
  (CategoryTheory.Sheaf.H.equiv₀ F
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)).toAddCommGrpIso

/-- The identification `H⁰(X, F) ≅ Γ(X, F)` is natural in the sheaf `F`. -/
theorem h0GlobalIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (extFunctorObj (TopCat.ConstantSheaf.integralSheaf X) 0).map f ≫ (h0GlobalIso G).hom =
      (h0GlobalIso F).hom ≫ (TopCat.Sheaf.globalSectionsFunctor X).map f := by
  ext x
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality
    (show IsTerminal (⊤ : Opens X) from isTerminalTop) f x).symm

namespace AcyclicResolutionH1

variable (R : CategoryTheory.Abelian.Ext.AcyclicResolutionH1
  (C := TopCat.Sheaf AddCommGrpCat.{u} X))

/-- Literal global sections of the three-term complex. -/
abbrev globalComplex : ShortComplex AddCommGrpCat.{u} :=
  R.complex.map (TopCat.Sheaf.globalSectionsFunctor X)

/-- Degree-zero Ext and global sections agree as short complexes. -/
def extZeroGlobalIso : R.extZeroComplex (TopCat.ConstantSheaf.integralSheaf X) ≅ globalComplex R :=
  ShortComplex.isoMk (h0GlobalIso R.complex.X₁) (h0GlobalIso R.complex.X₂)
    (h0GlobalIso R.complex.X₃) (h0GlobalIso_naturality R.complex.f).symm
      (h0GlobalIso_naturality R.complex.g).symm

/-- Native Ext-defined sheaf H¹ is the homology of literal global sections. -/
def h1GlobalIso [Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} R.F 1) ≅ (globalComplex R).homology := by
  letI : Subsingleton (Ext.{u} (TopCat.ConstantSheaf.integralSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)›
  exact R.extOneIso (TopCat.ConstantSheaf.integralSheaf X) ≪≫ ShortComplex.homologyMapIso (extZeroGlobalIso R)

end AcyclicResolutionH1

end TopCat.SheafH1
