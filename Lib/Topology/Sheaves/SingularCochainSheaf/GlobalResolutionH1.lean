/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1
public import Lib.Topology.Sheaves.SingularCochainSheaf.DegreeZeroAcyclic
public import Lib.Topology.Sheaves.SingularCochainSheaf.ResolutionH1

/-!
# Constant-sheaf H¹ from global singular-cochain sheaf sections

The generic sheaf acyclic-resolution comparison is instantiated with the locally exact native
singular-cochain sheaf resolution.  Its short-complex homology is then identified with native
degree-one homology of the full literal global-section complex.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Literal global sections of the full sheafified native cochain complex. -/
def globalCochainComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((TopCat.SheafH1.globalSectionsFunctor X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (complexSheaf X A)

/-- Native homology of a cochain complex is computed by its literal three-term window. -/
def globalWindowH1Iso :
    (globalCochainComplex X A).homology 1 ≅
      ((globalCochainComplex X A).sc' 0 1 2).homology :=
  (HomologicalComplex.homologyFunctorIso' AddCommGrpCat.{0} (ComplexShape.up ℕ)
    0 1 2 ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))).app (globalCochainComplex X A)

/-- Constant-sheaf `H¹` is native degree-one homology of literal global cochain-sheaf sections. -/
def constantSheafGlobalH1Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (TopCat.ConstantSheaf.sheaf X A) 1) ≅
      (globalCochainComplex X A).homology 1 := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf X A 0) 1) :=
    zeroCochainSheaf_h1_subsingleton X A
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (resolutionH1 X A hLC).complex.X₁ 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf X A 0) 1)
    infer_instance
  exact TopCat.SheafH1.AcyclicResolutionH1.h1GlobalIso (resolutionH1 X A hLC) ≪≫
    (globalWindowH1Iso X A).symm

end TopCat.SingularCochainSheaf
