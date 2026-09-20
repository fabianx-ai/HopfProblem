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
# Constant-sheaf `H¹` from global sections of the singular-cochain resolution

Sheaf cohomology is computed by the cohomology of the global sections of an acyclic resolution
(Godement, *Topologie algébrique et théorie des faisceaux* II.4.7; Bredon, *Sheaf Theory* II.4.1).
Applied to the resolution of the constant sheaf `A_X` by the sheafified singular cochains, this
identifies `H¹(X; A_X)` with degree-one cohomology of the complex of global sections
`Γ(X, 𝒮^•(·; A))`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The complex `Γ(X, 𝒮^•(·; A))` of global sections of the sheafified singular-cochain
complex. -/
def globalCochainComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((TopCat.SheafH1.globalSectionsFunctor X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (complexSheaf X A)

/-- Degree-one cohomology of the global-section complex is the homology of its three-term window
`Γ(𝒮^0) → Γ(𝒮^1) → Γ(𝒮^2)`. -/
def globalWindowH1Iso :
    (globalCochainComplex X A).homology 1 ≅
      ((globalCochainComplex X A).sc' 0 1 2).homology :=
  (HomologicalComplex.homologyFunctorIso' AddCommGrpCat.{0} (ComplexShape.up ℕ)
    0 1 2 ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))).app (globalCochainComplex X A)

/-- `H¹(X; A_X)` is degree-one cohomology of the complex of global sections of the sheafified
singular cochains (Bredon, *Sheaf Theory* II.4.1 for cohomology via an acyclic resolution). -/
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
