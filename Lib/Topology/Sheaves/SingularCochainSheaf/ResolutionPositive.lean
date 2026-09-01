/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.AcyclicResolution
public import Lib.Topology.Sheaves.Cohomology.FlasqueAcyclic
public import Lib.Topology.Sheaves.SingularCochainSheaf.AugmentationMono
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalResolutionH1
public import Lib.Topology.Sheaves.SingularCochainSheaf.LocalExactPositive
public import Lib.Topology.Sheaves.SingularCochainSheaf.OpenRestriction

/-!
# The indexed singular-cochain sheaf resolution

On a locally contractible space, the constant sheaf augmented into the sheafified native
singular-cochain complex is exact in every degree.  Its actual cycle objects therefore form an
indexed resolution.  On a metrizable space every term of this resolution is flasque and hence
acyclic for global sections.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The exact augmented native singular-cochain sheaf complex. -/
def exactAugmentedComplex (hLC : LocallyContractibleSpace X) :
    CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex
      (C := TopCat.Sheaf AddCommGrpCat.{0} X) where
  F := TopCat.ConstantSheaf.sheaf X A
  complex := complexSheaf X A
  ι := sheafAugmentation X A
  zero := sheafAugmentation_d X A
  initialExact := initialComplex_exact X A hLC
  mono_ι := sheafAugmentation_mono X A
  positiveExact n :=
    ((complexSheaf X A).exactAt_iff' n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1))).mp
        (complexSheaf_exactAt_succ X A hLC n)

/-- The canonical indexed resolution extracted from the exact augmented singular-cochain sheaf
complex. -/
def resolution (hLC : LocallyContractibleSpace X) :
    TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X) :=
  (exactAugmentedComplex X A hLC).toAcyclicResolution

@[simp]
theorem resolution_Z_zero (hLC : LocallyContractibleSpace X) :
    (resolution X A hLC).Z 0 = TopCat.ConstantSheaf.sheaf X A := rfl

@[simp]
theorem resolution_X (hLC : LocallyContractibleSpace X) (n : ℕ) :
    (resolution X A hLC).X n = sheaf X A n := rfl

/-- The differential reconstructed from the indexed singular resolution is the original
sheafified singular-cochain differential. -/
theorem resolution_d (hLC : LocallyContractibleSpace X) (n : ℕ) :
    (resolution X A hLC).d n = sheafDifferential X A n (n + 1) :=
  CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex.toAcyclicResolution_d
    (exactAugmentedComplex X A hLC) n

/-- The indexed resolution is acyclic for global sections on a metrizable space. -/
theorem resolution_isAcyclic (hLC : LocallyContractibleSpace X)
    [MetrizableSpace X] :
    TopCat.SheafCohomology.AcyclicResolution.IsAcyclic
      (resolution X A hLC) := by
  intro i q hq
  let _ : (sheaf X A i).IsFlasque :=
    OpenRestriction.isFlasque_of_metrizable A i
  exact TopCat.SheafCohomology.subsingleton_h_of_isFlasque
    (sheaf X A i) q hq

/-- Literal global sections of the indexed resolution are canonically the full sheafified
singular-cochain complex of global sections. -/
def resolutionGlobalComplexIso (hLC : LocallyContractibleSpace X) :
    TopCat.SheafCohomology.AcyclicResolution.globalComplex
        (resolution X A hLC) ≅
      globalCochainComplex X A :=
  ((TopCat.SheafH1.globalSectionsFunctor X).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso
    (exactAugmentedComplex X A hLC).resolutionComplexIso

end TopCat.SingularCochainSheaf
