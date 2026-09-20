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
# The singular-cochain resolution of the constant sheaf

On a locally contractible space the augmented complex `0 → A_X → 𝒮^0 → 𝒮^1 → ⋯` is exact, so the
sheafified singular cochains form a resolution of the constant sheaf; on a paracompact space (here
a metrizable one) every term of the resolution is flasque, hence acyclic for global sections.  The
resolution is therefore usable to compute `H^•(X; A_X)` (Bredon, *Sheaf Theory* III.1; Warner,
*Foundations of Differentiable Manifolds and Lie Groups* 5.31–5.32).

## Main results

* `TopCat.SingularCochainSheaf.resolution`
* `TopCat.SingularCochainSheaf.resolution_isAcyclic`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The exact augmented complex `0 → A_X → 𝒮^0 → 𝒮^1 → ⋯` on a locally contractible space. -/
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

/-- The resolution of the constant sheaf `A_X` by the sheaves `𝒮^n(·; A)` of singular cochains,
on a locally contractible space (Bredon, *Sheaf Theory* III.1). -/
def resolution (hLC : LocallyContractibleSpace X) :
    TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X) :=
  (exactAugmentedComplex X A hLC).toAcyclicResolution

/-- The zeroth cycle object of the resolution is the constant sheaf `A_X`. -/
@[simp]
theorem resolution_Z_zero (hLC : LocallyContractibleSpace X) :
    (resolution X A hLC).Z 0 = TopCat.ConstantSheaf.sheaf X A := rfl

/-- The degree-`n` term of the resolution is the singular-cochain sheaf `𝒮^n(·; A)`. -/
@[simp]
theorem resolution_X (hLC : LocallyContractibleSpace X) (n : ℕ) :
    (resolution X A hLC).X n = sheaf X A n := rfl

/-- The differential of the resolution is the sheafified singular coboundary. -/
theorem resolution_d (hLC : LocallyContractibleSpace X) (n : ℕ) :
    (resolution X A hLC).d n = sheafDifferential X A n (n + 1) :=
  CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex.toAcyclicResolution_d
    (exactAugmentedComplex X A hLC) n

/-- On a metrizable space the singular-cochain resolution is acyclic for global sections, since
each `𝒮^n(·; A)` is flasque (Warner, *Foundations of Differentiable Manifolds and Lie Groups*
5.32). -/
theorem resolution_isAcyclic (hLC : LocallyContractibleSpace X)
    [MetrizableSpace X] :
    TopCat.SheafCohomology.AcyclicResolution.IsAcyclic
      (resolution X A hLC) := by
  intro i q hq
  let _ : (sheaf X A i).IsFlasque :=
    OpenRestriction.isFlasque_of_metrizable A i
  exact TopCat.SheafCohomology.subsingleton_h_of_isFlasque
    (sheaf X A i) q hq

/-- The complex of global sections of the resolution is canonically the complex
`Γ(X, 𝒮^•(·; A))`. -/
def resolutionGlobalComplexIso (hLC : LocallyContractibleSpace X) :
    TopCat.SheafCohomology.AcyclicResolution.globalComplex
        (resolution X A hLC) ≅
      globalCochainComplex X A :=
  ((TopCat.SheafH1.globalSectionsFunctor X).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso
    (exactAugmentedComplex X A hLC).resolutionComplexIso

end TopCat.SingularCochainSheaf
