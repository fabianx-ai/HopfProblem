/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantProductH1FibreIndependence
public import Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonPositive
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.FiniteClosedPositive

/-!
# Positive-degree fibre independence from comparison naturality

Once the Ext-defined pullback maps commute with the canonical comparison to native singular
cohomology, homotopy of the two based-fibre inclusions makes the Ext-defined pullbacks literally
equal.  The unconditional endpoints assume the stated compactness, separation, metrizability and
local contractibility hypotheses.

This is homotopy invariance of constant-coefficient sheaf cohomology in all degrees; see Bredon,
*Sheaf Theory*, II.11.12.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.ConstantProductPositive

/-- If comparison isomorphisms intertwine native constant-sheaf pullback in degree `n+1`
with singular pullback, then the native pullback is an isomorphism whenever singular pullback is.
This is the degree-positive form of the categorical cancellation used in degree one. -/
theorem nativePullback_isIso_of_comparison
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    (f : TopCat.of Z ⟶ TopCat.of Y) (hf : IsClosedMap f)
    (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (A : AddCommGrpCat.{0}) (n : ℕ)
    (cY : @AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0}
          (TopCat.ConstantSheaf.sheaf (TopCat.of Y) A) (n + 1))
        (CategoryTheory.Sheaf.instAddCommGroupH
          (TopCat.ConstantSheaf.sheaf (TopCat.of Y) A) (n + 1)) ≅
      (AlgebraicTopology.SingularCochains.complex Y A).homology (n + 1))
    (cZ : @AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0}
          (TopCat.ConstantSheaf.sheaf (TopCat.of Z) A) (n + 1))
        (CategoryTheory.Sheaf.instAddCommGroupH
          (TopCat.ConstantSheaf.sheaf (TopCat.of Z) A) (n + 1)) ≅
      (AlgebraicTopology.SingularCochains.complex Z A).homology (n + 1))
    (hcomm : TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1) ≫ cZ.hom =
      cY.hom ≫ HomologicalComplex.homologyMap
        (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1))
    [IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1))] :
    IsIso (TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1)) := by
  have : IsIso
      (TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1) ≫ cZ.hom) := by
    rw [hcomm]
    infer_instance
  exact (isIso_comp_right_iff
    (TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1)) cZ.hom).mp this

variable (S X : Type) [TopologicalSpace S] [TopologicalSpace X]
  [T2Space S] [ContractibleSpace S] [MetrizableSpace S]
  [CompactSpace X] [T2Space X] [MetrizableSpace X]

/-- Pullback to one based fibre is an isomorphism in degree `n+1` as soon as its canonical
Ext-to-singular comparison square is known. -/
theorem nativePullback_basedFibreInclusion_isIso_of_comparison_naturality
    (A : AddCommGrpCat.{0}) (s : S)
    (hProd : LocallyContractibleSpace (S × X))
    (hX : LocallyContractibleSpace X) (n : ℕ)
    (hcomm :
      TopCat.ConstantSheafCohomology.pullback
          (TopCat.ConstantProductH1.basedFibreInclusion S X s)
          (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
          (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A (n + 1) ≫
          (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
            (TopCat.of X) A hX n).hom =
        (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
            (TopCat.of (S × X)) A hProd n).hom ≫
          HomologicalComplex.homologyMap
            (AlgebraicTopology.SingularCochains.pullback A
              (TopCat.ConstantProductH1.basedFibreInclusion S X s).hom) (n + 1)) :
    IsIso (TopCat.ConstantSheafCohomology.pullback
      (TopCat.ConstantProductH1.basedFibreInclusion S X s)
      (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
      (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A (n + 1)) := by
  exact nativePullback_isIso_of_comparison
    (TopCat.ConstantProductH1.basedFibreInclusion S X s)
    (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
    (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A n
    (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
      (TopCat.of (S × X)) A hProd n)
    (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
      (TopCat.of X) A hX n) hcomm

/-- Unconditional positive-degree isomorphism for pullback to one based fibre of a
contractible product, using the canonical finite-closed Ext-to-singular naturality theorem. -/
theorem nativePullback_basedFibreInclusion_isIso
    (A : AddCommGrpCat.{0}) (s : S)
    (hProd : LocallyContractibleSpace (S × X))
    (hX : LocallyContractibleSpace X) (n : ℕ) :
    IsIso (TopCat.ConstantSheafCohomology.pullback
      (TopCat.ConstantProductH1.basedFibreInclusion S X s)
      (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
      (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A (n + 1)) := by
  apply nativePullback_basedFibreInclusion_isIso_of_comparison_naturality
    S X A s hProd hX n
  exact TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_naturality
    (TopCat.ConstantProductH1.basedFibreInclusion S X s)
    (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
    (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s)
    A hX hProd n

/-- The contractible-product fibre-independence argument in positive degree, separated from
the construction-specific proof that native Ext pullback commutes with the canonical
Ext-to-singular comparison. -/
theorem nativePullback_basedFibreInclusion_eq_of_comparison_naturality
    (A : AddCommGrpCat.{0}) (s t : S)
    (hProd : LocallyContractibleSpace (S × X))
    (hX : LocallyContractibleSpace X) (n : ℕ)
    (hs :
      TopCat.ConstantSheafCohomology.pullback
          (TopCat.ConstantProductH1.basedFibreInclusion S X s)
          (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
          (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A (n + 1) ≫
          (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
            (TopCat.of X) A hX n).hom =
        (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
            (TopCat.of (S × X)) A hProd n).hom ≫
          HomologicalComplex.homologyMap
            (AlgebraicTopology.SingularCochains.pullback A
              (TopCat.ConstantProductH1.basedFibreInclusion S X s).hom) (n + 1))
    (ht :
      TopCat.ConstantSheafCohomology.pullback
          (TopCat.ConstantProductH1.basedFibreInclusion S X t)
          (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X t)
          (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X t) A (n + 1) ≫
          (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
            (TopCat.of X) A hX n).hom =
        (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
            (TopCat.of (S × X)) A hProd n).hom ≫
          HomologicalComplex.homologyMap
            (AlgebraicTopology.SingularCochains.pullback A
              (TopCat.ConstantProductH1.basedFibreInclusion S X t).hom) (n + 1)) :
    TopCat.ConstantSheafCohomology.pullback
        (TopCat.ConstantProductH1.basedFibreInclusion S X s)
        (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
        (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A (n + 1) =
      TopCat.ConstantSheafCohomology.pullback
        (TopCat.ConstantProductH1.basedFibreInclusion S X t)
        (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X t)
        (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X t) A (n + 1) := by
  apply (cancel_mono
    (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
      (TopCat.of X) A hX n).hom).mp
  rw [hs, ht]
  exact congrArg
    (fun k =>
      (TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular
        (TopCat.of (S × X)) A hProd n).hom ≫ k)
    (AlgebraicTopology.SingularCochains.homologyMap_eq_of_homotopy A
      (Classical.choice
        (TopCat.ConstantProductH1.basedFibreInclusion_homotopic S X s t)) (n + 1))

/-- Pullback to two fibres of a contractible product is literally equal in every positive
degree.  This is equality of the actual Ext-defined maps. -/
theorem nativePullback_basedFibreInclusion_eq
    (A : AddCommGrpCat.{0}) (s t : S)
    (hProd : LocallyContractibleSpace (S × X))
    (hX : LocallyContractibleSpace X) (n : ℕ) :
    TopCat.ConstantSheafCohomology.pullback
        (TopCat.ConstantProductH1.basedFibreInclusion S X s)
        (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
        (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s) A (n + 1) =
      TopCat.ConstantSheafCohomology.pullback
        (TopCat.ConstantProductH1.basedFibreInclusion S X t)
        (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X t)
        (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X t) A (n + 1) := by
  apply nativePullback_basedFibreInclusion_eq_of_comparison_naturality
    S X A s t hProd hX n
  · exact TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_naturality
      (TopCat.ConstantProductH1.basedFibreInclusion S X s)
      (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X s)
      (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X s)
      A hX hProd n
  · exact TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_naturality
      (TopCat.ConstantProductH1.basedFibreInclusion S X t)
      (TopCat.ConstantProductH1.basedFibreInclusion_isClosedMap S X t)
      (TopCat.ConstantProductH1.basedFibreInclusion_finite_fibres S X t)
      A hX hProd n

end TopCat.ConstantProductPositive
