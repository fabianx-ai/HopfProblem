/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.BarycentricSmallChains
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnitPositive
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Global
public import Lib.Topology.Sheaves.SingularCochainSheaf.ResolutionPositive

/-!
# Constant-sheaf cohomology and native singular cohomology in positive degrees

The exact singular-cochain sheaf resolution first identifies native Ext-defined constant-sheaf
cohomology with the homology of global sheafified singular cochains.  Barycentric small chains
then show that the actual global sheafification unit identifies the latter with native singular
cohomology.  The resulting comparison is characterized by this literal unit map and is natural
whenever the resolution-to-global comparison is natural.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

section Comparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Constant-sheaf cohomology in degree `n+1` is the corresponding homology of literal global
sections of the sheafified native singular-cochain complex. -/
def constantSheafGlobalIso (hLC : LocallyContractibleSpace X)
    [MetrizableSpace X] (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf X A) (n + 1)) ≅
      (globalCochainComplex X A).homology (n + 1) :=
  Iso.trans
    (TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology
      (resolution X A hLC) (resolution_isAcyclic X A hLC) n)
    (HomologicalComplex.homologyMapIso
      (resolutionGlobalComplexIso X A hLC) (n + 1))

/-- On a metrizable space, barycentric small chains make the actual global sheafification-unit
map an isomorphism on every positive-degree homology group. -/
theorem globalCochainComparison_homology_isIso_succ_of_metrizable
    [MetrizableSpace X] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison X A) (n + 1)) := by
  let _ : MetricSpace X := metrizableSpaceMetric X
  exact globalCochainComparison_homology_isIso_succ X A
    (hasSmallChainEquivalences_barycentric X) n

/-- The canonical comparison from Ext-defined constant-sheaf cohomology to native singular
cohomology in every positive degree. -/
def constantSheafCohomologyIsoSingular (hLC : LocallyContractibleSpace X)
    [MetrizableSpace X] (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf X A) (n + 1)) ≅
      (AlgebraicTopology.SingularCochains.complex X A).homology (n + 1) := by
  let _ : IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison X A) (n + 1)) :=
    globalCochainComparison_homology_isIso_succ_of_metrizable X A n
  exact Iso.trans (constantSheafGlobalIso X A hLC n)
    (asIso (HomologicalComplex.homologyMap
      (globalCochainComparison X A) (n + 1))).symm

/-- The comparison is characterized by the actual global sheafification-unit homology map. -/
@[reassoc]
theorem constantSheafCohomologyIsoSingular_global
    (hLC : LocallyContractibleSpace X) [MetrizableSpace X] (n : ℕ) :
    (constantSheafCohomologyIsoSingular X A hLC n).hom ≫
        HomologicalComplex.homologyMap
          (globalCochainComparison X A) (n + 1) =
      (constantSheafGlobalIso X A hLC n).hom := by
  let _ : IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison X A) (n + 1)) :=
    globalCochainComparison_homology_isIso_succ_of_metrizable X A n
  let c := (constantSheafGlobalIso X A hLC n).hom
  let e := asIso (HomologicalComplex.homologyMap
    (globalCochainComparison X A) (n + 1))
  exact (Category.assoc c e.inv e.hom).trans
    ((congrArg (fun k => c ≫ k) e.inv_hom_id).trans (Category.comp_id c))

end Comparison

private theorem compare_naturality {C : Type*} [Category C]
    {H H' S S' G G' : C}
    (e : H ⟶ S) (e' : H' ⟶ S') (u : S ⟶ G) (u' : S' ⟶ G') [Mono u']
    (r : H ⟶ G) (r' : H' ⟶ G') (a : H ⟶ H') (b : S ⟶ S') (c : G ⟶ G')
    (he : e ≫ u = r) (he' : e' ≫ u' = r')
    (hr : a ≫ r' = r ≫ c) (hu : b ≫ u' = u ≫ c) :
    a ≫ e' = e ≫ b := by
  apply (cancel_mono u').mp
  calc
    (a ≫ e') ≫ u' = a ≫ r' := by rw [Category.assoc, he']
    _ = r ≫ c := hr
    _ = (e ≫ u) ≫ c := by rw [he]
    _ = e ≫ (b ≫ u') := by rw [Category.assoc, hu]
    _ = (e ≫ b) ≫ u' := (Category.assoc _ _ _).symm

end TopCat.SingularCochainSheaf

namespace TopCat.SingularCochainSheaf

/-- Compatibility with the resolution-to-global comparison implies compatibility with the
native singular-cohomology comparison in every positive degree. -/
theorem constantSheafCohomologyIsoSingular_naturality_of_global
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    [MetrizableSpace X] [MetrizableSpace Y] (n : ℕ)
    (a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf Y A) (n + 1)) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf X A) (n + 1)))
    (h : a ≫ (constantSheafGlobalIso X A hX n).hom =
      (constantSheafGlobalIso Y A hY n).hom ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1)) :
    a ≫ (constantSheafCohomologyIsoSingular X A hX n).hom =
      (constantSheafCohomologyIsoSingular Y A hY n).hom ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1) := by
  let _ : IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison X A) (n + 1)) :=
    globalCochainComparison_homology_isIso_succ_of_metrizable X A n
  let _ : IsIso (HomologicalComplex.homologyMap
      (globalCochainComparison Y A) (n + 1)) :=
    globalCochainComparison_homology_isIso_succ_of_metrizable Y A n
  exact compare_naturality
    (constantSheafCohomologyIsoSingular Y A hY n).hom
    (constantSheafCohomologyIsoSingular X A hX n).hom
    (HomologicalComplex.homologyMap (globalCochainComparison Y A) (n + 1))
    (HomologicalComplex.homologyMap (globalCochainComparison X A) (n + 1))
    (constantSheafGlobalIso Y A hY n).hom
    (constantSheafGlobalIso X A hX n).hom a
    (HomologicalComplex.homologyMap
      (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1))
    (HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1))
    (constantSheafCohomologyIsoSingular_global Y A hY n)
    (constantSheafCohomologyIsoSingular_global X A hX n) h
    (globalCochainComparison_homology_naturality f A (n + 1))

end TopCat.SingularCochainSheaf
