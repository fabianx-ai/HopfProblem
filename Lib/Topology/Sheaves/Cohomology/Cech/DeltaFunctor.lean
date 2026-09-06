/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Lib.Topology.Sheaves.Cohomology.Cech.LongExact

/-!
# The Cech cohomological delta functor

This file proves naturality of the lift--differentiate--descend connecting homomorphism and
packages refinement-directed Cech cohomology as a cohomological delta functor.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}

/-- Coefficient images of concrete Cech cocycles preserve composition. -/
theorem coefficientCocycle_comp
    {P Q R : TopCat.Presheaf AddCommGrpCat.{u} X}
    (f : P ⟶ Q) (g : Q ⟶ R) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle P U q) :
    coefficientCocycle (f ≫ g) U q c =
      coefficientCocycle g U q (coefficientCocycle f U q c) := by
  apply Subtype.ext
  simp only [coefficientCocycle_apply_coe]
  have h := congrArg (fun k => k.f q) (OrderedCech.coefficientMap_comp f g U.family)
  exact ConcreteCategory.congr_hom h c.1

namespace BoundaryPresentation

/-- Map a boundary presentation through a morphism of short complexes. -/
def map
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (φ : S ⟶ T) {U : SetOpenCover X} {q : ℕ}
    {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c) :
    BoundaryPresentation T U q (coefficientCocycle φ.τ₃.hom U q c) where
  cover := P.cover
  refinement := P.refinement
  lift := OrderedCech.coefficientMapDegree φ.τ₂.hom P.cover.family q P.lift
  descended := OrderedCech.coefficientMapDegree
    φ.τ₁.hom P.cover.family (q + 1) P.descended
  lift_eq := by
    have h₂₃ : φ.τ₂.hom ≫ T.g.hom = S.g.hom ≫ φ.τ₃.hom :=
      congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom) φ.comm₂₃
    calc
      OrderedCech.coefficientMapDegree T.g.hom P.cover.family q
          (OrderedCech.coefficientMapDegree φ.τ₂.hom P.cover.family q P.lift) =
        OrderedCech.coefficientMapDegree (φ.τ₂.hom ≫ T.g.hom)
          P.cover.family q P.lift := by
            exact (ConcreteCategory.congr_hom
              (congrArg (fun k => k.f q)
                (OrderedCech.coefficientMap_comp φ.τ₂.hom T.g.hom P.cover.family)) P.lift).symm
      _ = OrderedCech.coefficientMapDegree (S.g.hom ≫ φ.τ₃.hom)
          P.cover.family q P.lift := by rw [h₂₃]
      _ = OrderedCech.coefficientMapDegree φ.τ₃.hom P.cover.family q
          (OrderedCech.coefficientMapDegree S.g.hom P.cover.family q P.lift) := by
            exact ConcreteCategory.congr_hom
              (congrArg (fun k => k.f q)
                (OrderedCech.coefficientMap_comp S.g.hom φ.τ₃.hom P.cover.family)) P.lift
      _ = OrderedCech.coefficientMapDegree φ.τ₃.hom P.cover.family q
          (OrderedCech.refinementMapDegree S.X₃.presheaf P.refinement q c.1) := by rw [P.lift_eq]
      _ = OrderedCech.refinementMapDegree T.X₃.presheaf P.refinement q
          (coefficientCocycle φ.τ₃.hom U q c).1 := by
            rw [coefficientCocycle_apply_coe]
            exact (ConcreteCategory.congr_hom
              (congrArg (fun k => k.f q)
                (OrderedCech.coefficientMap_comp_refinementMap φ.τ₃.hom P.refinement)) c.1).symm
  descended_eq := by
    have h₁₂ : φ.τ₁.hom ≫ T.f.hom = S.f.hom ≫ φ.τ₂.hom :=
      congrArg (fun k : S.X₁ ⟶ T.X₂ => k.hom) φ.comm₁₂
    calc
      OrderedCech.coefficientMapDegree T.f.hom P.cover.family (q + 1)
          (OrderedCech.coefficientMapDegree φ.τ₁.hom P.cover.family (q + 1) P.descended) =
        OrderedCech.coefficientMapDegree (φ.τ₁.hom ≫ T.f.hom)
          P.cover.family (q + 1) P.descended := by
            exact (ConcreteCategory.congr_hom
              (congrArg (fun k => k.f (q + 1))
                (OrderedCech.coefficientMap_comp φ.τ₁.hom T.f.hom P.cover.family)) P.descended).symm
      _ = OrderedCech.coefficientMapDegree (S.f.hom ≫ φ.τ₂.hom)
          P.cover.family (q + 1) P.descended := by rw [h₁₂]
      _ = OrderedCech.coefficientMapDegree φ.τ₂.hom P.cover.family (q + 1)
          (OrderedCech.coefficientMapDegree S.f.hom P.cover.family (q + 1) P.descended) := by
            exact ConcreteCategory.congr_hom
              (congrArg (fun k => k.f (q + 1))
                (OrderedCech.coefficientMap_comp S.f.hom φ.τ₂.hom P.cover.family)) P.descended
      _ = OrderedCech.coefficientMapDegree φ.τ₂.hom P.cover.family (q + 1)
          (OrderedCech.differential S.X₂.presheaf P.cover.family q P.lift) := by rw [P.descended_eq]
      _ = OrderedCech.differential T.X₂.presheaf P.cover.family q
          (OrderedCech.coefficientMapDegree φ.τ₂.hom P.cover.family q P.lift) := by
            exact (ConcreteCategory.congr_hom
              (OrderedCech.coefficientMapDegree_comp_differential
                φ.τ₂.hom P.cover.family q) P.lift).symm

/-- Mapping a boundary presentation commutes with further refinement. -/
theorem map_refine
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (φ : S ⟶ T) {U : SetOpenCover X} {q : ℕ}
    {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (r : Refinement W.family P.cover.family) :
    (P.refine W r).map φ = (P.map φ).refine W r := by
  rw [BoundaryPresentation.mk.injEq]
  simp only [map, refine]
  refine ⟨trivial, HEq.rfl, ?_, ?_⟩
  · have h := (ConcreteCategory.congr_hom
      (congrArg (fun k => k.f q)
        (OrderedCech.coefficientMap_comp_refinementMap φ.τ₂.hom r)) P.lift).symm
    exact heq_of_eq h
  · have h := (ConcreteCategory.congr_hom
      (congrArg (fun k => k.f (q + 1))
        (OrderedCech.coefficientMap_comp_refinementMap φ.τ₁.hom r)) P.descended).symm
    exact heq_of_eq h

/-- The cocycle descended by a mapped presentation is the coefficient image of the original. -/
theorem map_descendedCocycle
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    {U : SetOpenCover X} {q : ℕ}
    {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c) :
    (P.map φ).descendedCocycle hT =
      coefficientCocycle φ.τ₁.hom P.cover (q + 1)
        (P.descendedCocycle hS) := by
  apply Subtype.ext
  rfl

/-- The class descended by a mapped presentation is the coefficient image of the old class. -/
theorem map_cechClass
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    {U : SetOpenCover X} {q : ℕ}
    {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c) :
    (P.map φ).cechClass hT =
      cechCohomologyCoefficientMap φ.τ₁.hom (q + 1) (P.cechClass hS) := by
  change toCechCohomology T.X₁.presheaf (q + 1) P.cover
      (cocycleClass T.X₁.presheaf P.cover (q + 1)
        ((P.map φ).descendedCocycle hT)) = _
  rw [map_descendedCocycle hS hT]
  exact (cechCohomologyCoefficientMap_cocycleClass
    φ.τ₁.hom P.cover (q + 1) (P.descendedCocycle hS)).symm

end BoundaryPresentation

/-- Fixed-cover boundary maps are natural in morphisms of short exact sequences. -/
theorem normalizedCechCohomologyCoefficientMap_comp_fixedCoverBoundaryHom
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (U : SetOpenCover X) (q : ℕ) :
    normalizedCechCohomologyCoefficientMap φ.τ₃.hom U q ≫
        fixedCoverBoundaryHom hT U q =
      fixedCoverBoundaryHom hS U q ≫
        cechCohomologyCoefficientMap φ.τ₁.hom (q + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨c, rfl⟩ := cocycleClass_surjective S.X₃.presheaf U q x
  let P := chosenBoundaryPresentation hS U q c
  calc
    (normalizedCechCohomologyCoefficientMap φ.τ₃.hom U q ≫
        fixedCoverBoundaryHom hT U q)
        (cocycleClass S.X₃.presheaf U q c) =
      (P.map φ).cechClass hT := by
        rw [ConcreteCategory.comp_apply,
          normalizedCechCohomologyCoefficientMap_cocycleClass,
          fixedCoverBoundaryHom_cocycleClass,
          boundaryClass_eq_cechClass hT U q
            (coefficientCocycle φ.τ₃.hom U q c) (P.map φ)]
    _ = cechCohomologyCoefficientMap φ.τ₁.hom (q + 1) (P.cechClass hS) :=
      P.map_cechClass hS hT φ
    _ = (fixedCoverBoundaryHom hS U q ≫
        cechCohomologyCoefficientMap φ.τ₁.hom (q + 1))
        (cocycleClass S.X₃.presheaf U q c) := by
          rw [ConcreteCategory.comp_apply, fixedCoverBoundaryHom_cocycleClass,
            boundaryClass_eq_cechClass hS U q c P]

/-- The direct-limit Cech connecting homomorphism is natural in short exact sequences. -/
theorem connectingHom_naturality
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (q : ℕ) :
    cechCohomologyCoefficientMap φ.τ₃.hom q ≫ connectingHom hT q =
      connectingHom hS q ≫
        cechCohomologyCoefficientMap φ.τ₁.hom (q + 1) := by
  apply cechCohomology_hom_ext S.X₃.presheaf q
  intro U
  calc
    toCechCohomology S.X₃.presheaf q U ≫
        (cechCohomologyCoefficientMap φ.τ₃.hom q ≫ connectingHom hT q) =
      (toCechCohomology S.X₃.presheaf q U ≫
        cechCohomologyCoefficientMap φ.τ₃.hom q) ≫ connectingHom hT q :=
        (Category.assoc _ _ _).symm
    _ = normalizedCechCohomologyCoefficientMap φ.τ₃.hom U q ≫
        fixedCoverBoundaryHom hT U q := by
          rw [toCechCohomology_comp_cechCohomologyCoefficientMap, Category.assoc,
            toCechCohomology_comp_connectingHom]
    _ = fixedCoverBoundaryHom hS U q ≫
        cechCohomologyCoefficientMap φ.τ₁.hom (q + 1) :=
      normalizedCechCohomologyCoefficientMap_comp_fixedCoverBoundaryHom hS hT φ U q
    _ = (toCechCohomology S.X₃.presheaf q U ≫ connectingHom hS q) ≫
        cechCohomologyCoefficientMap φ.τ₁.hom (q + 1) := by
          rw [toCechCohomology_comp_connectingHom]
    _ = toCechCohomology S.X₃.presheaf q U ≫
        (connectingHom hS q ≫
          cechCohomologyCoefficientMap φ.τ₁.hom (q + 1)) :=
      Category.assoc _ _ _

end TopologicalSpace.OpenCover.SetOpenCover
