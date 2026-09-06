/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.ConnectingHom
public import Lib.Topology.Sheaves.Cohomology.Cech.DegreeZero
public import Mathlib.Algebra.Homology.ExactSequence

/-!
# The long exact sequence in refinement-directed Cech cohomology

This file translates reviewed textbook section CD-05I, equation (C24). It proves exactness of
the refinement-directed Cech sequence attached to a short exact sequence of abelian sheaves by
the representative calculations in the textbook proof, including its separate degree-zero
branches, and packages the resulting consecutive exact pairs and finite six-object windows.

Naturality of the connecting morphism and the cohomological-delta-functor structure belong to
CD-05J and are deliberately not asserted here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}

/-! ## Initial injection -/

/-- The degree-zero Cech coefficient map induced by the left map of a short exact sequence is
injective. This is the initial injection in equation (C24), transported through the canonical
degree-zero identification with global sections. -/
theorem initialCoefficientMap_injective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) :
    Function.Injective (cechCohomologyCoefficientMap S.f.hom 0) := by
  let _ : Mono S.f.hom :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
      (Opens.grothendieckTopology X) AddCommGrpCat S.f).mp hS.mono_f
  have hf : Function.Injective (S.f.hom.app (op (⊤ : Opens X))) :=
    (AddCommGrpCat.mono_iff_injective _).1 (by infer_instance)
  have hzero :
      cechCohomologyCoefficientMap S.f.hom 0 ≫
          (cechCohomologyZeroIsoGlobalSections S.X₂).hom =
        (cechCohomologyZeroIsoGlobalSections S.X₁).hom ≫
          S.f.hom.app (op (⊤ : Opens X)) :=
    cechCohomologyCoefficientMap_comp_zeroIsoGlobalSections S.X₁ S.f
  intro x y hxy
  apply (AddCommGrpCat.mono_iff_injective
    (cechCohomologyZeroIsoGlobalSections S.X₁).hom).1 (by infer_instance)
  apply hf
  calc
    S.f.hom.app (op (⊤ : Opens X))
        ((cechCohomologyZeroIsoGlobalSections S.X₁).hom x) =
      (cechCohomologyZeroIsoGlobalSections S.X₂).hom
        (cechCohomologyCoefficientMap S.f.hom 0 x) := by
          exact (ConcreteCategory.congr_hom hzero x).symm
    _ = (cechCohomologyZeroIsoGlobalSections S.X₂).hom
        (cechCohomologyCoefficientMap S.f.hom 0 y) := by rw [hxy]
    _ = S.f.hom.app (op (⊤ : Opens X))
        ((cechCohomologyZeroIsoGlobalSections S.X₁).hom y) := by
          exact ConcreteCategory.congr_hom hzero y

/-- The initial categorical pair `0 ⟶ H⁰(A) ⟶ H⁰(B)` in the Cech long sequence. -/
noncomputable def initialCechShortComplex
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (0 : AddCommGrpCat.of PUnit.{u + 1} ⟶ cechCohomology S.X₁.presheaf 0)
    (cechCohomologyCoefficientMap S.f.hom 0) zero_comp

/-- Exactness of the initial categorical pair `0 ⟶ H⁰(A) ⟶ H⁰(B)`. -/
theorem initialCechShortComplex_exact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) : (initialCechShortComplex S).Exact := by
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact
    (0 : AddCommGrpCat.of PUnit.{u + 1} ⟶ cechCohomology S.X₁.presheaf 0)
    (cechCohomologyCoefficientMap S.f.hom 0)
  intro x
  constructor
  · intro hx
    have hx0 : x = 0 := initialCoefficientMap_injective hS (by
      simpa only [map_zero] using hx)
    subst x
    refine ⟨PUnit.unit, ?_⟩
    rfl
  · rintro ⟨z, rfl⟩
    change cechCohomologyCoefficientMap S.f.hom 0 0 = 0
    exact map_zero _

end TopologicalSpace.OpenCover.SetOpenCover
