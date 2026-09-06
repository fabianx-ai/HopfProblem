/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.Coefficients
public import Lib.Topology.Sheaves.Cohomology.Cech.Colimit

/-!
# Coefficient functoriality of direct-limit Cech cohomology

This file continues the coefficient-functorial part of textbook section CD-05. The fixed-cover
coefficient maps commute with refinement, so the colimit universal property gives a canonical map
on refinement-directed Cech cohomology. These maps preserve identities and composition and hence
make direct-limit Cech cohomology functorial in presheaf, and therefore sheaf, coefficients.

No effaceability assertion, long exact sequence, or comparison with derived sheaf cohomology is
made here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}
variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]
  [CategoryWithHomology A] [HasColimitsOfShape (SetOpenCover X) A]
variable {P Q R : TopCat.Presheaf A X}

/-- The canonical map on refinement-directed Cech cohomology induced by a morphism of
coefficient presheaves. -/
noncomputable def cechCohomologyCoefficientMap (f : P ⟶ Q) (n : ℕ) :
    cechCohomology P n ⟶ cechCohomology Q n :=
  cechCohomologyDesc P n (cechCohomology Q n)
    (fun U => normalizedCechCohomologyCoefficientMap f U n ≫
      toCechCohomology Q n U)
    (fun {U V} h => by
      rw [← Category.assoc,
        ← normalizedCechCohomologyCoefficientMap_comp_refinement f h n,
        Category.assoc, normalizedCechCohomologyMap_comp_toCechCohomology])

/-- The canonical map from fixed-cover to direct-limit Cech cohomology is natural in the
coefficient presheaf. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_comp_cechCohomologyCoefficientMap
    (f : P ⟶ Q) (n : ℕ) (U : SetOpenCover X) :
    toCechCohomology P n U ≫ cechCohomologyCoefficientMap f n =
      normalizedCechCohomologyCoefficientMap f U n ≫
        toCechCohomology Q n U := by
  exact toCechCohomology_comp_cechCohomologyDesc P n _ _ _ U

/-- The identity coefficient morphism induces the identity map on direct-limit Cech
cohomology. -/
@[simp]
theorem cechCohomologyCoefficientMap_id (P : TopCat.Presheaf A X) (n : ℕ) :
    cechCohomologyCoefficientMap (𝟙 P) n = 𝟙 (cechCohomology P n) := by
  apply cechCohomology_hom_ext P n
  intro U
  rw [toCechCohomology_comp_cechCohomologyCoefficientMap,
    normalizedCechCohomologyCoefficientMap_id, Category.id_comp, Category.comp_id]

/-- Direct-limit Cech coefficient maps preserve composition. -/
@[reassoc]
theorem cechCohomologyCoefficientMap_comp (f : P ⟶ Q) (g : Q ⟶ R) (n : ℕ) :
    cechCohomologyCoefficientMap (f ≫ g) n =
      cechCohomologyCoefficientMap f n ≫ cechCohomologyCoefficientMap g n := by
  apply cechCohomology_hom_ext P n
  intro U
  rw [toCechCohomology_comp_cechCohomologyCoefficientMap,
    normalizedCechCohomologyCoefficientMap_comp]
  calc
    (normalizedCechCohomologyCoefficientMap f U n ≫
        normalizedCechCohomologyCoefficientMap g U n) ≫
          toCechCohomology R n U =
      normalizedCechCohomologyCoefficientMap f U n ≫
        (normalizedCechCohomologyCoefficientMap g U n ≫
          toCechCohomology R n U) := Category.assoc _ _ _
    _ = normalizedCechCohomologyCoefficientMap f U n ≫
        (toCechCohomology Q n U ≫ cechCohomologyCoefficientMap g n) := by
      rw [toCechCohomology_comp_cechCohomologyCoefficientMap]
    _ = (normalizedCechCohomologyCoefficientMap f U n ≫
          toCechCohomology Q n U) ≫ cechCohomologyCoefficientMap g n :=
      (Category.assoc _ _ _).symm
    _ = (toCechCohomology P n U ≫ cechCohomologyCoefficientMap f n) ≫
        cechCohomologyCoefficientMap g n := by
      rw [toCechCohomology_comp_cechCohomologyCoefficientMap]
    _ = toCechCohomology P n U ≫
        (cechCohomologyCoefficientMap f n ≫
          cechCohomologyCoefficientMap g n) := Category.assoc _ _ _

/-- Refinement-directed Cech cohomology in a fixed degree, as a functor of coefficient
presheaves. -/
noncomputable def cechCohomologyCoefficientFunctor (n : ℕ) :
    TopCat.Presheaf A X ⥤ A where
  obj P := cechCohomology P n
  map f := cechCohomologyCoefficientMap f n
  map_id P := cechCohomologyCoefficientMap_id P n
  map_comp f g := cechCohomologyCoefficientMap_comp f g n

@[simp]
theorem cechCohomologyCoefficientFunctor_obj (n : ℕ) (P : TopCat.Presheaf A X) :
    (cechCohomologyCoefficientFunctor (A := A) n).obj P = cechCohomology P n :=
  rfl

@[simp]
theorem cechCohomologyCoefficientFunctor_map
    (n : ℕ) {P Q : TopCat.Presheaf A X} (f : P ⟶ Q) :
    (cechCohomologyCoefficientFunctor (A := A) n).map f =
      cechCohomologyCoefficientMap f n :=
  rfl

/-- Refinement-directed Cech cohomology in a fixed degree, functorial in abelian-sheaf
coefficients. -/
noncomputable def sheafCechCohomologyCoefficientFunctor (n : ℕ) :
    TopCat.Sheaf A X ⥤ A :=
  TopCat.Sheaf.forget A X ⋙ cechCohomologyCoefficientFunctor (A := A) n

@[simp]
theorem sheafCechCohomologyCoefficientFunctor_obj
    (n : ℕ) (F : TopCat.Sheaf A X) :
    (sheafCechCohomologyCoefficientFunctor (A := A) n).obj F =
      cechCohomology F.presheaf n :=
  rfl

@[simp]
theorem sheafCechCohomologyCoefficientFunctor_map
    (n : ℕ) {F G : TopCat.Sheaf A X} (f : F ⟶ G) :
    (sheafCechCohomologyCoefficientFunctor (A := A) n).map f =
      cechCohomologyCoefficientMap f.hom n :=
  rfl

end TopologicalSpace.OpenCover.SetOpenCover
