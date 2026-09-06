/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.CohomologySystem

/-!
# Functoriality of normalized Cech cohomology in the coefficients

This file supplies the coefficient functoriality implicit in the natural comparison of textbook
section CD-05. A morphism of coefficient presheaves acts componentwise on the normalized ordered
Cech complex. The resulting cochain map is functorial and commutes with every chosen refinement
map. Passing to homology gives the corresponding naturality square for normalized fixed-cover
Cech cohomology.

No direct-limit comparison, effaceability assertion, or derived-functor identification is made
here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s

namespace TopologicalSpace.OpenCover

namespace OrderedCech

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]
variable {A : Type w} [Category.{t} A] [Preadditive A] [HasProducts.{v} A]
variable {P Q R : TopCat.Presheaf A X}

/-- The degreewise map on normalized Cech cochains induced by a morphism of coefficient
presheaves. -/
noncomputable def coefficientMapDegree (f : P ⟶ Q)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    object P U n ⟶ object Q U n :=
  Limits.Pi.map fun σ => f.app (op (σ.intersection U))

omit [Preadditive A] in
/-- Component formula for the map induced by a coefficient morphism. -/
@[reassoc (attr := simp)]
theorem coefficientMapDegree_π (f : P ⟶ Q)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (σ : OrderedSimplex ι n) :
    coefficientMapDegree f U n ≫ π Q U n σ =
      π P U n σ ≫ f.app (op (σ.intersection U)) :=
  Limits.Pi.map_π _ _

/-- Coefficient maps commute with the normalized Cech differential. -/
theorem coefficientMapDegree_comp_differential (f : P ⟶ Q)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    coefficientMapDegree f U n ≫ differential Q U n =
      differential P U n ≫ coefficientMapDegree f U (n + 1) := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [Category.assoc]
  change coefficientMapDegree f U n ≫
      (differential Q U n ≫ π Q U (n + 1) σ) =
    differential P U n ≫
      (coefficientMapDegree f U (n + 1) ≫ π Q U (n + 1) σ)
  rw [differential_π, coefficientMapDegree_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    coefficientMapDegree_π_assoc]
  rw [← Category.assoc, differential_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← f.naturality]

/-- The morphism of normalized Cech complexes induced by a morphism of coefficient
presheaves. -/
noncomputable def coefficientMap (f : P ⟶ Q)
    (U : ι → TopologicalSpace.Opens X) :
    complex P U ⟶ complex Q U :=
  CochainComplex.ofHom (coefficientMapDegree f U) fun n => by
    simpa only [complex_d] using coefficientMapDegree_comp_differential f U n

/-- Degreewise description of the normalized Cech coefficient map. -/
@[simp]
theorem coefficientMap_f (f : P ⟶ Q)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    (coefficientMap f U).f n = coefficientMapDegree f U n :=
  rfl

/-- The identity coefficient morphism induces the identity normalized Cech cochain map. -/
@[simp]
theorem coefficientMap_id (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) :
    coefficientMap (𝟙 P) U = 𝟙 (complex P U) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Limits.Pi.hom_ext
  intro σ
  rw [coefficientMap_f, HomologicalComplex.id_f, Category.id_comp]
  calc
    coefficientMapDegree (𝟙 P) U n ≫ π P U n σ =
        π P U n σ ≫ (𝟙 P : P ⟶ P).app (op (σ.intersection U)) :=
      coefficientMapDegree_π (P := P) (Q := P) (𝟙 P) U n σ
    _ = π P U n σ := by
      change π P U n σ ≫ 𝟙 _ = π P U n σ
      exact Category.comp_id _

/-- Coefficient maps compose in the expected order. -/
@[reassoc]
theorem coefficientMap_comp (f : P ⟶ Q) (g : Q ⟶ R)
    (U : ι → TopologicalSpace.Opens X) :
    coefficientMap (f ≫ g) U = coefficientMap f U ≫ coefficientMap g U := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Limits.Pi.hom_ext
  intro σ
  simp [coefficientMap, coefficientMapDegree]

/-- Alternating evaluation is natural in the coefficient presheaf. -/
theorem coefficientMapDegree_comp_alternatingEvaluation (f : P ⟶ Q)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ)
    (a : Fin (n + 1) → ι) :
    coefficientMapDegree f U n ≫ alternatingEvaluation Q U n a =
      alternatingEvaluation P U n a ≫
        f.app (op (IndexTuple.intersection U a)) := by
  by_cases ha : Function.Injective a
  · rw [alternatingEvaluation_of_injective P U n a ha,
      alternatingEvaluation_of_injective Q U n a ha]
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
      coefficientMapDegree_π_assoc]
    congr 1
    rw [← f.naturality]
  · rw [alternatingEvaluation_of_not_injective P U n a ha,
      alternatingEvaluation_of_not_injective Q U n a ha, comp_zero, zero_comp]

section Refinement

variable {κ : Type s} [LinearOrder κ] [HasProducts.{s} A]
variable {U : ι → TopologicalSpace.Opens X} {V : κ → TopologicalSpace.Opens X}

/-- Changing coefficients commutes with pullback along a chosen refinement. -/
theorem coefficientMap_comp_refinementMap (f : P ⟶ Q) (r : Refinement V U) :
    coefficientMap f U ≫ refinementMap (U := U) (V := V) Q r =
      refinementMap (U := U) (V := V) P r ≫ coefficientMap f V := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Limits.Pi.hom_ext
  intro σ
  change (coefficientMapDegree f U n ≫ refinementMapDegree Q r n) ≫ π Q V n σ =
    (refinementMapDegree P r n ≫ coefficientMapDegree f V n) ≫ π Q V n σ
  calc
    (coefficientMapDegree f U n ≫ refinementMapDegree Q r n) ≫ π Q V n σ =
        coefficientMapDegree f U n ≫
          (alternatingEvaluation Q U n (r.index ∘ σ) ≫
            Q.map (r.orderedIntersectionHom σ).op) := by
      rw [Category.assoc, refinementMapDegree_π]
    _ = (coefficientMapDegree f U n ≫
          alternatingEvaluation Q U n (r.index ∘ σ)) ≫
            Q.map (r.orderedIntersectionHom σ).op :=
      (Category.assoc _ _ _).symm
    _ = (alternatingEvaluation P U n (r.index ∘ σ) ≫
          f.app (op (IndexTuple.intersection U (r.index ∘ σ)))) ≫
            Q.map (r.orderedIntersectionHom σ).op := by
      rw [coefficientMapDegree_comp_alternatingEvaluation]
    _ = alternatingEvaluation P U n (r.index ∘ σ) ≫
          (f.app (op (IndexTuple.intersection U (r.index ∘ σ))) ≫
            Q.map (r.orderedIntersectionHom σ).op) :=
      Category.assoc _ _ _
    _ = alternatingEvaluation P U n (r.index ∘ σ) ≫
          (P.map (r.orderedIntersectionHom σ).op ≫
            f.app (op (σ.intersection V))) := by
      rw [← f.naturality]
    _ = (alternatingEvaluation P U n (r.index ∘ σ) ≫
          P.map (r.orderedIntersectionHom σ).op) ≫
            f.app (op (σ.intersection V)) :=
      (Category.assoc _ _ _).symm
    _ = (refinementMapDegree P r n ≫ π P V n σ) ≫
          f.app (op (σ.intersection V)) := by
      rw [refinementMapDegree_π]
    _ = refinementMapDegree P r n ≫
          (coefficientMapDegree f V n ≫ π Q V n σ) := by
      rw [coefficientMapDegree_π]
      exact Category.assoc _ _ _
    _ = (refinementMapDegree P r n ≫ coefficientMapDegree f V n) ≫
          π Q V n σ :=
      (Category.assoc _ _ _).symm

end Refinement

end OrderedCech

namespace SetOpenCover

variable {X : TopCat.{u}}
variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]
  [CategoryWithHomology A]
variable {P Q R : TopCat.Presheaf A X}

/-- The map on normalized fixed-cover Cech complexes induced by a coefficient morphism. -/
noncomputable def normalizedCechComplexMap (f : P ⟶ Q) (U : SetOpenCover X) :
    normalizedCechComplex P U ⟶ normalizedCechComplex Q U :=
  OrderedCech.coefficientMap f U.family

/-- The map on normalized fixed-cover Cech cohomology induced by a coefficient morphism. -/
noncomputable def normalizedCechCohomologyCoefficientMap
    (f : P ⟶ Q) (U : SetOpenCover X) (n : ℕ) :
    normalizedCechCohomology P U n ⟶ normalizedCechCohomology Q U n :=
  HomologicalComplex.homologyMap (normalizedCechComplexMap f U) n

/-- Changing coefficients commutes with the map on normalized Cech cohomology induced by a
refinement in the thin cover preorder. -/
theorem normalizedCechCohomologyCoefficientMap_comp_refinement
    (f : P ⟶ Q) {U V : SetOpenCover X} (h : U ≤ V) (n : ℕ) :
    normalizedCechCohomologyCoefficientMap f U n ≫
        normalizedCechCohomologyMap Q h n =
      normalizedCechCohomologyMap P h n ≫
        normalizedCechCohomologyCoefficientMap f V n := by
  rw [normalizedCechCohomologyMap_eq Q h (refinementOfLE h) n,
    normalizedCechCohomologyMap_eq P h (refinementOfLE h) n]
  simpa only [normalizedCechCohomologyCoefficientMap, normalizedCechComplexMap,
    HomologicalComplex.homologyMap_comp] using
    congrArg (fun k => HomologicalComplex.homologyMap k n)
      (OrderedCech.coefficientMap_comp_refinementMap f (refinementOfLE h))

/-- For one set-valued cover, normalized Cech cohomology is functorial in the coefficient
presheaf. -/
noncomputable def normalizedCechCohomologyCoefficientFunctor
    (U : SetOpenCover X) (n : ℕ) : TopCat.Presheaf A X ⥤ A where
  obj P := normalizedCechCohomology P U n
  map f := normalizedCechCohomologyCoefficientMap f U n
  map_id P := by
    dsimp only [normalizedCechCohomologyCoefficientMap, normalizedCechComplexMap]
    rw [OrderedCech.coefficientMap_id]
    exact HomologicalComplex.homologyMap_id (OrderedCech.complex P U.family) n
  map_comp f g := by
    dsimp only [normalizedCechCohomologyCoefficientMap, normalizedCechComplexMap]
    rw [OrderedCech.coefficientMap_comp, HomologicalComplex.homologyMap_comp]

@[simp]
theorem normalizedCechCohomologyCoefficientFunctor_obj
    (U : SetOpenCover X) (n : ℕ) (P : TopCat.Presheaf A X) :
    (normalizedCechCohomologyCoefficientFunctor (A := A) U n).obj P =
      normalizedCechCohomology P U n :=
  rfl

@[simp]
theorem normalizedCechCohomologyCoefficientFunctor_map
    (U : SetOpenCover X) (n : ℕ) {P Q : TopCat.Presheaf A X} (f : P ⟶ Q) :
    (normalizedCechCohomologyCoefficientFunctor (A := A) U n).map f =
      normalizedCechCohomologyCoefficientMap f U n :=
  rfl

end SetOpenCover

end TopologicalSpace.OpenCover
