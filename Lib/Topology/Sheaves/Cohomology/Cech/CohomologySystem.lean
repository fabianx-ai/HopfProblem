/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.DirectedSystem

/-!
# Normalized Cech cohomology over the refinement-directed cover category

Normalized Cech cohomology in a fixed degree is a functor on the refinement-preordered category
of set-valued open covers.  Refinement pullbacks are strictly compatible with identities and with
composition already at the level of cochains, and two choices of a refinement function induce the
same map on cohomology, so a classical choice of refinement for each arrow of the thin cover
category defines the degreewise normalized Cech cohomology functor.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.7
* G. E. Bredon, *Sheaf Theory*, III.4
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s q

namespace TopologicalSpace.OpenCover

namespace OrderedCech

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]
variable {A : Type w} [Category.{t} A] [Preadditive A] [HasProducts.{v} A]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along the identity refinement is the identity cochain map. -/
@[simp]
theorem refinementMap_refl (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) :
    refinementMap P (Refinement.refl U) = 𝟙 (complex P U) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Limits.Pi.hom_ext
  intro sigma
  simp only [refinementMap_f, HomologicalComplex.id_f, Category.id_comp]
  change refinementMapDegree P (Refinement.refl U) n ≫ π P U n sigma = π P U n sigma
  rw [refinementMapDegree_π]
  dsimp [Refinement.refl, Refinement.orderedIntersectionHom, Function.comp_def,
    OrderedSimplex.intersection, IndexTuple.intersection, π]
  rw [alternatingEvaluation_ordered]
  dsimp [π, OrderedSimplex.intersection]
  rw [P.map_id]
  exact Category.comp_id _

section Composition

variable {κ : Type s} [LinearOrder κ] [HasProducts.{s} A]
variable {U : ι → TopologicalSpace.Opens X} {V : κ → TopologicalSpace.Opens X}

/-- Evaluation on an arbitrary fine tuple commutes with pullback along a refinement. -/
theorem refinementMapDegree_comp_alternatingEvaluation
    (P : TopCat.Presheaf A X) (r : Refinement V U) (n : ℕ)
    (f : Fin (n + 1) → κ) :
    refinementMapDegree P r n ≫ alternatingEvaluation P V n f =
      alternatingEvaluation P U n (r.index ∘ f) ≫ P.map (r.intersectionHom f).op := by
  by_cases hf : Function.Injective f
  · rw [alternatingEvaluation_of_injective P V n f hf]
    simp only [Preadditive.comp_zsmul, ← Category.assoc]
    rw [refinementMapDegree_π]
    let W := IndexTuple.intersection V f
    let sigma := IndexTuple.sortedSimplex f hf
    have hWsorted : W ≤ IndexTuple.intersection U (r.index ∘ (sigma : Fin (n + 1) → κ)) := by
      apply le_iInf
      intro j
      exact (iInf_le _ (Tuple.sort f j)).trans (r.le (f (Tuple.sort f j)))
    have hmaps :
        (r.orderedIntersectionHom sigma).op ≫
            eqToHom (congrArg op (IndexTuple.sortedSimplex_intersection V f hf)) =
          (CategoryTheory.homOfLE hWsorted).op := by
      subsingleton
    dsimp only [sigma] at hWsorted hmaps ⊢
    simp only [Category.assoc, ← P.map_comp, hmaps]
    have hWperm : W ≤
        IndexTuple.intersection U ((r.index ∘ f) ∘ Tuple.sort f) := by
      apply le_iInf
      intro j
      exact (iInf_le _ (Tuple.sort f j)).trans (r.le (f (Tuple.sort f j)))
    have htuple : (r.index ∘ f) ∘ Tuple.sort f =
        r.index ∘ (IndexTuple.sortedSimplex f hf : Fin (n + 1) → κ) := by
      funext j
      rfl
    have hequiv := alternatingEvaluation_comp_equiv P U n (r.index ∘ f)
      (Tuple.sort f) W hWperm (r.intersection_le f)
    have hsubPerm : IndexTuple.Subordinate U W
        ((r.index ∘ f) ∘ Tuple.sort f) :=
      fun j => hWperm.trans (iInf_le _ j)
    have hsubSorted : IndexTuple.Subordinate U W
        (r.index ∘ (IndexTuple.sortedSimplex f hf : Fin (n + 1) → κ)) :=
      fun j => hWsorted.trans (iInf_le _ j)
    have hsub : IndexTuple.Subordinate U W (r.index ∘ f) :=
      fun j => (r.intersection_le f).trans (iInf_le _ j)
    have hcongr := restrictedAlternatingEvaluation_congr P U n W htuple
      hsubPerm hsubSorted
    have hequivRestricted :
        restrictedAlternatingEvaluation P U n W
              ((r.index ∘ f) ∘ Tuple.sort f) hsubPerm =
          (Equiv.Perm.sign (Tuple.sort f) : ℤ) •
            restrictedAlternatingEvaluation P U n W (r.index ∘ f) hsub := by
      simpa only [restrictedAlternatingEvaluation, Refinement.intersectionHom] using hequiv
    have hequiv' :
        alternatingEvaluation P U n
              (r.index ∘ (IndexTuple.sortedSimplex f hf : Fin (n + 1) → κ)) ≫
            P.map (CategoryTheory.homOfLE hWsorted).op =
          (Equiv.Perm.sign (Tuple.sort f) : ℤ) •
            (alternatingEvaluation P U n (r.index ∘ f) ≫
              P.map (r.intersectionHom f).op) := by
      change restrictedAlternatingEvaluation P U n W
          (r.index ∘ (IndexTuple.sortedSimplex f hf : Fin (n + 1) → κ)) hsubSorted = _
      rw [← hcongr, hequivRestricted]
      rfl
    rw [hequiv']
    simp only [smul_smul]
    rw [show (Equiv.Perm.sign (Tuple.sort f) : ℤ) *
        (Equiv.Perm.sign (Tuple.sort f) : ℤ) = 1 by simp]
    exact one_smul _ _
  · have hrf : ¬ Function.Injective (r.index ∘ f) := by
      intro h
      apply hf
      intro a b hab
      exact h (congrArg r.index hab)
    rw [alternatingEvaluation_of_not_injective P V n f hf,
      alternatingEvaluation_of_not_injective P U n (r.index ∘ f) hrf]
    simp

variable {μ : Type q} [LinearOrder μ] [HasProducts.{q} A]
variable {W : μ → TopologicalSpace.Opens X}

/-- Refinement pullbacks compose in the refinement direction. -/
@[reassoc]
theorem refinementMap_comp (P : TopCat.Presheaf A X)
    (r : Refinement V U) (s : Refinement W V) :
    refinementMap (U := U) (V := W) P (r.comp s) =
      refinementMap (U := U) (V := V) P r ≫
        refinementMap (U := V) (V := W) P s := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Limits.Pi.hom_ext
  intro sigma
  simp only [refinementMap_f, HomologicalComplex.comp_f, Category.assoc]
  change refinementMapDegree P (r.comp s) n ≫ π P W n sigma =
    refinementMapDegree P r n ≫ refinementMapDegree P s n ≫ π P W n sigma
  rw [refinementMapDegree_π P (r.comp s) n sigma,
    refinementMapDegree_π P s n sigma]
  rw [← Category.assoc, refinementMapDegree_comp_alternatingEvaluation]
  simp only [Category.assoc, ← P.map_comp]
  let Z := sigma.intersection W
  let f₁ := (r.comp s).index ∘ (sigma : Fin (n + 1) → μ)
  let f₂ := r.index ∘ s.index ∘ (sigma : Fin (n + 1) → μ)
  have hf : f₁ = f₂ := by
    funext j
    rfl
  have hsub₁ : IndexTuple.Subordinate U Z f₁ :=
    (r.comp s).orderedSubordinate sigma
  have hsub₂ : IndexTuple.Subordinate U Z f₂ := by
    intro j
    exact ((iInf_le _ j).trans (s.le (sigma j))).trans (r.le (s.index (sigma j)))
  have hmaps :
      (r.intersectionHom (s.index ∘ (sigma : Fin (n + 1) → μ))).op ≫
          (s.orderedIntersectionHom sigma).op =
        (CategoryTheory.homOfLE hsub₂.intersection_le).op := by
    subsingleton
  rw [hmaps]
  change restrictedAlternatingEvaluation P U n Z f₁ hsub₁ =
    restrictedAlternatingEvaluation P U n Z f₂ hsub₂
  exact restrictedAlternatingEvaluation_congr P U n Z hf hsub₁ hsub₂

end Composition

end OrderedCech

namespace SetOpenCover

variable {X : TopCat.{u}}
variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]

/-- The normalized ordered Cech complex of a set-valued open cover.  The index subtype carries
the arbitrary well-order fixed in `SetOpenCover.indexLinearOrder`. -/
@[implicit_reducible]
noncomputable def normalizedCechComplex (P : TopCat.Presheaf A X)
    (U : SetOpenCover X) : CochainComplex A ℕ :=
  OrderedCech.complex P U.family

/-- The degree-`n` term of the normalized Cech complex of a cover is the normalized Cech object
of its underlying family. -/
@[simp]
theorem normalizedCechComplex_X (P : TopCat.Presheaf A X)
    (U : SetOpenCover X) (n : ℕ) :
    (normalizedCechComplex P U).X n = OrderedCech.object P U.family n :=
  rfl

variable [CategoryWithHomology A]

/-- Degree-`n` normalized Cech cohomology of one set-valued open cover. -/
@[implicit_reducible]
noncomputable def normalizedCechCohomology (P : TopCat.Presheaf A X)
    (U : SetOpenCover X) (n : ℕ) : A :=
  (normalizedCechComplex P U).homology n

/-- The map on normalized Cech cohomology induced by an inequality in the refinement preorder.
The underlying refinement function is chosen classically. -/
noncomputable def normalizedCechCohomologyMap (P : TopCat.Presheaf A X)
    {U V : SetOpenCover X} (h : U ≤ V) (n : ℕ) :
    normalizedCechCohomology P U n ⟶ normalizedCechCohomology P V n :=
  HomologicalComplex.homologyMap
    (OrderedCech.refinementMap P (refinementOfLE h)) n

/-- The cohomology map selected for an arrow agrees with the map induced by any refinement
function witnessing that arrow. -/
theorem normalizedCechCohomologyMap_eq (P : TopCat.Presheaf A X)
    {U V : SetOpenCover X} (h : U ≤ V) (r : Refinement V.family U.family) (n : ℕ) :
    normalizedCechCohomologyMap P h n =
      HomologicalComplex.homologyMap (OrderedCech.refinementMap P r) n :=
  OrderedCech.refinementMap_homologyMap_eq P (refinementOfLE h) r n

/-- For a fixed coefficient presheaf and degree, normalized Cech cohomology is a functor from
the filtered refinement preorder of set-valued open covers. -/
noncomputable def normalizedCechCohomologyFunctor (P : TopCat.Presheaf A X) (n : ℕ) :
    SetOpenCover X ⥤ A where
  obj U := normalizedCechCohomology P U n
  map {U V} f := normalizedCechCohomologyMap P (leOfHom f) n
  map_id U := by
    rw [normalizedCechCohomologyMap_eq P _ (Refinement.refl U.family) n,
      OrderedCech.refinementMap_refl, HomologicalComplex.homologyMap_id]
    rfl
  map_comp {U V W} f g := by
    let r := refinementOfLE (leOfHom f)
    let s := refinementOfLE (leOfHom g)
    calc
      normalizedCechCohomologyMap P (leOfHom (f ≫ g)) n =
          HomologicalComplex.homologyMap
            (OrderedCech.refinementMap P (r.comp s)) n :=
        normalizedCechCohomologyMap_eq P _ (r.comp s) n
      _ = HomologicalComplex.homologyMap
            (OrderedCech.refinementMap P r ≫ OrderedCech.refinementMap P s) n := by
        rw [OrderedCech.refinementMap_comp]
      _ = HomologicalComplex.homologyMap (OrderedCech.refinementMap P r) n ≫
            HomologicalComplex.homologyMap (OrderedCech.refinementMap P s) n :=
        HomologicalComplex.homologyMap_comp
          (OrderedCech.refinementMap P r) (OrderedCech.refinementMap P s) n
      _ = normalizedCechCohomologyMap P (leOfHom f) n ≫
            normalizedCechCohomologyMap P (leOfHom g) n := by
        rfl

/-- The Cech cohomology functor sends a cover to the normalized Cech cohomology of that cover. -/
@[simp]
theorem normalizedCechCohomologyFunctor_obj (P : TopCat.Presheaf A X)
    (n : ℕ) (U : SetOpenCover X) :
    (normalizedCechCohomologyFunctor P n).obj U = normalizedCechCohomology P U n :=
  rfl

/-- The Cech cohomology functor sends a refinement arrow to the refinement map on normalized
Cech cohomology. -/
@[simp]
theorem normalizedCechCohomologyFunctor_map (P : TopCat.Presheaf A X)
    (n : ℕ) {U V : SetOpenCover X} (f : U ⟶ V) :
    (normalizedCechCohomologyFunctor P n).map f =
      normalizedCechCohomologyMap P (leOfHom f) n :=
  rfl

end SetOpenCover

end TopologicalSpace.OpenCover
