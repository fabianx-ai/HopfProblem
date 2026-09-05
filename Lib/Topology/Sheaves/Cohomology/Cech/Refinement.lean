/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.Ordered
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Alternating evaluation for normalized Čech cochains

This file begins the refinement-map portion of textbook section CD-04. A chosen refinement
function between index sets need not preserve the chosen orders and need not be injective on an
ordered simplex. Consequently, its image cannot in general be used directly as an
`OrderedSimplex`.

For an arbitrary index tuple, the normalized cochain is therefore evaluated by the standard
alternating extension: a tuple with a repeated index is sent to zero, while an injective tuple is
sorted and its ordered component is multiplied by the sign of the sorting permutation. The
codomain is transported along the equality between the sorted and unsorted open intersections.

This independently shippable sub-boundary introduces no refinement cochain map, homotopy between
refinement choices, direct limit, or comparison with derived sheaf cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace TopologicalSpace.OpenCover

namespace IndexTuple

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}
variable {n : ℕ}

/-- The open intersection indexed by an arbitrary tuple, before imposing alternation. -/
def intersection (U : ι → TopologicalSpace.Opens X) (f : Fin (n + 1) → ι) :
    TopologicalSpace.Opens X :=
  ⨅ j, U (f j)

/-- Reindexing a tuple by a permutation does not change its open intersection. -/
theorem intersection_comp_equiv (U : ι → TopologicalSpace.Opens X)
    (f : Fin (n + 1) → ι) (e : Equiv.Perm (Fin (n + 1))) :
    intersection U (f ∘ e) = intersection U f := by
  exact e.surjective.iInf_comp (fun j ↦ U (f j))

variable [LinearOrder ι]

/-- Sorting an injective tuple produces the corresponding strictly increasing Čech simplex. -/
def sortedSimplex (f : Fin (n + 1) → ι) (hf : Function.Injective f) :
    OrderedSimplex ι n :=
  OrderEmbedding.ofStrictMono (f ∘ Tuple.sort f)
    ((Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective))

/-- The sorted simplex evaluates as the original tuple after its sorting permutation. -/
@[simp]
theorem sortedSimplex_apply (f : Fin (n + 1) → ι) (hf : Function.Injective f)
    (j : Fin (n + 1)) :
    sortedSimplex f hf j = f (Tuple.sort f j) :=
  rfl

/-- The open indexed by the sorted simplex is the open indexed by the original tuple. -/
theorem sortedSimplex_intersection (U : ι → TopologicalSpace.Opens X)
    (f : Fin (n + 1) → ι) (hf : Function.Injective f) :
    (sortedSimplex f hf).intersection U = intersection U f := by
  change (⨅ j, U (f (Tuple.sort f j))) = ⨅ j, U (f j)
  exact (Tuple.sort f).surjective.iInf_comp (fun j ↦ U (f j))

/-- Sorting a tuple which is already strictly increasing recovers that ordered simplex. -/
@[simp]
theorem sortedSimplex_coe (f : OrderedSimplex ι n) :
    sortedSimplex (fun j ↦ f j) f.injective = f := by
  ext j
  simp only [sortedSimplex_apply]
  rw [Tuple.sort_eq_refl_iff_monotone.mpr f.monotone]
  rfl

end IndexTuple

namespace OrderedCech

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]
variable {A : Type w} [Category.{t} A] [Preadditive A] [HasProducts.{v} A]

/-- Evaluate a normalized ordered Čech cochain on an arbitrary index tuple.

If the tuple has a repeated index, alternation makes the evaluation zero. Otherwise `Tuple.sort`
produces its ordered simplex, and the ordered projection is multiplied by the sign of that
sorting permutation. -/
noncomputable def alternatingEvaluation (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : Fin (n + 1) → ι) :
    object P U n ⟶ P.obj (op (IndexTuple.intersection U f)) :=
  if hf : Function.Injective f then
    (Equiv.Perm.sign (Tuple.sort f) : ℤ) •
      (π P U n (IndexTuple.sortedSimplex f hf) ≫
        P.map (eqToHom (congrArg op (IndexTuple.sortedSimplex_intersection U f hf))))
  else
    0

/-- Alternating evaluation vanishes on a tuple with a repeated index. -/
@[simp]
theorem alternatingEvaluation_of_not_injective (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : Fin (n + 1) → ι)
    (hf : ¬ Function.Injective f) :
    alternatingEvaluation P U n f = 0 := by
  simp [alternatingEvaluation, hf]

/-- On an injective tuple, alternating evaluation is the signed projection at its sorted
simplex, transported to the unsorted intersection. -/
theorem alternatingEvaluation_of_injective (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : Fin (n + 1) → ι)
    (hf : Function.Injective f) :
    alternatingEvaluation P U n f =
      (Equiv.Perm.sign (Tuple.sort f) : ℤ) •
        (π P U n (IndexTuple.sortedSimplex f hf) ≫
          P.map (eqToHom (congrArg op (IndexTuple.sortedSimplex_intersection U f hf)))) := by
  simp [alternatingEvaluation, hf]

omit [Preadditive A] in
private theorem π_comp_map_eqToHom (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) {f g : OrderedSimplex ι n}
    (h : f = g) :
    π P U n f ≫
        P.map (eqToHom (congrArg (fun σ ↦ op (σ.intersection U)) h)) =
      π P U n g := by
  subst g
  simp

/-- Alternating evaluation on an already ordered simplex is its product projection. -/
@[simp]
theorem alternatingEvaluation_ordered (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : OrderedSimplex ι n) :
    alternatingEvaluation P U n (fun j ↦ f j) = π P U n f := by
  rw [alternatingEvaluation_of_injective P U n _ f.injective]
  have hsort : Tuple.sort (fun j ↦ f j) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr f.monotone
  rw [show (Equiv.Perm.sign (Tuple.sort (fun j ↦ f j)) : ℤ) = 1 by simp [hsort]]
  simp only [one_zsmul]
  simpa only [IndexTuple.intersection, OrderedSimplex.intersection] using
    π_comp_map_eqToHom P U n (IndexTuple.sortedSimplex_coe f)

end OrderedCech

end TopologicalSpace.OpenCover
