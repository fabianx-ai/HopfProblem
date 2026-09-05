/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.Ordered
public import Lib.Topology.Dimension.Covering
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Refinement pullbacks for normalized Čech cochains

This file begins the refinement-map portion of textbook section CD-04. A chosen refinement
function between index sets need not preserve the chosen orders and need not be injective on an
ordered simplex. Consequently, its image cannot in general be used directly as an
`OrderedSimplex`.

For an arbitrary index tuple, the normalized cochain is therefore evaluated by the standard
alternating extension: a tuple with a repeated index is sent to zero, while an injective tuple is
sorted and its ordered component is multiplied by the sign of the sorting permutation. The
codomain is transported along the equality between the sorted and unsorted open intersections.

The arbitrary-tuple coboundary identity then shows that evaluation along a chosen refinement,
followed by restriction to the fine intersection, defines a morphism of normalized ordered Čech
cochain complexes. This file makes no claim that different refinement choices induce equal or
homotopic maps, and introduces no direct limit or comparison with derived sheaf cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s

namespace TopologicalSpace.OpenCover

namespace IndexTuple

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}
variable {n : ℕ}

/-- The open intersection indexed by an arbitrary tuple, before imposing alternation. -/
def intersection (U : ι → TopologicalSpace.Opens X) (f : Fin (n + 1) → ι) :
    TopologicalSpace.Opens X :=
  ⨅ j, U (f j)

/-- Delete one entry from an arbitrary index tuple. -/
def face (f : Fin (n + 2) → ι) (k : Fin (n + 2)) : Fin (n + 1) → ι :=
  f ∘ k.succAbove

/-- An arbitrary tuple intersection is contained in each of its face intersections. -/
theorem intersection_le_face (U : ι → TopologicalSpace.Opens X)
    (f : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    intersection U f ≤ intersection U (face f k) := by
  apply le_iInf
  intro j
  exact iInf_le _ (k.succAbove j)

/-- The inclusion from an arbitrary tuple intersection to one of its face intersections. -/
def faceHom (U : ι → TopologicalSpace.Opens X)
    (f : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    intersection U f ⟶ intersection U (face f k) :=
  CategoryTheory.homOfLE (intersection_le_face U f k)

/-- Reindexing a tuple by a permutation does not change its open intersection. -/
theorem intersection_comp_equiv (U : ι → TopologicalSpace.Opens X)
    (f : Fin (n + 1) → ι) (e : Equiv.Perm (Fin (n + 1))) :
    intersection U (f ∘ e) = intersection U f := by
  exact e.surjective.iInf_comp (fun j ↦ U (f j))

/-- Delete from a permutation the source position `l` and its image. -/
def deletePerm (p : Equiv.Perm (Fin (n + 2))) (l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin
    (Fin.cycleRange (p l) * p * (Fin.cycleRange l)⁻¹)).2

/-- The deleted permutation intertwines the two order-preserving embeddings which omit the
deleted source position and its image. -/
theorem succAbove_deletePerm (p : Equiv.Perm (Fin (n + 2)))
    (l : Fin (n + 2)) (j : Fin (n + 1)) :
    (p l).succAbove (deletePerm p l j) = p (l.succAbove j) := by
  let q := Fin.cycleRange (p l) * p * (Fin.cycleRange l)⁻¹
  let e := (Equiv.Perm.decomposeFin q).2
  have hq0 : q 0 = 0 := by
    simp [q, Equiv.Perm.mul_apply]
  have hfst : (Equiv.Perm.decomposeFin q).1 = 0 := by
    have hfirst : (Equiv.Perm.decomposeFin q).1 = q 0 := by
      calc
        (Equiv.Perm.decomposeFin q).1 =
            (Equiv.Perm.decomposeFin.symm
              ((Equiv.Perm.decomposeFin q).1, (Equiv.Perm.decomposeFin q).2)) 0 :=
          (Equiv.Perm.decomposeFin_symm_apply_zero _ _).symm
        _ = (Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin q)) 0 := by
          rw [Prod.eta]
        _ = q 0 := by rw [Equiv.Perm.decomposeFin.symm_apply_apply]
    exact hfirst.trans hq0
  have hq : q = Equiv.Perm.decomposeFin.symm (0, e) := by
    apply Equiv.Perm.decomposeFin.injective
    rw [Equiv.Perm.decomposeFin.apply_symm_apply]
    exact Prod.ext hfst rfl
  apply (Fin.cycleRange (p l)).injective
  rw [Fin.cycleRange_succAbove]
  calc
    (deletePerm p l j).succ = (e j).succ := by rfl
    _ = q j.succ := by rw [hq]; simp
    _ = Fin.cycleRange (p l) (p (l.succAbove j)) := by
      simp [q, Equiv.Perm.mul_apply]

/-- Deleting a source position and its image changes the sign by the two corresponding
alternating boundary signs. -/
theorem sign_deletePerm (p : Equiv.Perm (Fin (n + 2))) (l : Fin (n + 2)) :
    (Equiv.Perm.sign (deletePerm p l) : ℤ) =
      (-1 : ℤ) ^ (p l : ℕ) * (Equiv.Perm.sign p : ℤ) * (-1 : ℤ) ^ (l : ℕ) := by
  let q := Fin.cycleRange (p l) * p * (Fin.cycleRange l)⁻¹
  let e := (Equiv.Perm.decomposeFin q).2
  have hq0 : q 0 = 0 := by
    simp [q, Equiv.Perm.mul_apply]
  have hfst : (Equiv.Perm.decomposeFin q).1 = 0 := by
    have hfirst : (Equiv.Perm.decomposeFin q).1 = q 0 := by
      calc
        (Equiv.Perm.decomposeFin q).1 =
            (Equiv.Perm.decomposeFin.symm
              ((Equiv.Perm.decomposeFin q).1, (Equiv.Perm.decomposeFin q).2)) 0 :=
          (Equiv.Perm.decomposeFin_symm_apply_zero _ _).symm
        _ = (Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin q)) 0 := by
          rw [Prod.eta]
        _ = q 0 := by rw [Equiv.Perm.decomposeFin.symm_apply_apply]
    exact hfirst.trans hq0
  have hq : q = Equiv.Perm.decomposeFin.symm (0, e) := by
    apply Equiv.Perm.decomposeFin.injective
    rw [Equiv.Perm.decomposeFin.apply_symm_apply]
    exact Prod.ext hfst rfl
  have hsign : Equiv.Perm.sign q = Equiv.Perm.sign e := by
    rw [hq, Equiv.Perm.decomposeFin.symm_sign]
    simp
  calc
    (Equiv.Perm.sign (deletePerm p l) : ℤ) = (Equiv.Perm.sign e : ℤ) := by rfl
    _ = (Equiv.Perm.sign q : ℤ) := congrArg ((↑) : ℤˣ → ℤ) hsign.symm
    _ = (-1 : ℤ) ^ (p l : ℕ) * (Equiv.Perm.sign p : ℤ) *
        (-1 : ℤ) ^ (l : ℕ) := by
      simp [q, Equiv.Perm.sign_mul]

variable [LinearOrder ι]

/-- Deleting an entry after sorting is governed by the deleted sorting permutation. -/
theorem deletePerm_sort_eq_sort_face (f : Fin (n + 2) → ι)
    (hf : Function.Injective f) (l : Fin (n + 2)) :
    deletePerm (Tuple.sort f) l = Tuple.sort (face f (Tuple.sort f l)) := by
  let p := Tuple.sort f
  let g := face f (p l)
  have hg : Function.Injective g := hf.comp Fin.succAbove_right_injective
  have hcomp : g ∘ deletePerm p l = (f ∘ p) ∘ l.succAbove := by
    funext j
    exact congrArg f (succAbove_deletePerm p l j)
  have hstrict : StrictMono (f ∘ p) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp p.injective)
  have hmono : Monotone (g ∘ deletePerm p l) := by
    rw [hcomp]
    exact (hstrict.comp (Fin.succAboveOrderEmb l).strictMono).monotone
  apply Equiv.ext
  intro j
  apply hg
  exact congrFun (Tuple.comp_sort_eq_comp_iff_monotone.mpr hmono) j

/-- The face-sorting sign is the product of the original sorting sign and the two boundary
signs attached to the deleted position before and after sorting. -/
theorem sign_sort_face (f : Fin (n + 2) → ι) (hf : Function.Injective f)
    (l : Fin (n + 2)) :
    (-1 : ℤ) ^ (Tuple.sort f l : ℕ) *
        (Equiv.Perm.sign (Tuple.sort (face f (Tuple.sort f l))) : ℤ) =
      (Equiv.Perm.sign (Tuple.sort f) : ℤ) * (-1 : ℤ) ^ (l : ℕ) := by
  rw [← deletePerm_sort_eq_sort_face f hf l, sign_deletePerm]
  have heven : (Tuple.sort f l : ℕ) + (Tuple.sort f l : ℕ) =
      2 * (Tuple.sort f l : ℕ) := by omega
  have hsquare : (-1 : ℤ) ^ (Tuple.sort f l : ℕ) *
      (-1 : ℤ) ^ (Tuple.sort f l : ℕ) = 1 := by
    rw [← pow_add, heven, pow_mul]
    simp
  calc
    (-1 : ℤ) ^ (Tuple.sort f l : ℕ) *
          ((-1 : ℤ) ^ (Tuple.sort f l : ℕ) *
            (Equiv.Perm.sign (Tuple.sort f) : ℤ) * (-1 : ℤ) ^ (l : ℕ)) =
        ((-1 : ℤ) ^ (Tuple.sort f l : ℕ) *
          (-1 : ℤ) ^ (Tuple.sort f l : ℕ)) *
            ((Equiv.Perm.sign (Tuple.sort f) : ℤ) * (-1 : ℤ) ^ (l : ℕ)) := by
      ring
    _ = (Equiv.Perm.sign (Tuple.sort f) : ℤ) * (-1 : ℤ) ^ (l : ℕ) := by
      rw [hsquare, one_mul]

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

/-- Sorting a face of an injective tuple gives the corresponding face of the sorted simplex. -/
theorem sortedSimplex_face (f : Fin (n + 2) → ι) (hf : Function.Injective f)
    (l : Fin (n + 2)) :
    sortedSimplex (face f (Tuple.sort f l))
        (hf.comp Fin.succAbove_right_injective) =
      (sortedSimplex f hf).face l := by
  ext j
  change f ((Tuple.sort f l).succAbove
      (Tuple.sort (face f (Tuple.sort f l)) j)) =
    f (Tuple.sort f (l.succAbove j))
  rw [← deletePerm_sort_eq_sort_face f hf l]
  exact congrArg f (succAbove_deletePerm (Tuple.sort f) l j)

end IndexTuple

namespace Refinement

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} {κ : Type w}
variable {U : ι → TopologicalSpace.Opens X} {V : κ → TopologicalSpace.Opens X}

/-- A refinement contains the fine tuple intersection in the coarse intersection selected by
its index function. -/
theorem intersection_le (r : Refinement V U) {n : ℕ} (f : Fin (n + 1) → κ) :
    IndexTuple.intersection V f ≤ IndexTuple.intersection U (r.index ∘ f) := by
  apply le_iInf
  intro j
  exact (iInf_le _ j).trans (r.le (f j))

/-- The inclusion from a fine tuple intersection to its selected coarse tuple intersection. -/
def intersectionHom (r : Refinement V U) {n : ℕ} (f : Fin (n + 1) → κ) :
    IndexTuple.intersection V f ⟶ IndexTuple.intersection U (r.index ∘ f) :=
  CategoryTheory.homOfLE (r.intersection_le f)

/-- The inclusion from an ordered fine intersection to the coarse tuple intersection selected
by a refinement. -/
def orderedIntersectionHom [LinearOrder κ] (r : Refinement V U) {n : ℕ}
    (σ : OrderedSimplex κ n) :
    σ.intersection V ⟶ IndexTuple.intersection U (r.index ∘ σ) :=
  CategoryTheory.homOfLE (by
    simpa only [OrderedSimplex.intersection, IndexTuple.intersection] using
      r.intersection_le (fun j ↦ σ j))

end Refinement

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

private theorem alternatingEvaluation_face_of_injective (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : Fin (n + 2) → ι)
    (hf : Function.Injective f) (l : Fin (n + 2)) :
    (-1 : ℤ) ^ (Tuple.sort f l : ℕ) •
        (alternatingEvaluation P U n (IndexTuple.face f (Tuple.sort f l)) ≫
          P.map (IndexTuple.faceHom U f (Tuple.sort f l)).op) =
      ((Equiv.Perm.sign (Tuple.sort f) : ℤ) * (-1 : ℤ) ^ (l : ℕ)) •
        (π P U n ((IndexTuple.sortedSimplex f hf).face l) ≫
          P.map (((IndexTuple.sortedSimplex f hf).faceHom U l).op) ≫
          P.map (eqToHom
            (congrArg op (IndexTuple.sortedSimplex_intersection U f hf)))) := by
  have hface : Function.Injective (IndexTuple.face f (Tuple.sort f l)) :=
    hf.comp Fin.succAbove_right_injective
  rw [alternatingEvaluation_of_injective P U n _ hface]
  simp only [Preadditive.zsmul_comp, smul_smul, Category.assoc, ← P.map_comp]
  rw [IndexTuple.sign_sort_face f hf l]
  congr 1
  let hs := IndexTuple.sortedSimplex_face f hf l
  rw [← π_comp_map_eqToHom P U n hs]
  simp only [Category.assoc, ← P.map_comp]
  congr 1

private theorem differential_comp_alternatingEvaluation_of_injective
    (P : TopCat.Presheaf A X) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (f : Fin (n + 2) → ι) (hf : Function.Injective f) :
    differential P U n ≫ alternatingEvaluation P U (n + 1) f =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (alternatingEvaluation P U n (IndexTuple.face f k) ≫
          P.map (IndexTuple.faceHom U f k).op) := by
  rw [alternatingEvaluation_of_injective P U (n + 1) f hf]
  simp only [Preadditive.comp_zsmul]
  rw [← Category.assoc, differential_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Finset.smul_sum, smul_smul,
    Category.assoc]
  rw [← Equiv.sum_comp (Tuple.sort f) (fun k : Fin (n + 2) ↦
    (-1 : ℤ) ^ (k : ℕ) •
      (alternatingEvaluation P U n (IndexTuple.face f k) ≫
        P.map (IndexTuple.faceHom U f k).op))]
  apply Finset.sum_congr rfl
  intro l _
  exact (alternatingEvaluation_face_of_injective P U n f hf l).symm

/-- Alternating evaluation changes by the sign of a permutation. The two sides are restricted to
a common smaller open so that the statement is independent of equality transports between the
two presentations of the same tuple intersection. -/
theorem alternatingEvaluation_comp_equiv (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : Fin (n + 1) → ι)
    (e : Equiv.Perm (Fin (n + 1))) (W : TopologicalSpace.Opens X)
    (hfe : W ≤ IndexTuple.intersection U (f ∘ e))
    (hf : W ≤ IndexTuple.intersection U f) :
    alternatingEvaluation P U n (f ∘ e) ≫
        P.map (CategoryTheory.homOfLE hfe).op =
      (Equiv.Perm.sign e : ℤ) •
        (alternatingEvaluation P U n f ≫
          P.map (CategoryTheory.homOfLE hf).op) := by
  by_cases hinj : Function.Injective f
  · have hinje : Function.Injective (f ∘ e) := hinj.comp e.injective
    rw [alternatingEvaluation_of_injective P U n _ hinje,
      alternatingEvaluation_of_injective P U n _ hinj]
    have hperm : e * Tuple.sort (f ∘ e) = Tuple.sort f := by
      apply Equiv.ext
      intro j
      apply hinj
      exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := f) (σ := e)) j
    have hsort : Tuple.sort (f ∘ e) = e⁻¹ * Tuple.sort f := by
      calc
        Tuple.sort (f ∘ e) = 1 * Tuple.sort (f ∘ e) := by simp
        _ = (e⁻¹ * e) * Tuple.sort (f ∘ e) := by simp
        _ = e⁻¹ * (e * Tuple.sort (f ∘ e)) := by rw [mul_assoc]
        _ = e⁻¹ * Tuple.sort f := by rw [hperm]
    have hsign : (Equiv.Perm.sign (Tuple.sort (f ∘ e)) : ℤ) =
        (Equiv.Perm.sign e : ℤ) * (Equiv.Perm.sign (Tuple.sort f) : ℤ) := by
      rw [hsort, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
      rfl
    have hs : IndexTuple.sortedSimplex (f ∘ e) hinje =
        IndexTuple.sortedSimplex f hinj := by
      ext j
      exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := f) (σ := e)) j
    rw [hsign]
    simp only [Preadditive.zsmul_comp, smul_smul, Category.assoc, ← P.map_comp]
    congr 1
    rw [← π_comp_map_eqToHom P U n hs]
    simp only [Category.assoc, ← P.map_comp]
    congr 1
  · have hinje : ¬ Function.Injective (f ∘ e) := by
      intro h
      apply hinj
      simpa [Function.comp_assoc] using h.comp e.symm.injective
    rw [alternatingEvaluation_of_not_injective P U n _ hinje,
      alternatingEvaluation_of_not_injective P U n _ hinj]
    simp

private theorem alternatingEvaluation_restrict_congr (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) {f g : Fin (n + 1) → ι}
    (hfg : f = g) (W : TopologicalSpace.Opens X)
    (hf : W ≤ IndexTuple.intersection U f) (hg : W ≤ IndexTuple.intersection U g) :
    alternatingEvaluation P U n f ≫ P.map (CategoryTheory.homOfLE hf).op =
      alternatingEvaluation P U n g ≫ P.map (CategoryTheory.homOfLE hg).op := by
  subst g
  rfl

private theorem alternatingEvaluation_face_add_eq_zero_of_eq
    (P : TopCat.Presheaf A X) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (f : Fin (n + 2) → ι) {a b : Fin (n + 2)}
    (hab : f a = f b) (hne : a ≠ b) :
    (-1 : ℤ) ^ (a : ℕ) •
          (alternatingEvaluation P U n (IndexTuple.face f a) ≫
            P.map (IndexTuple.faceHom U f a).op) +
        (-1 : ℤ) ^ (b : ℕ) •
          (alternatingEvaluation P U n (IndexTuple.face f b) ≫
            P.map (IndexTuple.faceHom U f b).op) =
      0 := by
  let p : Equiv.Perm (Fin (n + 2)) := Equiv.swap a b
  let e : Equiv.Perm (Fin (n + 1)) := IndexTuple.deletePerm p a
  have hpa : p a = b := by simp [p]
  have hswap : f ∘ p = f := by
    funext k
    by_cases hka : k = a
    · subst k
      simp [p, hab]
    by_cases hkb : k = b
    · subst k
      simp [p, hab]
    · simp [p, Equiv.swap_apply_of_ne_of_ne hka hkb]
  have hface : IndexTuple.face f b ∘ e = IndexTuple.face f a := by
    funext j
    change f (b.succAbove (e j)) = f (a.succAbove j)
    calc
      f (b.succAbove (e j)) = f (p (a.succAbove j)) := by
        rw [← hpa]
        exact congrArg f (IndexTuple.succAbove_deletePerm p a j)
      _ = f (a.succAbove j) := congrFun hswap (a.succAbove j)
  have hleft : IndexTuple.intersection U f ≤
      IndexTuple.intersection U (IndexTuple.face f b ∘ e) := by
    rw [hface]
    exact IndexTuple.intersection_le_face U f a
  have hequiv := alternatingEvaluation_comp_equiv P U n (IndexTuple.face f b) e
    (IndexTuple.intersection U f) hleft (IndexTuple.intersection_le_face U f b)
  have hmaps :
      alternatingEvaluation P U n (IndexTuple.face f a) ≫
          P.map (IndexTuple.faceHom U f a).op =
        (Equiv.Perm.sign e : ℤ) •
          (alternatingEvaluation P U n (IndexTuple.face f b) ≫
            P.map (IndexTuple.faceHom U f b).op) := by
    calc
      alternatingEvaluation P U n (IndexTuple.face f a) ≫
          P.map (IndexTuple.faceHom U f a).op =
        alternatingEvaluation P U n (IndexTuple.face f b ∘ e) ≫
          P.map (CategoryTheory.homOfLE hleft).op :=
        alternatingEvaluation_restrict_congr P U n hface.symm
          (IndexTuple.intersection U f) _ _
      _ = _ := hequiv
  rw [hmaps, smul_smul, ← add_smul]
  suffices (-1 : ℤ) ^ (a : ℕ) * (Equiv.Perm.sign e : ℤ) +
      (-1 : ℤ) ^ (b : ℕ) = 0 by rw [this, zero_smul]
  rw [IndexTuple.sign_deletePerm p a]
  simp only [hpa]
  have hsignp : (Equiv.Perm.sign p : ℤ) = -1 := by
    simp [p, Equiv.Perm.sign_swap hne]
  rw [hsignp]
  have hsquare : (-1 : ℤ) ^ (a : ℕ) * (-1 : ℤ) ^ (a : ℕ) = 1 := by
    rw [← pow_add]
    have hadd : (a : ℕ) + (a : ℕ) = 2 * (a : ℕ) := by omega
    rw [hadd, pow_mul]
    simp
  calc
    (-1 : ℤ) ^ (a : ℕ) *
          ((-1 : ℤ) ^ (b : ℕ) * -1 * (-1 : ℤ) ^ (a : ℕ)) +
        (-1 : ℤ) ^ (b : ℕ) =
      -((-1 : ℤ) ^ (a : ℕ) * (-1 : ℤ) ^ (a : ℕ)) *
          (-1 : ℤ) ^ (b : ℕ) + (-1 : ℤ) ^ (b : ℕ) := by ring
    _ = 0 := by rw [hsquare]; ring

private theorem differential_comp_alternatingEvaluation_of_not_injective
    (P : TopCat.Presheaf A X) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (f : Fin (n + 2) → ι) (hf : ¬ Function.Injective f) :
    differential P U n ≫ alternatingEvaluation P U (n + 1) f =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (alternatingEvaluation P U n (IndexTuple.face f k) ≫
          P.map (IndexTuple.faceHom U f k).op) := by
  rw [alternatingEvaluation_of_not_injective P U (n + 1) f hf, comp_zero]
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hf
  symm
  calc
    (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (alternatingEvaluation P U n (IndexTuple.face f k) ≫
          P.map (IndexTuple.faceHom U f k).op)) =
      (-1 : ℤ) ^ (a : ℕ) •
          (alternatingEvaluation P U n (IndexTuple.face f a) ≫
            P.map (IndexTuple.faceHom U f a).op) +
        (-1 : ℤ) ^ (b : ℕ) •
          (alternatingEvaluation P U n (IndexTuple.face f b) ≫
            P.map (IndexTuple.faceHom U f b).op) := by
      refine Fintype.sum_eq_add _ _ hne fun k ⟨hka, hkb⟩ ↦ ?_
      have hface : ¬ Function.Injective (IndexTuple.face f k) := by
        rw [Function.not_injective_iff]
        obtain ⟨ia, hia⟩ := Fin.exists_succAbove_eq hka.symm
        obtain ⟨ib, hib⟩ := Fin.exists_succAbove_eq hkb.symm
        refine ⟨ia, ib, ?_, ?_⟩
        · simpa [IndexTuple.face, hia, hib] using hab
        · intro hiab
          apply hne
          rw [← hia, ← hib, hiab]
      rw [alternatingEvaluation_of_not_injective P U n _ hface, zero_comp, smul_zero]
    _ = 0 := alternatingEvaluation_face_add_eq_zero_of_eq P U n f hab hne

/-- The alternating extension of a normalized ordered Čech cochain obeys the usual coboundary
formula on every tuple, including tuples with repeated indices. -/
theorem differential_comp_alternatingEvaluation (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (f : Fin (n + 2) → ι) :
    differential P U n ≫ alternatingEvaluation P U (n + 1) f =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (alternatingEvaluation P U n (IndexTuple.face f k) ≫
          P.map (IndexTuple.faceHom U f k).op) := by
  by_cases hf : Function.Injective f
  · exact differential_comp_alternatingEvaluation_of_injective P U n f hf
  · exact differential_comp_alternatingEvaluation_of_not_injective P U n f hf

section RefinementMap

variable {κ : Type s} [LinearOrder κ] [HasProducts.{s} A]
variable {U : ι → TopologicalSpace.Opens X} {V : κ → TopologicalSpace.Opens X}

/-- The degree-`n` pullback on normalized ordered Čech cochains induced by a chosen refinement.
The coarse tuple selected by the refinement is evaluated alternately, then restricted to the
fine tuple intersection. -/
noncomputable def refinementMapDegree (P : TopCat.Presheaf A X)
    (r : Refinement V U) (n : ℕ) : object P U n ⟶ object P V n :=
  Limits.Pi.lift fun σ ↦
    alternatingEvaluation P U n (r.index ∘ σ) ≫ P.map (r.orderedIntersectionHom σ).op

/-- Component formula for the degreewise refinement pullback. -/
@[reassoc (attr := simp)]
theorem refinementMapDegree_π (P : TopCat.Presheaf A X)
    (r : Refinement V U) (n : ℕ) (σ : OrderedSimplex κ n) :
    refinementMapDegree P r n ≫ π P V n σ =
      alternatingEvaluation P U n (r.index ∘ σ) ≫
        P.map (r.orderedIntersectionHom σ).op :=
  Limits.Pi.lift_π _ _

omit [LinearOrder ι] [Preadditive A] [HasProducts.{v} A] [HasProducts.{s} A] in
private theorem refinement_face_square (P : TopCat.Presheaf A X)
    (r : Refinement V U) (n : ℕ) (σ : OrderedSimplex κ (n + 1))
    (k : Fin (n + 2)) :
    P.map (r.orderedIntersectionHom (σ.face k)).op ≫ P.map (σ.faceHom V k).op =
      P.map (IndexTuple.faceHom U (r.index ∘ σ) k).op ≫
        P.map (r.orderedIntersectionHom σ).op := by
  dsimp only [Refinement.orderedIntersectionHom, OrderedSimplex.faceHom,
    IndexTuple.faceHom, OrderedSimplex.intersection, IndexTuple.intersection,
    OrderedSimplex.face_apply, IndexTuple.face]
  rw [← P.map_comp, ← P.map_comp]
  congr 1

/-- The degreewise refinement pullbacks commute with the normalized ordered Čech
differentials. -/
theorem refinementMapDegree_comp_differential (P : TopCat.Presheaf A X)
    (r : Refinement V U) (n : ℕ) :
    refinementMapDegree P r n ≫ differential P V n =
      differential P U n ≫ refinementMapDegree P r (n + 1) := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [Category.assoc]
  change refinementMapDegree P r n ≫
      (differential P V n ≫ π P V (n + 1) σ) =
    differential P U n ≫
      (refinementMapDegree P r (n + 1) ≫ π P V (n + 1) σ)
  rw [differential_π, refinementMapDegree_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    refinementMapDegree_π_assoc]
  conv_rhs =>
    rw [← Category.assoc, differential_comp_alternatingEvaluation]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [refinement_face_square]
  rfl

/-- The morphism of normalized ordered Čech cochain complexes induced by a chosen refinement. -/
noncomputable def refinementMap (P : TopCat.Presheaf A X) (r : Refinement V U) :
    complex P U ⟶ complex P V :=
  CochainComplex.ofHom (refinementMapDegree (U := U) (V := V) P r) fun n ↦ by
    simpa only [complex_d] using refinementMapDegree_comp_differential P r n

/-- The degree-`n` component of the refinement cochain-complex morphism. -/
@[simp]
theorem refinementMap_f (P : TopCat.Presheaf A X) (r : Refinement V U) (n : ℕ) :
    (refinementMap P r).f n = refinementMapDegree P r n :=
  rfl

/-- Component formula for the refinement cochain-complex morphism. -/
@[reassoc (attr := simp)]
theorem refinementMap_f_π (P : TopCat.Presheaf A X) (r : Refinement V U)
    (n : ℕ) (σ : OrderedSimplex κ n) :
    (refinementMap P r).f n ≫ π P V n σ =
      alternatingEvaluation P U n (r.index ∘ σ) ≫
        P.map (r.orderedIntersectionHom σ).op := by
  simpa only [refinementMap_f] using refinementMapDegree_π P r n σ

end RefinementMap

end OrderedCech

end TopologicalSpace.OpenCover
