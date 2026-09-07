/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Sets.OpenCover

/-!
# Lebesgue covering dimension: open-cover vocabulary

This file records the elementary open-cover notions used in the definition of Lebesgue covering
dimension. A refinement includes a chosen function from the finer indices to the coarser indices.
The multiplicity bound says that no point lies in more than the prescribed number of cover
members; equivalently, every intersection of too many distinct members is empty.

The vocabulary, its elementary finite-intersection reformulations, and transport of dimension
bounds along homeomorphisms are developed here. Transport uses a common arbitrary universe for
the two spaces and their cover indices. No separation axiom, compactness assumption, or sheaf
theory is involved.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open Set

universe u v w t z

namespace TopologicalSpace

namespace OpenCover

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} {κ : Type w} {μ : Type t}

/-- A chosen refinement of `U` by `V`: every member of `V` is assigned a containing member of
`U`. The families need not cover the space for this elementary notion. -/
@[ext]
structure Refinement (V : κ → Opens X) (U : ι → Opens X) where
  /-- The member of the coarser family assigned to each member of the finer family. -/
  index : κ → ι
  /-- Every finer member is contained in its assigned coarser member. -/
  le : ∀ j, V j ≤ U (index j)

namespace Refinement

variable {U : ι → Opens X} {V : κ → Opens X} {W : μ → Opens X}

/-- Every family is a chosen refinement of itself. -/
@[refl]
def refl (U : ι → Opens X) : Refinement U U where
  index := id
  le _ := le_rfl

/-- Chosen refinements compose by composing their index functions. -/
def comp (r : Refinement V U) (s : Refinement W V) : Refinement W U where
  index j := r.index (s.index j)
  le j := (s.le j).trans (r.le (s.index j))

@[simp]
theorem refl_index (U : ι → Opens X) (i : ι) : (refl U).index i = i :=
  rfl

@[simp]
theorem comp_index (r : Refinement V U) (s : Refinement W V) (k : μ) :
    (r.comp s).index k = r.index (s.index k) :=
  rfl

@[simp]
theorem refl_comp (r : Refinement V U) : (refl U).comp r = r := by
  ext
  rfl

@[simp]
theorem comp_refl (r : Refinement V U) : r.comp (refl V) = r := by
  ext
  rfl

@[simp]
theorem comp_assoc {Z : Type z} {T : Z → Opens X}
    (r : Refinement V U) (s : Refinement W V) (t : Refinement T W) :
    (r.comp s).comp t = r.comp (s.comp t) := by
  ext
  rfl

end Refinement

/-- The family `U` has multiplicity at most `m` if every finite collection of distinct members
which contains one point has at most `m` members. This formulation also rules out a point lying in
infinitely many members. -/
def MultiplicityLE (U : ι → Opens X) (m : ℕ) : Prop :=
  ∀ (x : X) (s : Finset ι), (∀ i : s, x ∈ U i) → s.card ≤ m

namespace MultiplicityLE

variable {U : ι → Opens X} {m n : ℕ}

/-- A multiplicity bound remains true after increasing the bound. -/
theorem mono (h : MultiplicityLE U m) (hmn : m ≤ n) : MultiplicityLE U n :=
  fun x s hs ↦ (h x s hs).trans hmn

/-- The point-membership definition of multiplicity is equivalent to saying that every finite
intersection with more than `m` distinct members is empty. -/
theorem iff_iInter_eq_empty :
    MultiplicityLE U m ↔
      ∀ (s : Finset ι), m < s.card → ⋂ i : s, (U i : Set X) = ∅ := by
  constructor
  · intro h s hcard
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Nat.not_lt_of_ge (h x s (Set.mem_iInter.mp hx))) hcard
  · intro h x s hx
    apply Nat.le_of_not_gt
    intro hcard
    have hmem : x ∈ ⋂ i : s, (U i : Set X) := Set.mem_iInter.mpr hx
    rw [h s hcard] at hmem
    exact hmem

/-- Equivalently, it suffices to test intersections of exactly `m + 1` distinct members. A
`Finset` already records distinctness of its members. -/
theorem iff_iInter_eq_empty_of_card_eq_succ :
    MultiplicityLE U m ↔
      ∀ (s : Finset ι), s.card = m + 1 → ⋂ i : s, (U i : Set X) = ∅ := by
  constructor
  · intro h s hs
    apply iff_iInter_eq_empty.mp h s
    rw [hs]
    exact Nat.lt_succ_self m
  · intro h x s hx
    apply Nat.le_of_not_gt
    intro hcard
    obtain ⟨t, hts, htcard⟩ :=
      s.exists_subset_card_eq (Nat.succ_le_iff.mpr hcard)
    have hmem : x ∈ ⋂ i : t, (U i : Set X) := by
      apply Set.mem_iInter.mpr
      intro i
      exact hx ⟨i, hts i.property⟩
    rw [Nat.succ_eq_add_one] at htcard
    rw [h t htcard] at hmem
    exact hmem

end MultiplicityLE

end OpenCover

end TopologicalSpace

variable (X : Type u) [TopologicalSpace X]

/-- A space has Lebesgue covering dimension at most `n` if every open cover admits an open
refinement of multiplicity at most `n + 1`. The refinement carries the chosen index function used
to compare the finer cover with the original one.

As in Mathlib's definition of `ParacompactSpace`, cover indices live in the same universe as the
space. -/
def HasCoveringDimensionLE (n : ℕ) : Prop :=
  ∀ {ι : Type u} (U : ι → TopologicalSpace.Opens X), TopologicalSpace.IsOpenCover U →
    ∃ (κ : Type u) (V : κ → TopologicalSpace.Opens X)
      (_ : TopologicalSpace.OpenCover.Refinement V U),
      TopologicalSpace.IsOpenCover V ∧ TopologicalSpace.OpenCover.MultiplicityLE V (n + 1)

namespace HasCoveringDimensionLE

variable {X : Type u} [TopologicalSpace X] {m n : ℕ}

/-- A covering-dimension bound remains true after increasing the dimension. -/
theorem mono (hmn : m ≤ n) (h : HasCoveringDimensionLE X m) :
    HasCoveringDimensionLE X n := by
  intro ι U hU
  obtain ⟨κ, V, r, hV, hmult⟩ := h U hU
  exact ⟨κ, V, r, hV, hmult.mono (Nat.add_le_add_right hmn 1)⟩

open TopologicalSpace in
/-- Transport a covering-dimension bound along a homeomorphism between spaces in a common
arbitrary universe, using the existing convention that cover indices share the space universe.

Textbook Lemma 6.1 (CD12C-T): push an arbitrary indexed open cover forward, choose a refinement
on the target, and pull that refinement back. The original and refinement index types and the
chosen assignment are unchanged. Membership of a point in a finite family pulls back to
membership of its image in the same finite family, preserving the index-counting multiplicity.
No separation, compactness, metric, nonemptiness, or finite-cover hypothesis is required. -/
theorem of_homeomorph {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (g : X ≃ₜ Y) {n : ℕ} (hY : HasCoveringDimensionLE Y n) :
    HasCoveringDimensionLE X n := by
  intro ι U hU
  -- T01: image openness and surjectivity give a cover on the same original indices.
  let U' : ι → Opens Y :=
    fun i => ⟨g '' (U i : Set X), g.isOpenMap _ (U i).isOpen⟩
  have hImageUnion : (⋃ i, g '' (U i : Set X)) = Set.univ := by
    rw [← Set.image_iUnion, hU.iSup_set_eq_univ]
    exact Set.image_univ_of_surjective g.surjective
  have hImage : IsOpenCover U' :=
    IsOpenCover.of_sets (fun i => g.isOpenMap _ (U i).isOpen) hImageUnion
  -- T02: choose the target refinement once, with its actual assignment.
  obtain ⟨κ, V', r, hV', hM'⟩ := hY U' hImage
  -- T03: continuous preimages form a cover on those same refinement indices.
  let f : C(X, Y) := ⟨g, g.continuous⟩
  let V : κ → Opens X := fun j => (V' j).comap f
  have hV : IsOpenCover V := hV'.comap f
  -- T04: preimage monotonicity and injective cancellation retain the assignment.
  have hContain : ∀ j, V j ≤ U (r.index j) := by
    intro j
    change g ⁻¹' (V' j : Set Y) ⊆ (U (r.index j) : Set X)
    have hpre : g ⁻¹' (V' j : Set Y) ⊆ g ⁻¹' (g '' (U (r.index j) : Set X)) :=
      Set.preimage_mono (r.le j)
    simpa only [g.preimage_image] using hpre
  let rX : OpenCover.Refinement V U := ⟨r.index, hContain⟩
  -- T05: the same finite index family at x meets the target cover at g x.
  have hM : OpenCover.MultiplicityLE V (n + 1) := by
    intro x s hs
    exact hM' (g x) s hs
  -- T06: these witnesses satisfy the original arbitrary-cover criterion.
  exact ⟨κ, V, rX, hV, hM⟩

end HasCoveringDimensionLE
