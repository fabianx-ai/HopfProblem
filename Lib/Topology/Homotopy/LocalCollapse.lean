/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Patching of local collapses

  Patching of local collapses: collapses performed in overlapping coordinate
  patches glue to a homotopy equivalence of the whole space (Hatcher, Algebraic
  Topology, Proposition 0.17-style glueing).
-/



open Set Function Filter Manifold Topology

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Compact zero sets of continuous functions -/

/-- The zero set is compact inside a compact sublevel. -/
theorem LocalCollapse.zeroSet_isCompact {X : Type*} [TopologicalSpace X] (f : C(X, ℝ))
    {r : ℝ} (hr : 0 < r) (hc : IsCompact {x : X | f x ≤ r}) : IsCompact {x : X | f x = 0} := by
  apply hc.of_isClosed_subset (isClosed_eq f.continuous continuous_const)
  intro x hx
  change f x ≤ r
  rw [show f x = 0 from hx]
  exact hr.le

/-- A small positive sublevel of the zero set fits in a neighborhood. -/
theorem LocalCollapse.exists_positive_sublevel_subset_open {X : Type*}
    [TopologicalSpace X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r}) {U : Set X} (hU : IsOpen U) (hS : {x : X | f x = 0} ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ {x : X | f x ≤ η} ⊆ U := by
  have hK : IsCompact (f '' ({x : X | f x ≤ r} \ U)) := (hc.diff hU).image f.continuous
  have hzero : (0 : ℝ) ∈ (f '' ({x : X | f x ≤ r} \ U))ᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx.2 (hS hfx)
  obtain ⟨a, b, hab, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hK.isClosed.isOpen_compl.mem_nhds hzero)
  refine ⟨Min.min r (b / 2), lt_min hr (half_pos hab.2), min_le_left _ _, ?_⟩
  intro x hx
  change f x ≤ Min.min r (b / 2) at hx
  by_contra hxu
  have hfx : f x < b := (hx.trans (min_le_right r (b / 2))).trans_lt (half_lt_self hab.2)
  apply hsub ⟨hab.1.trans_le (hf x), hfx⟩
  exact ⟨x, ⟨hx.trans (min_le_left r (b / 2)), hxu⟩, rfl⟩

/-! ### Collapses preserving a zero set -/

/-- A homotopy fixing the zero set and nonincreasing in `f`, collapsing a region. -/
structure LocalCollapse.Collapse {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) where
  homotopy : C(unitInterval × X, X)
  map_zero : ∀ x, homotopy (0, x) = x
  fixes_zero : ∀ s x, f x = 0 → homotopy (s, x) = x
  nonincreasing : ∀ s x, f (homotopy (s, x)) ≤ f x
  collapseSet : Set X
  isOpen_collapseSet : IsOpen collapseSet
  map_one_zero : ∀ x ∈ collapseSet, f (homotopy (1, x)) = 0

/-- The trivial collapse. -/
def LocalCollapse.Collapse.identity {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : LocalCollapse.Collapse f
    where
  homotopy := ⟨Prod.snd, continuous_snd⟩
  map_zero _ := rfl
  fixes_zero _ _ _ := rfl
  nonincreasing _ _ := le_rfl
  collapseSet := ∅
  isOpen_collapseSet := isOpen_empty
  map_one_zero _ h := h.elim

/-- The composite of two collapses. -/
def LocalCollapse.Collapse.comp {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
    (A B : LocalCollapse.Collapse f) : LocalCollapse.Collapse f
    where
  homotopy :=
    ⟨fun p => B.homotopy (p.1, A.homotopy p),
      B.homotopy.continuous.comp (continuous_fst.prodMk A.homotopy.continuous)⟩
  map_zero
    x := by
    change B.homotopy (0, A.homotopy (0, x)) = x
    rw [A.map_zero, B.map_zero]
  fixes_zero s x
    hx := by
    change B.homotopy (s, A.homotopy (s, x)) = x
    rw [A.fixes_zero s x hx, B.fixes_zero s x hx]
  nonincreasing s x := (B.nonincreasing s (A.homotopy (s, x))).trans (A.nonincreasing s x)
  collapseSet := A.collapseSet ∪ (fun x => A.homotopy (1, x)) ⁻¹' B.collapseSet
  isOpen_collapseSet :=
    A.isOpen_collapseSet.union
      (B.isOpen_collapseSet.preimage
        (A.homotopy.continuous.comp (continuous_const.prodMk continuous_id)))
  map_one_zero x
    hx := by
    change f (B.homotopy (1, A.homotopy (1, x))) = 0
    rcases hx with hx | hx
    · rw [B.fixes_zero 1 _ (A.map_one_zero x hx)]
      exact A.map_one_zero x hx
    · exact B.map_one_zero (A.homotopy (1, x)) hx

/-- A zero point in either collapse set lies in the composite's. -/
theorem LocalCollapse.Collapse.mem_comp_collapseSet_of_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} (A B : LocalCollapse.Collapse f) {x : X}
    (hx : f x = 0) (h : x ∈ A.collapseSet ∪ B.collapseSet) : x ∈ (A.comp B).collapseSet := by
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    change A.homotopy (1, x) ∈ B.collapseSet
    rwa [A.fixes_zero 1 x hx]

/-- A list of collapses combined by composition. -/
def LocalCollapse.Collapse.combine {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
    {ι : Type*} (A : ι → LocalCollapse.Collapse f) :
    List ι → LocalCollapse.Collapse f
  | [] => identity f
  | i :: l => (A i).comp (combine A l)

/-- A zero point in a member's collapse set lies in the combination's. -/
theorem LocalCollapse.Collapse.mem_combine_collapseSet_of_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} {ι : Type*}
    (A : ι → LocalCollapse.Collapse f) (l : List ι) {x : X} (hx : f x = 0) {i : ι}
    (hi : i ∈ l) (hxi : x ∈ (A i).collapseSet) : x ∈ (combine A l).collapseSet := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inl hxi)
    · exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inr (ih hi))

/-! ### Covering the zero set by a collapse -/

/-- Finitely many collapses covering the compact zero set combine to one. -/
theorem LocalCollapse.exists_localCollapse_covering_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} {ι : Type*} (A : ι → LocalCollapse.Collapse f)
    (hcompact : IsCompact {x : X | f x = 0})
    (hcover : {x : X | f x = 0} ⊆ ⋃ i, (A i).collapseSet) :
    ∃ B : LocalCollapse.Collapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  obtain ⟨s, hs⟩ :=
    hcompact.elim_finite_subcover (fun i => (A i).collapseSet) (fun i => (A i).isOpen_collapseSet)
      hcover
  refine ⟨LocalCollapse.Collapse.combine A s.toList, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact
    LocalCollapse.Collapse.mem_combine_collapseSet_of_zero A s.toList hx
      (by simpa only [Finset.mem_toList] using hi) hxi

/-- Locally covering collapses combine to a global collapse of the zero set. -/
theorem LocalCollapse.exists_localCollapse_covering_zero_of_local {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} (hcompact : IsCompact {x : X | f x = 0})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse.Collapse f, x ∈ A.collapseSet) :
    ∃ B : LocalCollapse.Collapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  choose A hA using fun x : { x : X // f x = 0 } => hlocal x x.2
  apply exists_localCollapse_covering_zero A hcompact
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hA ⟨x, hx⟩⟩

/-- A small sublevel admits a collapse covering it. -/
theorem LocalCollapse.exists_small_sublevel_localCollapse {X : Type*}
    [TopologicalSpace X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse.Collapse f, x ∈ A.collapseSet) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ ∃ A : LocalCollapse.Collapse f, {x : X | f x ≤ η} ⊆ A.collapseSet := by
  obtain ⟨A, hA⟩ := exists_localCollapse_covering_zero_of_local (zeroSet_isCompact f hr hc) hlocal
  obtain ⟨η, hη, hηr, hηA⟩ :=
    exists_positive_sublevel_subset_open f hf hr hc A.isOpen_collapseSet hA
  exact ⟨η, hη, hηr, A, hηA⟩
