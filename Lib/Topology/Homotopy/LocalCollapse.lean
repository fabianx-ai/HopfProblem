/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

theorem CuspRetraction.Patching.zeroSet_isCompact {X : Type*} [TopologicalSpace X] (f : C(X, ℝ))
    {r : ℝ} (hr : 0 < r) (hc : IsCompact {x : X | f x ≤ r}) : IsCompact {x : X | f x = 0} := by
  apply hc.of_isClosed_subset (isClosed_eq f.continuous continuous_const)
  intro x hx
  change f x ≤ r
  rw [show f x = 0 from hx]
  exact hr.le

theorem CuspRetraction.Patching.exists_positive_sublevel_subset_open {X : Type*}
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

structure CuspRetraction.Patching.LocalCollapse {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) where
  homotopy : C(unitInterval × X, X)
  map_zero : ∀ x, homotopy (0, x) = x
  fixes_zero : ∀ s x, f x = 0 → homotopy (s, x) = x
  nonincreasing : ∀ s x, f (homotopy (s, x)) ≤ f x
  collapseSet : Set X
  isOpen_collapseSet : IsOpen collapseSet
  map_one_zero : ∀ x ∈ collapseSet, f (homotopy (1, x)) = 0

def CuspRetraction.Patching.LocalCollapse.identity {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : CuspRetraction.Patching.LocalCollapse f
    where
  homotopy := ⟨Prod.snd, continuous_snd⟩
  map_zero _ := rfl
  fixes_zero _ _ _ := rfl
  nonincreasing _ _ := le_rfl
  collapseSet := ∅
  isOpen_collapseSet := isOpen_empty
  map_one_zero _ h := h.elim

def CuspRetraction.Patching.LocalCollapse.comp {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
    (A B : CuspRetraction.Patching.LocalCollapse f) : CuspRetraction.Patching.LocalCollapse f
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

theorem CuspRetraction.Patching.LocalCollapse.mem_comp_collapseSet_of_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} (A B : CuspRetraction.Patching.LocalCollapse f) {x : X}
    (hx : f x = 0) (h : x ∈ A.collapseSet ∪ B.collapseSet) : x ∈ (A.comp B).collapseSet := by
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    change A.homotopy (1, x) ∈ B.collapseSet
    rwa [A.fixes_zero 1 x hx]

def CuspRetraction.Patching.LocalCollapse.combine {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
    {ι : Type*} (A : ι → CuspRetraction.Patching.LocalCollapse f) :
    List ι → CuspRetraction.Patching.LocalCollapse f
  | [] => identity f
  | i :: l => (A i).comp (combine A l)

theorem CuspRetraction.Patching.LocalCollapse.mem_combine_collapseSet_of_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} {ι : Type*}
    (A : ι → CuspRetraction.Patching.LocalCollapse f) (l : List ι) {x : X} (hx : f x = 0) {i : ι}
    (hi : i ∈ l) (hxi : x ∈ (A i).collapseSet) : x ∈ (combine A l).collapseSet := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inl hxi)
    · exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inr (ih hi))

theorem CuspRetraction.Patching.exists_localCollapse_covering_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} {ι : Type*} (A : ι → LocalCollapse f)
    (hcompact : IsCompact {x : X | f x = 0})
    (hcover : {x : X | f x = 0} ⊆ ⋃ i, (A i).collapseSet) :
    ∃ B : LocalCollapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  obtain ⟨s, hs⟩ :=
    hcompact.elim_finite_subcover (fun i => (A i).collapseSet) (fun i => (A i).isOpen_collapseSet)
      hcover
  refine ⟨LocalCollapse.combine A s.toList, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact
    LocalCollapse.mem_combine_collapseSet_of_zero A s.toList hx
      (by simpa only [Finset.mem_toList] using hi) hxi

theorem CuspRetraction.Patching.exists_localCollapse_covering_zero_of_local {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} (hcompact : IsCompact {x : X | f x = 0})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ B : LocalCollapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  choose A hA using fun x : { x : X // f x = 0 } => hlocal x x.2
  apply exists_localCollapse_covering_zero A hcompact
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hA ⟨x, hx⟩⟩

theorem CuspRetraction.Patching.exists_small_sublevel_localCollapse {X : Type*}
    [TopologicalSpace X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ ∃ A : LocalCollapse f, {x : X | f x ≤ η} ⊆ A.collapseSet := by
  obtain ⟨A, hA⟩ := exists_localCollapse_covering_zero_of_local (zeroSet_isCompact f hr hc) hlocal
  obtain ⟨η, hη, hηr, hηA⟩ :=
    exists_positive_sublevel_subset_open f hf hr hc A.isOpen_collapseSet hA
  exact ⟨η, hη, hηr, A, hηA⟩
end Mathoverflow1973
