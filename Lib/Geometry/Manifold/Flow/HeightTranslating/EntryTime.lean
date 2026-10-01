/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Entry times of a flow into a closed set

For a flow `F : Flow ℝ X` on a topological space and a set `A`, the *entry time* of a point `x` is
`entryTime F A x = sInf {t | 0 ≤ t ∧ F t x ∈ A}`. If `A` is closed, forward invariant
(`F t x ∈ A` for `x ∈ A`, `0 ≤ t`) and strictly absorbing (`F t x ∈ interior A` for `x ∈ A`,
`0 < t`), the entry time is continuous on every set of points that reach `A`, and flowing each
point for its entry time retracts such a set onto `A`. This is the argument of Milnor,
*Morse Theory*, Theorem 3.1 (the sublevel `M^a` is a deformation retract of `M^b` when
`f⁻¹[a, b]` has no critical point), stated for an arbitrary flow.

## Main definitions and results

* `FlowConstruction.forwardInvariant_of_local`, `FlowConstruction.interior_entry_of_local` :
  forward invariance and strict absorption follow from their short-time versions.
* `FlowConstruction.entryTime` : the entry time, with `entryTime_le_iff` (for `0 ≤ t`,
  `entryTime F A x ≤ t ↔ F t x ∈ A`) and `continuousOn_entryTime`.
* `FlowConstruction.entryRetraction`, `FlowConstruction.entryDeformation`,
  `FlowConstruction.entryHomotopyEquiv` : the retraction `B → A`, the homotopy from the identity
  of `B` to it relative to `A`, and the resulting homotopy equivalence `A ≃ₕ B`.
* `FlowConstruction.entryTime_flow_of_le`, `FlowConstruction.entryTime_eq_add_of_flow_pos` :
  the entry time along an orbit.
* `FlowConstruction.frontier_sublevel_eq_of_strict_flow` : if `f` is nonincreasing along the
  flow and strictly decreases off the level `b`, then `frontier {x | f x ≤ b} = {x | f x = b}`.

## References

* [John Milnor, *Morse Theory*][milnor63], §3, Theorem 3.1

## Tags

flow, entry time, hitting time, deformation retract
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-! ### Forward invariance and entry -/

/-- A closed set `A` such that every `x ∈ A` satisfies `F t x ∈ A` for all `t` in some `[0, ε]`,
`ε > 0`, is forward invariant: `F t x ∈ A` for all `x ∈ A` and `0 ≤ t`. -/
theorem FlowConstruction.forwardInvariant_of_local {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Icc 0 ε, F t x ∈ A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A := by
  intro x hx T hT
  let S : Set ℝ := {t | F t x ∈ A}
  have hS : IsClosed S := hA.preimage (F.continuous continuous_id continuous_const)
  have hzero : (0 : ℝ) ∈ S := by simpa only [S, Set.mem_ofPred_eq, F.map_zero_apply] using hx
  apply (hS.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hzero hT
  intro s hs
  obtain ⟨ε, hε, hstay⟩ := hlocal (F s x) hs.1
  let δ := Min.min ε (T - s) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hs.2.2))
  have hδε : δ ≤ ε :=
    (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans (min_le_left _ _)
  have hδT : δ ≤ T - s :=
    (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans (min_le_right _ _)
  refine ⟨s + δ, ?_, by linarith, by linarith⟩
  change F (s + δ) x ∈ A
  rw [add_comm s δ, F.map_add]
  exact hstay δ ⟨hδ.le, hδε⟩

/-- If `A` is forward invariant under the flow `F`, then so is `interior A`: for `x ∈ interior A`
and `0 ≤ t`, `F t x ∈ interior A`. -/
theorem FlowConstruction.forwardInvariant_interior {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A) {x : X}
    (hx : x ∈ interior A) {t : ℝ} (ht : 0 ≤ t) : F t x ∈ interior A := by
  apply mem_interior.mpr
  refine ⟨F t '' interior A, ?_, (F.toHomeomorph t).isOpenMap _ isOpen_interior, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hforward y (interior_subset hy) t ht
  · exact ⟨x, hx, rfl⟩

/-- If `A` is forward invariant and every `x ∈ A` satisfies `F t x ∈ interior A` for all `t` in some
`(0, ε]`, `ε > 0`, then `F t x ∈ interior A` for all `x ∈ A` and `0 < t`. -/
theorem FlowConstruction.interior_entry_of_local {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioc 0 ε, F t x ∈ interior A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A := by
  intro x hx t ht
  obtain ⟨ε, hε, hentry⟩ := hlocal x hx
  let δ := Min.min ε t / 2
  have hδ : 0 < δ := half_pos (lt_min hε ht)
  have hδε : δ ≤ ε := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_left _ _)
  have hδt : δ ≤ t := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_right _ _)
  have hi := forwardInvariant_interior F hforward (hentry δ ⟨hδ, hδε⟩) (sub_nonneg.mpr hδt)
  rw [← F.map_add, sub_add_cancel] at hi
  exact hi

/-! ### The entry time -/

/-- The entry time of `x` into `A` under the flow `F`: the infimum of the times `t ≥ 0` with
`F t x ∈ A` (it is `sInf ∅ = 0` if the forward orbit of `x` does not meet `A`). -/
def FlowConstruction.entryTime {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (A : Set X)
    (x : X) : ℝ :=
  InfSet.sInf {t : ℝ | 0 ≤ t ∧ F t x ∈ A}

/-- If the forward orbit of `x` meets `A`, then `0 ≤ entryTime F A x`. -/
theorem FlowConstruction.entryTime_nonneg {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : 0 ≤ entryTime F A x :=
  le_csInf hx (fun _ ht => ht.1)

/-- If `0 ≤ t` and `F t x ∈ A`, then `entryTime F A x ≤ t`. -/
theorem FlowConstruction.entryTime_le_of_mem {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} {t : ℝ} (ht : 0 ≤ t) (hx : F t x ∈ A) : entryTime F A x ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, hx⟩

/-- If `A` is closed and the forward orbit of `x` meets `A`, then `F (entryTime F A x) x ∈ A`. -/
theorem FlowConstruction.flow_entryTime_mem {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} (hA : IsClosed A) {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) :
    F (entryTime F A x) x ∈ A := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ F t x ∈ A} :=
    isClosed_Ici.inter (hA.preimage (F.continuous continuous_id continuous_const))
  exact (hclosed.csInf_mem hx ⟨0, fun _ hs => hs.1⟩).2

/-- A point of `A` has entry time `0` into `A`. -/
theorem FlowConstruction.entryTime_eq_zero {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} (hx : x ∈ A) : entryTime F A x = 0 := by
  have hhit : F 0 x ∈ A := by simpa only [F.map_zero_apply] using hx
  exact le_antisymm (entryTime_le_of_mem F le_rfl hhit) (entryTime_nonneg F ⟨0, le_rfl, hhit⟩)

/-- Let `A` be closed and forward invariant and let the forward orbit of `x` meet `A`. Then for
`0 ≤ t`, `entryTime F A x ≤ t ↔ F t x ∈ A`. -/
theorem FlowConstruction.entryTime_le_iff {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t) : entryTime F A x ≤ t ↔ F t x ∈ A := by
  constructor
  · intro h
    have hh := hforward _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_nonneg.mpr h)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  · exact entryTime_le_of_mem F ht

/-- Let `A` be closed and strictly absorbing (`F t x ∈ interior A` for `x ∈ A`, `0 < t`) and let the
forward orbit of `x` meet `A`. Then `F t x ∈ interior A` for every `t > entryTime F A x`. -/
theorem FlowConstruction.flow_mem_interior_of_entryTime_lt {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : entryTime F A x < t) : F t x ∈ interior A := by
  have hh := hentry _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_pos.mpr ht)
  rw [← F.map_add, sub_add_cancel] at hh
  exact hh

/-- Let `A` be closed and strictly absorbing. If `0 ≤ t` and `F t x ∈ frontier A`, then
`entryTime F A x = t`. -/
theorem FlowConstruction.entryTime_eq_of_flow_mem_frontier {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {x : X} {t : ℝ} (ht : 0 ≤ t)
    (hfront : F t x ∈ frontier A) : entryTime F A x = t := by
  have hmem : F t x ∈ A := by simpa only [hA.closure_eq] using frontier_subset_closure hfront
  apply le_antisymm (entryTime_le_of_mem F ht hmem)
  apply le_of_not_gt
  intro hlt
  exact hfront.2 (flow_mem_interior_of_entryTime_lt F hA hentry ⟨t, ht, hmem⟩ hlt)

/-- Let `A` be closed, forward invariant and strictly absorbing. Then `entryTime F A` is continuous
on any set `B` each of whose points has a forward orbit meeting `A`. -/
theorem FlowConstruction.continuousOn_entryTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {B : Set X}
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : ContinuousOn (entryTime F A) B := by
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hneg : a < 0
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hneg.trans_le (entryTime_nonneg F (hhit y hy))
    · have ha₀ : 0 ≤ a := le_of_not_gt hneg
      have hnot : F a x ∉ A := fun h => not_le_of_gt ha (entryTime_le_of_mem F ha₀ h)
      have hevent : ∀ᶠ y in 𝓝 x, F a y ∉ A :=
        (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
          (hA.isOpen_compl.mem_nhds hnot)
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hevent] with y
        hy hya
      apply lt_of_not_ge
      intro hle
      exact hya ((entryTime_le_iff F hA hforward (hhit y hy) ha₀).mp hle)
  · intro b hb
    obtain ⟨t, hxt, htb⟩ := exists_between hb
    have ht₀ : 0 ≤ t := (entryTime_nonneg F (hhit x hx)).trans hxt.le
    have hi := flow_mem_interior_of_entryTime_lt F hA hentry (hhit x hx) hxt
    have hevent : ∀ᶠ y in 𝓝 x, F t y ∈ interior A :=
      (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hi)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hevent] with y hy
    exact (entryTime_le_of_mem F ht₀ (interior_subset hy)).trans_lt htb

/-! ### The entry retraction -/

/-- The entry map `B → A`, `x ↦ F (entryTime F A x) x`, for `A` closed, forward invariant and
strictly absorbing and `B` a set each of whose points has a forward orbit meeting `A`. -/
def FlowConstruction.entryRetraction {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : C(B, A)
    where
  toFun x := ⟨F (entryTime F A x.1) x.1, flow_entryTime_mem F hA (hhit x.1 x.2)⟩
  continuous_toFun :=
    (F.continuous
          (continuousOn_iff_continuous_domRestrict.mp
            (continuousOn_entryTime F hA hforward hentry hhit))
          continuous_subtype_val).subtype_mk
      _

/-- For `A ⊆ B`, the entry map `B → A` restricts to the identity on `A`. -/
theorem FlowConstruction.entryRetraction_inclusion {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A B : Set X} (hA : IsClosed A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B) (x : A) :
    entryRetraction F hA hforward hentry hhit (ContinuousMap.inclusion hsub x) = x := by
  apply Subtype.ext
  change F (entryTime F A x.1) x.1 = x.1
  rw [entryTime_eq_zero F x.2, F.map_zero_apply]

/-- For `A ⊆ B` with `B` forward invariant, the homotopy `(s, x) ↦ F (s * entryTime F A x) x` of
`B`, from the identity to the entry map followed by the inclusion `A → B`, stationary on `A`. -/
def FlowConstruction.entryDeformation {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B)
    (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B) :
    (ContinuousMap.id B).HomotopyRel
      ((ContinuousMap.inclusion hsub).comp (entryRetraction F hA hforward hentry hhit))
      {x : B | x.1 ∈ A}
    where
  toFun
    q :=
    ⟨F (q.1.1 * entryTime F A q.2.1) q.2.1,
      hregion q.2.1 q.2.2 _ (mul_nonneg q.1.2.1 (entryTime_nonneg F (hhit q.2.1 q.2.2)))⟩
  continuous_toFun :=
    (F.continuous
          ((continuous_subtype_val.comp continuous_fst).mul
            ((continuousOn_iff_continuous_domRestrict.mp
                  (continuousOn_entryTime F hA hforward hentry hhit)).comp
              continuous_snd))
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change F ((0 : ℝ) * entryTime F A x.1) x.1 = x.1
    rw [MulZeroClass.zero_mul, F.map_zero_apply]
  map_one_left
    x := by
    apply Subtype.ext
    change F ((1 : ℝ) * entryTime F A x.1) x.1 = F (entryTime F A x.1) x.1
    rw [one_mul]
  prop' u x
    hx := by
    apply Subtype.ext
    change F (u.1 * entryTime F A x.1) x.1 = x.1
    rw [entryTime_eq_zero F (A := A) (show x.1 ∈ A from hx), MulZeroClass.mul_zero,
      F.map_zero_apply]

/-- Let `A ⊆ B` with `A` closed, forward invariant and strictly absorbing, `B` forward invariant,
and every forward orbit from `B` meeting `A`. Then the inclusion `A → B` is a homotopy equivalence,
with homotopy inverse the entry map `entryRetraction`. -/
def FlowConstruction.entryHomotopyEquiv {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B)
    (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B) : A ≃ₕ B
    where
  toFun := ContinuousMap.inclusion hsub
  invFun := entryRetraction F hA hforward hentry hhit
  left_inv := by
    have heq :
      (entryRetraction F hA hforward hentry hhit).comp (ContinuousMap.inclusion hsub) =
        ContinuousMap.id A := by
      apply ContinuousMap.ext
      intro x
      exact entryRetraction_inclusion F hA hforward hentry hhit hsub x
    rw [heq]
  right_inv := ⟨(entryDeformation F hA hforward hentry hhit hsub hregion).toHomotopy.symm⟩

/-! ### Entry times along an orbit -/

/-- Let `A` be closed and let the forward orbit of `x` meet `A`. For `0 ≤ t ≤ entryTime F A x`,
`entryTime F A (F t x) = entryTime F A x - t`. -/
theorem FlowConstruction.entryTime_flow_of_le {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ}
    (ht : 0 ≤ t) (hle : t ≤ entryTime F A x) : entryTime F A (F t x) = entryTime F A x - t := by
  have hhit : F (entryTime F A x - t) (F t x) ∈ A := by
    rw [← F.map_add, sub_add_cancel]
    exact flow_entryTime_mem F hA hx
  have hy : ∃ u : ℝ, 0 ≤ u ∧ F u (F t x) ∈ A := ⟨_, sub_nonneg.mpr hle, hhit⟩
  apply le_antisymm (entryTime_le_of_mem F (sub_nonneg.mpr hle) hhit)
  have hh := flow_entryTime_mem F hA hy
  rw [← F.map_add] at hh
  have hb := entryTime_le_of_mem F (add_nonneg (entryTime_nonneg F hy) ht) hh
  linarith

/-- If `0 < t` and `F t x ∈ interior A`, then `entryTime F A x < t`. -/
theorem FlowConstruction.entryTime_lt_of_flow_mem_interior {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} {x : X} {t : ℝ} (ht : 0 < t) (hx : F t x ∈ interior A) :
    entryTime F A x < t := by
  have he : ∀ᶠ s in 𝓝 t, 0 < s ∧ F s x ∈ interior A :=
    (eventually_gt_nhds ht).and
      ((F.continuous continuous_id continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hx))
  obtain ⟨s, hst, hs⟩ := he.exists_lt
  exact (entryTime_le_of_mem F hs.1.le (interior_subset hs.2)).trans_lt hst

/-- Let `A` be closed and forward invariant and let the forward orbit of `x` meet `A`. If `0 ≤ t`
and `F t x` has positive entry time, then `entryTime F A x = t + entryTime F A (F t x)`. -/
theorem FlowConstruction.entryTime_eq_add_of_flow_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t)
    (hpos : 0 < entryTime F A (F t x)) : entryTime F A x = t + entryTime F A (F t x) := by
  have hle : t ≤ entryTime F A x := by
    by_contra h
    have hh := (entryTime_le_iff F hA hforward hx ht).mp (le_of_not_ge h)
    rw [entryTime_eq_zero F hh] at hpos
    exact lt_irrefl _ hpos
  rw [entryTime_flow_of_le F hA hx ht hle]
  ring

/-! ### The frontier of a sublevel -/

/-- Let `f` be continuous and antitone along every orbit of the flow `F`, and suppose
`f (F t x) < b` whenever `f x = b` and `0 < t`. Then `frontier {x | f x ≤ b} = {x | f x = b}`. -/
theorem FlowConstruction.frontier_sublevel_eq_of_strict_flow {X : Type*}
    [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) (F : Flow ℝ X)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {b : ℝ}
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    frontier {x | f x ≤ b} = {x | f x = b} := by
  have hclosed : IsClosed {x | f x ≤ b} := isClosed_le hf continuous_const
  ext x
  rw [frontier, hclosed.closure_eq]
  constructor
  · rintro ⟨hx, hnot⟩
    apply le_antisymm hx
    by_contra hn
    have hlt : f x < b := lt_of_not_ge hn
    exact
      hnot (interior_maximal (fun y (hy : f y < b) => hy.le) (isOpen_lt hf continuous_const) hlt)
  · intro hx
    refine ⟨(show f x ≤ b from hx.le), ?_⟩
    intro hi
    have he : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ b} := by
      have hcont : ContinuousAt (fun t : ℝ => F t x) 0 :=
        (F.continuous continuous_id continuous_const).continuousAt
      apply hcont.preimage_mem_nhds
      simpa only [F.map_zero_apply] using isOpen_interior.mem_nhds hi
    obtain ⟨s, hs, hsB⟩ := he.exists_lt
    have hy : F s x ∈ {y | f y ≤ b} := interior_subset hsB
    have hxy : f x ≤ f (F s x) := by
      have hh := hmono (F s x) (show (0 : ℝ) ≤ -s by linarith)
      simpa only [F.map_zero_apply, ← F.map_add, neg_add_cancel] using hh
    have hyeq : f (F s x) = b := le_antisymm hy (hx ▸ hxy)
    have hstrict := htop (F s x) hyeq (-s) (by linarith)
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hx] at hstrict
    exact lt_irrefl b hstrict
