/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Flow.HeightTranslating

/-!
# Flows that cross a level set strictly downwards

Let `F : Flow ℝ X` be a flow on a topological space and `f : X → ℝ` a continuous function whose
derivative along the flow is a continuous function `D`, i.e. `d/ds f (F s x) = D (F t x)` at
`s = t`.  If `D < 0` on the level set `f = c`, then

* `f` is strictly decreasing along the orbit of a point where `D < 0`, for small times
  (`FlowCancellation.exists_local_strict_flow_descent`);
* the sublevel set `{f ≤ c}` is forward invariant and is mapped into `{f < c}` by every positive
  time (`forwardInvariant_sublevel_of_boundary`, `strict_sublevel_entry_of_boundary`);
* the interior of `{f ≤ c}` is `{f < c}` (`interior_sublevel_eq_of_boundary`);
* every orbit meets the level `f = c` at most once (`flow_level_time_unique`).

This is the elementary transversality of a flow to a regular level, cf. Milnor, *Morse Theory*, §3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- A locally strict descent flow exists. -/
theorem FlowCancellation.exists_local_strict_flow_descent {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {x : X} (hx : D x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ StrictAntiOn (fun t : ℝ => f (F t x)) (Set.Icc (-ε) ε) := by
  have hcont : Continuous (fun t : ℝ => D (F t x)) :=
    hD.comp (F.continuous continuous_id continuous_const)
  have he : ∀ᶠ t : ℝ in 𝓝 0, D (F t x) < 0 := by
    have hx0 : D (F 0 x) < 0 := by simpa only [F.map_zero_apply] using hx
    exact hcont.continuousAt (eventually_lt_nhds hx0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hfc : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hfc.continuousOn
  intro t ht
  rw [(hder x t).deriv]
  apply hball
  rw [Real.dist_eq, sub_zero, abs_lt]
  have ht' := interior_subset ht
  constructor <;> linarith [ht'.1, ht'.2]

/-- The flow strictly enters a sublevel locally. -/
theorem FlowCancellation.exists_local_strict_sublevel_entry {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x ≤ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioc (0 : ℝ) ε, f (F t x) < c := by
  rcases hx.lt_or_eq with hx | hx
  · have he : ∀ᶠ t : ℝ in 𝓝 0, f (F t x) < c := by
      have hfc : Continuous (fun t : ℝ => f (F t x)) :=
        hf.comp (F.continuous continuous_id continuous_const)
      have hx0 : f (F 0 x) < c := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (eventually_lt_nhds hx0)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro t ht
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  · obtain ⟨ε, hε, hanti⟩ := exists_local_strict_flow_descent F hf hD hder (hboundary x hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    have hh :=
      hanti (show (0 : ℝ) ∈ Set.Icc (-ε) ε from ⟨by linarith, hε.le⟩)
        (show t ∈ Set.Icc (-ε) ε from ⟨by linarith [ht.1], ht.2⟩) ht.1
    simpa only [F.map_zero_apply, hx] using hh

/-- A sublevel with forward-invariant boundary is forward invariant. -/
theorem FlowCancellation.forwardInvariant_sublevel_of_boundary {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ c := by
  apply FlowConstruction.forwardInvariant_of_local F (isClosed_le hf continuous_const)
  intro x hx
  obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
  refine ⟨ε, hε, ?_⟩
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | htpos
  · simpa only [← ht0, F.map_zero_apply] using hx
  · exact (hentry t ⟨htpos, ht.2⟩).le

/-- The sublevel interior is determined by the boundary. -/
theorem FlowCancellation.interior_sublevel_eq_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : interior {x | f x ≤ c} = {x | f x < c} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hle : f x ≤ c := (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) hx
    apply lt_of_le_of_ne hle
    intro heq
    have hnhds : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ c} := by
      have hfc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
      have hx0 : F 0 x ∈ interior {y | f y ≤ c} := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (isOpen_interior.mem_nhds hx0)
    have hmax : IsLocalMax (fun t : ℝ => f (F t x)) 0 := by
      filter_upwards [hnhds] with t ht
      change f (F t x) ≤ f (F 0 x)
      rw [F.map_zero_apply, heq]
      exact (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) ht
    have hz := hmax.hasDerivAt_eq_zero (hder x 0)
    rw [F.map_zero_apply] at hz
    exact (hboundary x heq).ne hz
  · exact interior_maximal (fun _ (hx : f _ < c) => hx.le) (isOpen_lt hf continuous_const)

/-- The flow strictly enters the sublevel across the boundary. -/
theorem FlowCancellation.strict_sublevel_entry_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 < t → f (F t x) < c := by
  have hforward := forwardInvariant_sublevel_of_boundary F hf hD hder hboundary
  have hlocal :
    ∀ x ∈ {y | f y ≤ c}, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioc 0 ε, F t x ∈ interior {y | f y ≤ c} := by
    intro x hx
    obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rw [interior_sublevel_eq_of_boundary F hf hder hboundary]
    exact hentry t ht
  intro x hx t ht
  have hi := FlowConstruction.interior_entry_of_local F hforward hlocal x hx t ht
  have hi' : F t x ∈ interior {y | f y ≤ c} := hi
  exact
    Eq.mp
      (congrArg (fun S : Set X => F t x ∈ S)
        (interior_sublevel_eq_of_boundary F hf hder hboundary))
      hi'

/-- The level hitting time is unique. -/
theorem FlowCancellation.flow_level_time_unique {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) (x : X) {s t : ℝ} (hs : f (F s x) = c)
    (ht : f (F t x) = c) : s = t := by
  have hnot {a b : ℝ} (ha : f (F a x) = c) (hb : f (F b x) = c) : ¬a < b := by
    intro hab
    have hh :=
      strict_sublevel_entry_of_boundary F hf hD hder hboundary (F a x) ha.le (b - a)
        (sub_pos.mpr hab)
    rw [← F.map_add, sub_add_cancel, hb] at hh
    exact lt_irrefl _ hh
  exact le_antisymm (le_of_not_gt (hnot ht hs)) (le_of_not_gt (hnot hs ht))
