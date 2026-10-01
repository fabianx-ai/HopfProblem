/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime

/-!
# The collar homeomorphism of a flow between two absorbing sets

Let `F : Flow ℝ X` and let `A ⊆ B` be closed, forward invariant and strictly absorbing sets (the
flow moves each of them into its own interior in positive time) such that some time `T > 0`
satisfies `F T '' B ⊆ interior A`. The structure `FlowConstruction.FlowCollarData F A B` records
this. Then `B` is pushed onto `A` along the orbits: every point `x ∈ B` moves forward by
`shift x = duration x * (1 - factor x)`, where `duration x` is the entry time of `x` into the
core `F T '' B`, and `factor x = (T - delay x) / T` with `delay x` the entry time into `A` of
`origin x = F (duration x - T) x`. For `X` Hausdorff and `B` compact this is a
homeomorphism `B ≃ₜ A` which maps `frontier B` onto `frontier A` along the orbits and fixes
`A ∩ frontier B`. It is the reparametrisation in the proof of Milnor, *Morse Theory*,
Theorem 3.1 (`M^a` is diffeomorphic to `M^b`), carried out for a continuous flow.

## Main definitions and results

* `FlowConstruction.FlowCollarData` : the hypotheses; `core`, `duration`, `origin`, `delay`,
  `factor`, `shift` : the auxiliary set and functions, with their continuity.
* `FlowConstruction.FlowCollarData.rescale` : the map `x ↦ F (shift x) x` of `B`; it is
  injective (`rescale_injective`) with image `A` (`rescale_mem_inner`, `exists_rescale_eq`).
* `FlowConstruction.FlowCollarData.homeomorph` : the homeomorphism `B ≃ₜ A`.
* `FlowConstruction.FlowCollarData.homeomorph_mem_frontier_iff`,
  `homeomorph_eq_flow_of_mem_frontier`, `homeomorph_symm_eq_flow_of_mem_frontier`,
  `homeomorph_fixed_on_common_frontier` : its behaviour on the frontiers.

## References

* [John Milnor, *Morse Theory*][milnor63], §3, Theorem 3.1

## Tags

flow, collar, absorbing set, homeomorphism
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-! ### Flow collar data -/

/-- Data for a flow collar: a core, an inner set, and timing bounds. -/
structure FlowConstruction.FlowCollarData {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (A B : Set X) where
  time : ℝ
  time_pos : 0 < time
  closed_outer : IsClosed B
  closed_inner : IsClosed A
  inner_subset : A ⊆ B
  forward_outer : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B
  forward_inner : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A
  strict_outer : ∀ x ∈ B, ∀ t : ℝ, 0 < t → F t x ∈ interior B
  strict_inner : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A
  core_inside : ∀ x ∈ B, F time x ∈ interior A

/-- The core of the flow collar. -/
def FlowConstruction.FlowCollarData.core {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) : Set X :=
  (F (-d.time)) ⁻¹' B

/-- The collar core is closed. -/
theorem FlowConstruction.FlowCollarData.closed_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    IsClosed d.core :=
  d.closed_outer.preimage (F.continuous continuous_const continuous_id)

/-- The collar core is forward invariant. -/
theorem FlowConstruction.FlowCollarData.forward_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    ∀ x ∈ d.core, ∀ t : ℝ, 0 ≤ t → F t x ∈ d.core := by
  intro x hx t ht
  change F (-d.time) (F t x) ∈ B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.forward_outer _ hx t ht

/-- The collar core is strictly absorbing. -/
theorem FlowConstruction.FlowCollarData.strict_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    ∀ x ∈ d.core, ∀ t : ℝ, 0 < t → F t x ∈ interior d.core := by
  intro x hx t ht
  apply preimage_interior_subset_interior_preimage (F.continuous continuous_const continuous_id)
  change F (-d.time) (F t x) ∈ interior B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.strict_outer _ hx t ht

/-- The flow at the duration lands in the core. -/
theorem FlowConstruction.FlowCollarData.flow_time_mem_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : F d.time x ∈ d.core := by
  change F (-d.time) (F d.time x) ∈ B
  simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hx

/-- Every point's flow hits the core. -/
theorem FlowConstruction.FlowCollarData.hits_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ d.core :=
  ⟨d.time, d.time_pos.le, d.flow_time_mem_core hx⟩

/-- Every point's flow hits the inner set. -/
theorem FlowConstruction.FlowCollarData.hits_inner {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A :=
  ⟨d.time, d.time_pos.le, interior_subset (d.core_inside x hx)⟩

/-- The collar duration: the entry time into the inner set. -/
def FlowConstruction.FlowCollarData.duration {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  FlowConstruction.entryTime F d.core x.1

/-- The collar duration is nonnegative. -/
theorem FlowConstruction.FlowCollarData.duration_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.duration x :=
  FlowConstruction.entryTime_nonneg F (d.hits_core x.2)

/-- The collar duration is bounded. -/
theorem FlowConstruction.FlowCollarData.duration_le {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x ≤ d.time :=
  FlowConstruction.entryTime_le_of_mem F d.time_pos.le (d.flow_time_mem_core x.2)

/-- The collar duration is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_duration {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.duration :=
  continuousOn_iff_continuous_domRestrict.mp
    (FlowConstruction.continuousOn_entryTime F d.closed_core d.forward_core d.strict_core
      (fun _ hx => d.hits_core hx))

/-- The collar origin: the entry point in the inner set. -/
def FlowConstruction.FlowCollarData.origin {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : B :=
  ⟨F (d.duration x - d.time) x.1,
    by
    have h := FlowConstruction.flow_entryTime_mem F d.closed_core (d.hits_core x.2)
    change F (-d.time) (F (d.duration x) x.1) ∈ B at h
    simpa only [← F.map_add, sub_eq_add_neg, add_comm] using h⟩

/-- The collar origin is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_origin {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.origin :=
  (F.continuous (d.continuous_duration.sub continuous_const) continuous_subtype_val).subtype_mk _

/-- A point is the flow of its origin for its duration. -/
theorem FlowConstruction.FlowCollarData.origin_reconstruct {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    F (d.time - d.duration x) (d.origin x).1 = x.1 := by
  change F (d.time - d.duration x) (F (d.duration x - d.time) x.1) = x.1
  rw [← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]

/-- The collar delay before reaching the core. -/
def FlowConstruction.FlowCollarData.delay {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  FlowConstruction.entryTime F A (d.origin x).1

/-- The collar delay is nonnegative. -/
theorem FlowConstruction.FlowCollarData.delay_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.delay x :=
  FlowConstruction.entryTime_nonneg F (d.hits_inner (d.origin x).2)

/-- The collar delay is bounded. -/
theorem FlowConstruction.FlowCollarData.delay_lt {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.delay x < d.time :=
  FlowConstruction.entryTime_lt_of_flow_mem_interior F d.time_pos
    (d.core_inside _ (d.origin x).2)

/-- The collar delay is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_delay {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.delay :=
  (continuousOn_iff_continuous_domRestrict.mp
        (FlowConstruction.continuousOn_entryTime F d.closed_inner d.forward_inner
          d.strict_inner (fun _ hx => d.hits_inner hx))).comp
    d.continuous_origin

/-- The rescaling factor of the collar time. -/
def FlowConstruction.FlowCollarData.factor {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  (d.time - d.delay x) / d.time

/-- The rescaling factor is positive. -/
theorem FlowConstruction.FlowCollarData.factor_pos {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 < d.factor x :=
  div_pos (sub_pos.mpr (d.delay_lt x)) d.time_pos

/-- The rescaling factor is at most one. -/
theorem FlowConstruction.FlowCollarData.factor_le_one {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.factor x ≤ 1 := by
  apply (div_le_one d.time_pos).mpr
  linarith [d.delay_nonneg x]

/-- The rescaled time factor identity. -/
theorem FlowConstruction.FlowCollarData.time_mul_factor {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.time * d.factor x = d.time - d.delay x := by
  dsimp [factor]
  field_simp [d.time_pos.ne']

/-- The rescaling factor is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_factor {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.factor :=
  (continuous_const.sub d.continuous_delay).div_const _

/-- The duration is bounded by the retained time. -/
theorem FlowConstruction.FlowCollarData.duration_le_retained {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) (hx : x.1 ∈ A) :
    d.duration x ≤ d.time * d.factor x := by
  have hhit : F (d.time - d.duration x) (d.origin x).1 ∈ A := by rwa [d.origin_reconstruct]
  have h := FlowConstruction.entryTime_le_of_mem F (sub_nonneg.mpr (d.duration_le x)) hhit
  change d.delay x ≤ d.time - d.duration x at h
  rw [d.time_mul_factor]
  linarith

/-- The collar shift of a point. -/
def FlowConstruction.FlowCollarData.shift {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  d.duration x * (1 - d.factor x)

/-- The collar shift is nonnegative. -/
theorem FlowConstruction.FlowCollarData.shift_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.shift x :=
  mul_nonneg (d.duration_nonneg x) (sub_nonneg.mpr (d.factor_le_one x))

/-- The collar shift is bounded by the duration. -/
theorem FlowConstruction.FlowCollarData.shift_le_duration {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.shift x ≤ d.duration x := by
  dsimp [shift]
  nlinarith [mul_nonneg (d.duration_nonneg x) (d.factor_pos x).le]

/-- The collar shift is continuous. -/
theorem FlowConstruction.FlowCollarData.continuous_shift {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Continuous d.shift :=
  d.continuous_duration.mul (continuous_const.sub d.continuous_factor)

/-! ### The collar rescaling -/

/-- The rescaling homeomorphism candidate of the collar. -/
def FlowConstruction.FlowCollarData.rescale {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) : C(B, B)
    where
  toFun x := ⟨F (d.shift x) x.1, d.forward_outer x.1 x.2 _ (d.shift_nonneg x)⟩
  continuous_toFun := (F.continuous d.continuous_shift continuous_subtype_val).subtype_mk _

/-- The rescaling computes from the origin. -/
theorem FlowConstruction.FlowCollarData.rescale_from_origin {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).1 = F (d.time - d.duration x * d.factor x) (d.origin x).1 := by
  change F (d.shift x) x.1 = _
  conv_lhs => rw [← d.origin_reconstruct x]
  rw [← F.map_add]
  congr 1
  dsimp [shift]
  ring

/-- The rescaling lands in the inner set. -/
theorem FlowConstruction.FlowCollarData.rescale_mem_inner {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).1 ∈ A := by
  rw [d.rescale_from_origin]
  have hh : d.delay x ≤ d.time - d.duration x * d.factor x := by
    have h := mul_le_mul_of_nonneg_right (d.duration_le x) (d.factor_pos x).le
    rw [d.time_mul_factor] at h
    linarith
  exact
    (FlowConstruction.entryTime_le_iff F d.closed_inner d.forward_inner
          (d.hits_inner (d.origin x).2) ((d.delay_nonneg x).trans hh)).mp
      hh

/-- The duration of a rescaled point. -/
theorem FlowConstruction.FlowCollarData.duration_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration (d.rescale x) = d.duration x * d.factor x := by
  change FlowConstruction.entryTime F d.core (F (d.shift x) x.1) = _
  rw [FlowConstruction.entryTime_flow_of_le F d.closed_core (d.hits_core x.2)
      (d.shift_nonneg x) (d.shift_le_duration x)]
  change d.duration x - d.shift x = _
  dsimp [shift]
  ring

/-- The origin of a rescaled point. -/
theorem FlowConstruction.FlowCollarData.origin_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.origin (d.rescale x) = d.origin x := by
  apply Subtype.ext
  change F (d.duration (d.rescale x) - d.time) (F (d.shift x) x.1) = F (d.duration x - d.time) x.1
  rw [d.duration_rescale, ← F.map_add]
  congr 1
  dsimp [shift]
  ring

/-- The factor of a rescaled point. -/
theorem FlowConstruction.FlowCollarData.factor_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.factor (d.rescale x) = d.factor x := by
  unfold factor delay
  rw [d.origin_rescale]

/-- The rescaling is injective. -/
theorem FlowConstruction.FlowCollarData.rescale_injective {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Function.Injective d.rescale := by
  intro x y h
  have hfactor : d.factor x = d.factor y := by rw [← d.factor_rescale x, ← d.factor_rescale y, h]
  have hdur : d.duration x = d.duration y := by
    have he := congrArg d.duration h
    rw [d.duration_rescale, d.duration_rescale, hfactor] at he
    exact mul_right_cancel₀ (d.factor_pos y).ne' he
  have horigin : d.origin x = d.origin y := by rw [← d.origin_rescale x, ← d.origin_rescale y, h]
  apply Subtype.ext
  rw [← d.origin_reconstruct x, ← d.origin_reconstruct y, hdur, horigin]

/-- A zero-duration point is fixed by the rescaling. -/
theorem FlowConstruction.FlowCollarData.rescale_eq_self_of_duration_eq_zero {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) (hx : d.duration x = 0) :
    d.rescale x = x := by
  apply Subtype.ext
  change F (d.shift x) x.1 = x.1
  simp only [shift, hx, MulZeroClass.zero_mul, F.map_zero_apply]

/-- Every point is a rescale of a core point. -/
theorem FlowConstruction.FlowCollarData.exists_rescale_eq {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) (y : B)
    (hy : y.1 ∈ A) : ∃ x : B, d.rescale x = y := by
  by_cases hs : d.duration y = 0
  · exact ⟨y, d.rescale_eq_self_of_duration_eq_zero y hs⟩
  have hspos : 0 < d.duration y := lt_of_le_of_ne (d.duration_nonneg y) (Ne.symm hs)
  let r := d.duration y / d.factor y
  have hr₀ : 0 ≤ r := (div_pos hspos (d.factor_pos y)).le
  have hrT : r ≤ d.time := (div_le_iff₀ (d.factor_pos y)).mpr (d.duration_le_retained y hy)
  have hr : r * d.factor y = d.duration y := div_mul_cancel₀ _ (d.factor_pos y).ne'
  have hsr : d.duration y ≤ r := by
    have hh := mul_le_mul_of_nonneg_left (d.factor_le_one y) hr₀
    rwa [mul_one, hr] at hh
  let x : B :=
    ⟨F (d.time - r) (d.origin y).1, d.forward_outer _ (d.origin y).2 _ (sub_nonneg.mpr hrT)⟩
  have hxy : F (r - d.duration y) x.1 = y.1 := by
    change F (r - d.duration y) (F (d.time - r) (d.origin y).1) = y.1
    rw [← F.map_add]
    convert d.origin_reconstruct y using 2
    ring
  have hdx : d.duration x = r := by
    have hh :=
      FlowConstruction.entryTime_eq_add_of_flow_pos F d.closed_core d.forward_core
        (d.hits_core x.2) (sub_nonneg.mpr hsr)
        (show 0 < FlowConstruction.entryTime F d.core (F (r - d.duration y) x.1) by
          rw [hxy]; exact hspos)
    rw [hxy] at hh
    change d.duration x = r - d.duration y + d.duration y at hh
    linarith
  have hox : d.origin x = d.origin y := by
    apply Subtype.ext
    change F (d.duration x - d.time) (F (d.time - r) (d.origin y).1) = _
    rw [hdx, ← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]
  have hfx : d.factor x = d.factor y := by
    unfold factor delay
    rw [hox]
  refine ⟨x, Subtype.ext ?_⟩
  rw [d.rescale_from_origin, hdx, hfx, hox, hr, d.origin_reconstruct]

/-! ### The collar homeomorphism -/

/-- The inner map of the collar homeomorphism. -/
def FlowConstruction.FlowCollarData.innerMap {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) : C(B, A)
    where
  toFun x := ⟨(d.rescale x).1, d.rescale_mem_inner x⟩
  continuous_toFun := (continuous_subtype_val.comp d.rescale.continuous).subtype_mk _

/-- The inner map is bijective. -/
theorem FlowConstruction.FlowCollarData.innerMap_bijective {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) :
    Function.Bijective d.innerMap := by
  constructor
  · intro x y h
    apply d.rescale_injective
    exact Subtype.ext (congrArg (fun z : A => (z : X)) h)
  · intro y
    obtain ⟨x, hx⟩ := d.exists_rescale_eq ⟨y.1, d.inner_subset y.2⟩ y.2
    exact ⟨x, Subtype.ext (congrArg (fun z : B => (z : X)) hx)⟩

/-- The flow collar homeomorphism. -/
def FlowConstruction.FlowCollarData.homeomorph {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : FlowConstruction.FlowCollarData F A B) [T2Space X]
    [CompactSpace B] : B ≃ₜ A :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective d.innerMap d.innerMap_bijective)
    d.innerMap.continuous

/-- The interior is characterized by the duration-time inequality. -/
theorem FlowConstruction.FlowCollarData.duration_lt_time_iff_interior {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x < d.time ↔ (x : X) ∈ interior B := by
  constructor
  · intro hlt
    have hi :=
      d.strict_outer (d.origin x).val (d.origin x).property (d.time - d.duration x)
        (sub_pos.mpr hlt)
    rwa [d.origin_reconstruct] at hi
  · intro hi
    have hcore : F d.time x.val ∈ interior d.core := by
      apply
        preimage_interior_subset_interior_preimage (F.continuous continuous_const continuous_id)
      change F (-d.time) (F d.time x.val) ∈ interior B
      simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hi
    exact FlowConstruction.entryTime_lt_of_flow_mem_interior F d.time_pos hcore

/-- The frontier is characterized by the duration-time equality. -/
theorem FlowConstruction.FlowCollarData.duration_eq_time_iff_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x = d.time ↔ (x : X) ∈ frontier B := by
  rw [frontier, d.closed_outer.closure_eq]
  constructor
  · intro heq
    refine ⟨x.property, ?_⟩
    intro hi
    have hlt := (d.duration_lt_time_iff_interior x).mpr hi
    exact (ne_of_lt hlt) heq
  · intro hx
    apply le_antisymm (d.duration_le x)
    exact le_of_not_gt (fun hlt => hx.2 ((d.duration_lt_time_iff_interior x).mp hlt))

/-- The rescaling preserves the interior. -/
theorem FlowConstruction.FlowCollarData.rescale_mem_interior_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).val ∈ interior A ↔ x.val ∈ interior B := by
  suffices h : (d.rescale x).val ∈ interior A ↔ d.duration x < d.time from
    h.trans (d.duration_lt_time_iff_interior x)
  constructor
  · intro hi
    by_contra hnot
    have heq : d.duration x = d.time := le_antisymm (d.duration_le x) (le_of_not_gt hnot)
    have horigin : (d.origin x).val = x.val := by
      change F (d.duration x - d.time) x.val = x.val
      rw [heq, sub_self, F.map_zero_apply]
    have hentry : F (d.delay x) (d.origin x).val ∈ interior A := by
      rw [d.rescale_from_origin, heq, d.time_mul_factor, sub_sub_cancel] at hi
      exact hi
    by_cases hpos : 0 < d.delay x
    · have hlt := FlowConstruction.entryTime_lt_of_flow_mem_interior F hpos hentry
      exact (lt_irrefl (d.delay x)) hlt
    · have hzero : d.delay x = 0 := le_antisymm (le_of_not_gt hpos) (d.delay_nonneg x)
      rw [hzero, F.map_zero_apply, horigin] at hentry
      have hB := interior_mono d.inner_subset hentry
      exact hnot ((d.duration_lt_time_iff_interior x).mpr hB)
  · intro hlt
    rw [d.rescale_from_origin]
    have hmul := mul_lt_mul_of_pos_right hlt (d.factor_pos x)
    rw [d.time_mul_factor] at hmul
    have hdelay : d.delay x < d.time - d.duration x * d.factor x := by linarith
    exact
      FlowConstruction.flow_mem_interior_of_entryTime_lt F d.closed_inner d.strict_inner
        (d.hits_inner (d.origin x).property) hdelay

/-- The inner map preserves the frontier. -/
theorem FlowConstruction.FlowCollarData.innerMap_mem_frontier_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.innerMap x).val ∈ frontier A ↔ x.val ∈ frontier B := by
  change (d.rescale x).val ∈ frontier A ↔ x.val ∈ frontier B
  rw [frontier, frontier, d.closed_inner.closure_eq, d.closed_outer.closure_eq]
  constructor
  · intro hx
    exact ⟨x.property, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mpr hi)⟩
  · intro hx
    exact ⟨d.rescale_mem_inner x, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mp hi)⟩

/-- The collar homeomorphism preserves the frontier. -/
theorem FlowConstruction.FlowCollarData.homeomorph_mem_frontier_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B) :
    (d.homeomorph x).val ∈ frontier A ↔ x.val ∈ frontier B :=
  d.innerMap_mem_frontier_iff x

/-- The collar homeomorphism computes the flow to the entry time. -/
theorem FlowConstruction.FlowCollarData.homeomorph_eq_flow_entryTime {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hx : x.val ∈ frontier B) :
    (d.homeomorph x).val = F (FlowConstruction.entryTime F A x.val) x.val := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hx
  have ho : (d.origin x).val = x.val := by
    change F (d.duration x - d.time) x.val = x.val
    rw [ht, sub_self, F.map_zero_apply]
  change (d.rescale x).val = _
  rw [d.rescale_from_origin, ht, d.time_mul_factor, sub_sub_cancel]
  change F (FlowConstruction.entryTime F A (d.origin x).val) (d.origin x).val = _
  rw [ho]

/-- The collar homeomorphism on the frontier is the flow. -/
theorem FlowConstruction.FlowCollarData.homeomorph_eq_flow_of_mem_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hx : x.val ∈ frontier B) {t : ℝ} (ht : 0 ≤ t) (hfront : F t x.val ∈ frontier A) :
    (d.homeomorph x).val = F t x.val := by
  rw [d.homeomorph_eq_flow_entryTime x hx,
    FlowConstruction.entryTime_eq_of_flow_mem_frontier F d.closed_inner d.strict_inner ht
      hfront]

/-- The collar homeomorphism inverse on the frontier is the flow. -/
theorem FlowConstruction.FlowCollarData.homeomorph_symm_eq_flow_of_mem_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (y : A)
    (hy : y.val ∈ frontier A) {t : ℝ} (ht : t ≤ 0) (hfront : F t y.val ∈ frontier B) :
    (d.homeomorph.symm y).val = F t y.val := by
  have hmem : F t y.val ∈ B := by
    simpa only [d.closed_outer.closure_eq] using frontier_subset_closure hfront
  let x : B := ⟨F t y.val, hmem⟩
  have hreturn : F (-t) x.val = y.val := by
    change F (-t) (F t y.val) = y.val
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have heq : d.homeomorph x = y := by
    apply Subtype.ext
    rw [d.homeomorph_eq_flow_of_mem_frontier x hfront (neg_nonneg.mpr ht) (hreturn ▸ hy), hreturn]
  have hinv := congrArg d.homeomorph.symm heq
  rw [d.homeomorph.symm_apply_apply] at hinv
  exact congrArg (fun z : B => z.val) hinv.symm

/-- The rescaling fixes the inner frontier. -/
theorem FlowConstruction.FlowCollarData.rescale_eq_self_of_mem_inner_frontier_outer
    {X : Type*} [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) (x : B) (hxA : x.val ∈ A)
    (hxB : x.val ∈ frontier B) : d.rescale x = x := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hxB
  have hret := d.duration_le_retained x hxA
  rw [ht] at hret
  have hfac : d.factor x = 1 := by nlinarith [d.factor_le_one x, d.time_pos]
  apply Subtype.ext
  change F (d.shift x) x.val = x.val
  simp only [shift, hfac, sub_self, MulZeroClass.mul_zero, F.map_zero_apply]

/-- The collar homeomorphism fixes the common frontier. -/
theorem FlowConstruction.FlowCollarData.homeomorph_fixed_on_common_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hxA : x.val ∈ A) (hxB : x.val ∈ frontier B) : (d.homeomorph x).val = x.val :=
  congrArg (fun y : B => y.val) (d.rescale_eq_self_of_mem_inner_frontier_outer x hxA hxB)
