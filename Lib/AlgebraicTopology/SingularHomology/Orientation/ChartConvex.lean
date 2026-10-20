/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.LocalToGlobal

/-!
# Chart-convex sets and finite unions

A *chart-convex* set of a manifold `M` modelled on `ℝⁿ` is the preimage under a chart `e` of a
compact convex subset of `e.target` (`IsChartConvex e Q`).  Such sets are the "compact convex sets
in a chart identified with `ℝⁿ`" of Hatcher's Lemma 3.27, step (2), and the accepted textbook's
P10/P16.  They are homology balls in every degree (`IsChartConvex.isHomologyBall`, transported
from `Orientation/LocalHomology.lean` through excision and the chart), connected, closed under
intersection, and they meet small balls in balls (`IsChartConvex.meetsBallsInBalls`), so the
agreement lemma applies to them.  This gives Lemma 3.27 for a chart-convex set
(`LocalToGlobal.of_isChartConvex`) and then, by the Mayer–Vietoris step, for finite unions of
sets from any class closed under intersection and satisfying the lemma
(`LocalToGlobal.of_list`), in particular for finite unions of chart-convex sets of one chart
(`LocalToGlobal.of_isChartConvex_list`).

## Main definitions and results

* `ManifoldOrientation.IsChartConvex`, `IsChartConvex.inter`, `IsChartConvex.isHomologyBall`,
  `IsChartConvex.meetsBallsInBalls`, `ManifoldOrientation.exists_chartBall`.
* `ManifoldOrientation.LocalToGlobal.of_isChartConvex` : Lemma 3.27 for a chart-convex set.
* `ManifoldOrientation.LocalToGlobal.of_list`, `LocalToGlobal.of_isChartConvex_list` : finite
  unions.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, Lemma 3.27, steps (1) and (2)

## Tags

local-to-global, convex, chart, finite union
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ManifoldOrientation

open RelativeSingularHomology

variable {M : Type} [TopologicalSpace M] {n : ℕ}

/-! ### Unions of lists of sets -/

/-- The union of a list of sets. -/
def listUnion {X : Type*} (l : List (Set X)) : Set X := l.foldr (· ∪ ·) ∅

@[simp] theorem listUnion_nil {X : Type*} : listUnion ([] : List (Set X)) = ∅ := rfl

@[simp] theorem listUnion_cons {X : Type*} (Q : Set X) (l : List (Set X)) :
    listUnion (Q :: l) = Q ∪ listUnion l := rfl

theorem listUnion_inter {X : Type*} (l : List (Set X)) (Q : Set X) :
    listUnion l ∩ Q = listUnion (l.map (· ∩ Q)) := by
  induction l with
  | nil => simp
  | cons P l ih => simp [union_inter_distrib_right, ih]

theorem subset_listUnion_of_mem {X : Type*} {l : List (Set X)} {Q : Set X} (hQ : Q ∈ l) :
    Q ⊆ listUnion l := by
  induction l with
  | nil => simp at hQ
  | cons P l ih =>
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact subset_union_left
    · exact ih hQ |>.trans subset_union_right

theorem listUnion_subset {X : Type*} {l : List (Set X)} {W : Set X} (h : ∀ Q ∈ l, Q ⊆ W) :
    listUnion l ⊆ W := by
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [listUnion_cons]
    exact union_subset (h P (List.mem_cons_self ..)) (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

theorem isCompact_listUnion {l : List (Set M)} (h : ∀ Q ∈ l, IsCompact Q) : IsCompact (listUnion l) := by
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [listUnion_cons]
    exact (h P (List.mem_cons_self ..)).union (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

/-! ### Finite unions from a class closed under intersection -/

/-- **Finite unions** (Hatcher's step (1), iterated): if a class `𝒞` of compact sets is closed under
intersection and every member satisfies the local-to-global property, so does every finite union
of members. -/
theorem LocalToGlobal.of_list [T2Space M] (𝒞 : Set (Set M))
    (h𝒞 : ∀ A ∈ 𝒞, IsCompact A ∧ LocalToGlobal M n Aᶜ)
    (hinter : ∀ A ∈ 𝒞, ∀ B ∈ 𝒞, A ∩ B ∈ 𝒞) :
    ∀ (k : ℕ) (l : List (Set M)), l.length = k → (∀ A ∈ l, A ∈ 𝒞) → LocalToGlobal M n (listUnion l)ᶜ := by
  intro k
  induction k with
  | zero =>
    intro l hl _
    rw [List.length_eq_zero_iff] at hl
    subst hl
    exact LocalToGlobal.univ.congr (by simp)
  | succ k ih =>
    intro l hl hl𝒞
    obtain ⟨Q, l', rfl⟩ : ∃ Q l', l = Q :: l' := by
      cases l with
      | nil => simp at hl
      | cons Q l' => exact ⟨Q, l', rfl⟩
    have hQ : Q ∈ 𝒞 := hl𝒞 Q (List.mem_cons_self ..)
    have hl' : ∀ A ∈ l', A ∈ 𝒞 := fun A hA => hl𝒞 A (List.mem_cons_of_mem _ hA)
    have hU : LocalToGlobal M n (listUnion l')ᶜ := ih l' (by simpa using hl) hl'
    have hV : LocalToGlobal M n Qᶜ := (h𝒞 Q hQ).2
    have hUV : LocalToGlobal M n ((listUnion l')ᶜ ∪ Qᶜ) := by
      have := ih (l'.map (· ∩ Q)) (by simpa using hl) (by
        intro A hA
        obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
        exact hinter B (hl' B hB) Q hQ)
      refine this.congr ?_
      rw [← listUnion_inter, compl_inter]
    have hUo : IsOpen (listUnion l')ᶜ :=
      (isCompact_listUnion fun A hA => (h𝒞 A (hl' A hA)).1).isClosed.isOpen_compl
    have hVo : IsOpen Qᶜ := (h𝒞 Q hQ).1.isClosed.isOpen_compl
    refine (LocalToGlobal.inter hUo hVo hU hV hUV).congr ?_
    rw [listUnion_cons, compl_union, inter_comm]

/-! ### Chart-convex sets -/

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- `Q ⊆ M` is chart-convex for the chart `e` if it is the preimage under `e` of a compact convex
subset of `e.target`. -/
def IsChartConvex (e : OpenPartialHomeomorph M E) (Q : Set M) : Prop :=
  ∃ Q' : Set E, Convex ℝ Q' ∧ IsCompact Q' ∧ Q' ⊆ e.target ∧ Q = e.symm '' Q'

variable {e : OpenPartialHomeomorph M E}

omit [ProperSpace E] in
theorem IsChartConvex.isCompact {Q : Set M} (hQ : IsChartConvex e Q) : IsCompact Q := by
  obtain ⟨Q', _, hQ'c, hQ't, rfl⟩ := hQ
  exact hQ'c.image_of_continuousOn (e.continuousOn_symm.mono hQ't)

omit [ProperSpace E] in
theorem IsChartConvex.subset_source {Q : Set M} (hQ : IsChartConvex e Q) : Q ⊆ e.source := by
  obtain ⟨Q', _, _, hQ't, rfl⟩ := hQ
  rintro _ ⟨y, hy, rfl⟩
  exact e.map_target (hQ't hy)

omit [ProperSpace E] in
theorem IsChartConvex.isPreconnected {Q : Set M} (hQ : IsChartConvex e Q) : IsPreconnected Q := by
  obtain ⟨Q', hQ'conv, _, hQ't, rfl⟩ := hQ
  exact hQ'conv.isPreconnected.image _ (e.continuousOn_symm.mono hQ't)

omit [ProperSpace E] in
theorem IsChartConvex.inter {Q₁ Q₂ : Set M} (h₁ : IsChartConvex e Q₁) (h₂ : IsChartConvex e Q₂) :
    IsChartConvex e (Q₁ ∩ Q₂) := by
  obtain ⟨Q₁', hc₁, hk₁, ht₁, rfl⟩ := h₁
  obtain ⟨Q₂', hc₂, hk₂, ht₂, rfl⟩ := h₂
  refine ⟨Q₁' ∩ Q₂', hc₁.inter hc₂, hk₁.inter_right hk₂.isClosed, inter_subset_left.trans ht₁, ?_⟩
  rw [← e.symm.injOn.image_inter (by rw [e.symm_source]; exact ht₁) (by rw [e.symm_source]; exact ht₂)]

/-- A closed-ball preimage is chart-convex. -/
theorem isChartConvex_symm_image_closedBall {c : E} {r : ℝ} (hr : Metric.closedBall c r ⊆ e.target) :
    IsChartConvex e (e.symm '' Metric.closedBall c r) :=
  ⟨_, convex_closedBall c r, isCompact_closedBall c r, hr, rfl⟩

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- Every neighbourhood of a point of the chart domain contains a chart ball (the preimage of a
closed ball in the chart) with the point in its interior, and the closed ball inside the target. -/
theorem exists_chartBall {x : M} (hx : x ∈ e.source) {W : Set M} (hW : W ∈ 𝓝 x) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (e x) r ⊆ e.target ∧
      e.symm '' Metric.closedBall (e x) r ⊆ W ∧ x ∈ interior (e.symm '' Metric.closedBall (e x) r) := by
  have hV : IsOpen (e.source ∩ interior W) := e.open_source.inter isOpen_interior
  have hxV : x ∈ e.source ∩ interior W := ⟨hx, mem_interior_iff_mem_nhds.mpr hW⟩
  have himg : IsOpen (e '' (e.source ∩ interior W)) :=
    e.isOpen_image_of_subset_source hV inter_subset_left
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp himg (e x) ⟨x, hxV, rfl⟩
  have hDball : Metric.closedBall (e x) (r / 2) ⊆ Metric.ball (e x) r :=
    Metric.closedBall_subset_ball (by linarith)
  have hDimg : Metric.closedBall (e x) (r / 2) ⊆ e '' (e.source ∩ interior W) := hDball.trans hball
  have hDt : Metric.closedBall (e x) (r / 2) ⊆ e.target := fun d hd => by
    obtain ⟨y, hy, rfl⟩ := hDimg hd
    exact e.map_source hy.1
  refine ⟨r / 2, by linarith, hDt, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hDimg hd
    rw [e.left_inv hy.1]
    exact interior_subset hy.2
  · have hopen : IsOpen (e.symm '' Metric.ball (e x) (r / 2)) :=
      e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (by rw [e.symm_source]; exact Metric.ball_subset_closedBall.trans hDt)
    apply interior_mono (image_mono Metric.ball_subset_closedBall)
    rw [hopen.interior_eq]
    exact ⟨e x, Metric.mem_ball_self (by linarith), e.left_inv hx⟩

omit [ProperSpace E] in
/-- A chart-convex set is a homology ball in every degree. -/
theorem IsChartConvex.isHomologyBall [T2Space M] {Q : Set M} (hQ : IsChartConvex e Q) (i : ℕ) :
    IsHomologyBall M i Q := by
  obtain ⟨Q', hQ'conv, hQ'c, hQ't, rfl⟩ := hQ
  have h₁ : IsHomologyBall E i Q' := isHomologyBall_of_convex hQ'conv hQ'c.isBounded i
  have h₂ : IsHomologyBall e.target i (trace Q' e.target) :=
    (isHomologyBall_trace_iff e.open_target hQ'c.isClosed.isOpen_compl hQ't i).mpr h₁
  have h₃ : IsHomologyBall e.source i (trace (e.symm '' Q') e.source) := by
    rw [← symm_image_trace e hQ't]
    exact (isHomologyBall_image_iff e.toHomeomorphSourceTarget.symm _ i).mp h₂
  have hK : IsCompact (e.symm '' Q') := hQ'c.image_of_continuousOn (e.continuousOn_symm.mono hQ't)
  exact (isHomologyBall_trace_iff e.open_source hK.isClosed.isOpen_compl
    (IsChartConvex.subset_source ⟨Q', hQ'conv, hQ'c, hQ't, rfl⟩) i).mp h₃

/-- A chart-convex set meets small chart balls in chart-convex sets, hence in homology balls. -/
theorem IsChartConvex.meetsBallsInBalls [T2Space M] {Q : Set M} (hQ : IsChartConvex e Q) :
    MeetsBallsInBalls M n Q := by
  intro x hx W hW
  obtain ⟨r, _, hrt, hrW, hxr⟩ := exists_chartBall (hQ.subset_source hx) hW
  exact ⟨_, hxr, hrW, ((isChartConvex_symm_image_closedBall hrt).inter hQ).isHomologyBall n⟩

end Chart

/-! ### Lemma 3.27 for chart-convex sets and their finite unions -/

section Manifold

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}

/-- **Lemma 3.27 for a chart-convex set** (Hatcher's step (2)): the local-to-global property holds
for `M ∖ Q`, `Q` chart-convex, in dimension `n ≥ 2`. -/
theorem LocalToGlobal.of_isChartConvex (hn : 2 ≤ n) {Q : Set M} (hQ : IsChartConvex e Q) :
    LocalToGlobal M n Qᶜ := by
  rcases Q.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact LocalToGlobal.univ.congr (by simp)
  · have hball : ∀ i, IsHomologyBall M i Q := hQ.isHomologyBall
    refine ⟨fun i hi => ?_, fun α hα => ?_, fun s hs => ?_⟩
    · -- vanishing above `n`, through the local homology at `x₀`
      have := localHomology_subsingleton hn x₀ i (by omega)
      exact (LinearEquiv.ofBijective _ (hball i x₀ hx₀)).injective.subsingleton
    · exact (hball n x₀ hx₀).1 (by rw [map_zero]; exact hα x₀ (not_not.mpr hx₀))
    · -- the class determined at `x₀`, then agreement on the connected `Q`
      obtain ⟨α, hα⟩ := (hball n x₀ hx₀).2 (s x₀)
      refine ⟨α, fun x hx => ?_⟩
      exact eqOn_of_agree hQ.meetsBallsInBalls hQ.isPreconnected α hs hx₀ hα x (not_not.mp hx)

/-- The local-to-global property for a finite union of chart-convex sets of one chart. -/
theorem LocalToGlobal.of_isChartConvex_list (hn : 2 ≤ n) (l : List (Set M))
    (hl : ∀ Q ∈ l, IsChartConvex e Q) : LocalToGlobal M n (listUnion l)ᶜ :=
  LocalToGlobal.of_list {Q | IsChartConvex e Q}
    (fun _ hQ => ⟨hQ.isCompact, LocalToGlobal.of_isChartConvex hn hQ⟩)
    (fun _ hA _ hB => hA.inter hB) l.length l rfl hl

end Manifold

end ManifoldOrientation
