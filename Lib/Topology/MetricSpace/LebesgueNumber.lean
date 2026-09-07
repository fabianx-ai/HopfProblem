module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sets.OpenCover

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open Set

universe u v

namespace Metric

/-!
# A same-radius diameter form of the Lebesgue number lemma

This file translates the ball-form Lebesgue number lemma and canonical Corollary 2.1 from
`TEXTBOOK.md`, lines 1329--1346.  For a compact metric space, the radius chosen for the ball
cover is used unchanged to control every nonempty subset of smaller diameter.
-/

/-- Canonical Corollary 2.1: a nonempty set whose diameter is smaller than a fixed ball-cover
radius lies in one member of the cover, at that same radius. -/
public theorem subset_cover_of_diam_lt_of_ball_cover
    {X : Type u} [MetricSpace X] [CompactSpace X] {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) (δ : ℝ) (hδ : 0 < δ)
    (hball : ∀ x : X, ∃ i : ι, Metric.ball x δ ⊆ U i)
    (A : Set X) (hA : A.Nonempty) (hdiam : Metric.diam A < δ) :
    ∃ i : ι, A ⊆ U i := by
  refine (fun _ : 0 < δ => ?_) hδ
  -- L-01: choose the textbook point `a ∈ A` and the cover member containing `B(a, δ)`.
  rcases hA with ⟨a, ha⟩
  rcases hball a with ⟨i, hai⟩
  refine ⟨i, ?_⟩
  -- L-02: compactness supplies the boundedness needed by the real-diameter inequality.
  have hbounded : Bornology.IsBounded A := Metric.isBounded_of_compactSpace
  -- L-03: `d(a,b) ≤ diam A < δ`, so every `b ∈ A` lies in the chosen ball and cover member.
  intro b hb
  have hab : dist a b ≤ Metric.diam A :=
    Metric.dist_le_diam_of_mem hbounded ha hb
  have habδ : dist a b < δ := lt_of_le_of_lt hab hdiam
  have hbaδ : dist b a < δ := by
    simpa only [dist_comm] using habδ
  have hbball : b ∈ Metric.ball a δ := Metric.mem_ball.mpr hbaδ
  exact hai hbball

/-- The ball-form Lebesgue lemma together with canonical Corollary 2.1: one positive radius works
simultaneously for the ball clause and for every nonempty subset of smaller diameter. -/
public theorem exists_lebesgue_number_diam
    {X : Type u} [MetricSpace X] [CompactSpace X] {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x : X, ∃ i : ι, Metric.ball x δ ⊆ U i) ∧
      (∀ A : Set X, A.Nonempty → Metric.diam A < δ → ∃ i : ι, A ⊆ U i) := by
  -- L-05: specialize Mathlib's ball-form lemma to the whole compact metric space.
  rcases lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set X)) (c := fun i ↦ (U i : Set X))
      isCompact_univ (fun i ↦ (U i).isOpen)
      (by rw [hU.iSup_set_eq_univ]) with ⟨δ, hδ, hball⟩
  have hball' : ∀ x : X, ∃ i : ι, Metric.ball x δ ⊆ U i := by
    simpa only [Set.mem_univ, forall_const] using hball
  refine ⟨δ, hδ, hball', ?_⟩
  -- L-06: apply Corollary 2.1 without halving or reselecting the ball-form radius.
  intro A hA hdiam
  exact subset_cover_of_diam_lt_of_ball_cover U δ hδ hball' A hA hdiam

end Metric
