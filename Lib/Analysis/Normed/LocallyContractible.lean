/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Strong local contractibility in real normed spaces

Real normed spaces, including their closed balls with the subspace topology, have neighborhood
bases of contractible balls.
-/

@[expose] public section

noncomputable section

open Filter Function Set Topology

/-- A real seminormed vector space is strongly locally contractible. -/
theorem normedSpaceStronglyLocallyContractible (E : Type*)
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E :=
  StronglyLocallyContractibleSpace.of_bases
    (p := fun (_ : E) (r : ℝ) ↦ 0 < r)
    (s := fun x r ↦ Metric.ball x r)
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun x r hr ↦
      (convex_ball x r).contractibleSpace ⟨x, Metric.mem_ball_self hr⟩)

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A metric ball in the subspace topology of a closed ball is the intersection of the two
corresponding ambient balls. -/
def ballInClosedBallHomeomorph (c : E) (R : ℝ)
    (x : closedBall c R) (r : ℝ) :
    (ball x r : Set (closedBall c R)) ≃ₜ
      (closedBall c R ∩ ball (x : E) r : Set E) where
  toFun y := ⟨y.1.1, y.1.2, y.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun y : (closedBall c R ∩ ball (x : E) r : Set E) ↦
        (⟨y.1, y.2.1⟩ : closedBall c R)) :=
      continuous_subtype_val.subtype_mk _
    exact h.subtype_mk _

/-- Every positive-radius subspace ball in a closed ball of a real normed space is contractible. -/
theorem ballInClosedBall_contractible (c : E) (R : ℝ)
    (x : closedBall c R) (r : ℝ) (hr : 0 < r) :
    ContractibleSpace (ball x r : Set (closedBall c R)) := by
  rw [(ballInClosedBallHomeomorph c R x r).contractibleSpace_iff]
  apply Convex.contractibleSpace
  · exact (convex_closedBall c R).inter (convex_ball (x : E) r)
  · exact ⟨(x : E), x.2, mem_ball_self hr⟩

/-- Every closed ball in a real normed space has a basis of contractible subspace balls, including
at boundary points. -/
instance closedBallStronglyLocallyContractible (c : E) (R : ℝ) :
    StronglyLocallyContractibleSpace (closedBall c R) := by
  apply StronglyLocallyContractibleSpace.of_bases
  · intro x
    exact nhds_basis_ball
  · intro x r hr
    exact ballInClosedBall_contractible c R x r hr

end Metric
