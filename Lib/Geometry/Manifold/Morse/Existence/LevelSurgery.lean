/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating

/-!
# Level sets across a handle as surgery boundary pairs

When the sublevel set `{f ≤ f p + ρ²}` is obtained from `{f ≤ f p - ρ²}` by attaching a handle
along a signed Morse chart, the upper level set `{f = f p + ρ²}` is obtained from the lower level
set `{f = f p - ρ²}` by surgery: removing a thickened attaching sphere `S^{k-1} × D^{n-k}` and
gluing in `D^k × S^{n-k-1}` (Milnor, *Morse theory*, §3; Milnor, *Lectures on the h-cobordism
theorem*, §3). This file packages the two level sets as a `SurgeryBoundaryPair` and identifies
the complements of the surgery regions.

## Main definitions and results

* `SurgeryBoundaryPair.changeNewBoundary`: transport the new side of a pair along a homeomorphism.
* `ClosedCover.frontierLevelHomeomorph`: a level-preserving homeomorphism of a closed set onto a
  sublevel set restricts to its frontier and the level set.
* `SurgeryBoundaryPair.complementHomeomorph`: the complements of the surgery regions agree.
* `ManifoldMorse.SignedMorseChart.levelSurgeryBoundaryPair`: the surgery pair of the two levels.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65]

## Tags

Morse theory, surgery, level set
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Surgery boundary pairs -/

/-- The boundary pair with the new boundary exchanged. -/
def SurgeryBoundaryPair.changeNewBoundary {N P R X Y Z : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (d : SurgeryBoundaryPair N P R X Y) (e : Y ≃ₜ Z) :
    SurgeryBoundaryPair N P R X Z
    where
  oldExterior := d.oldExterior
  newExterior := e ∘ d.newExterior
  oldPiece := d.oldPiece
  newPiece := e ∘ d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := e.isClosedEmbedding.comp d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := e.isClosedEmbedding.comp d.newPiece_closed
  old_cover := d.old_cover
  new_cover := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : e.symm z ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by
      rw [d.new_cover]
      trivial
    rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
    · exact Or.inl ⟨r, (congrArg e hr).trans (e.apply_symm_apply z)⟩
    · exact Or.inr ⟨p, (congrArg e hp).trans (e.apply_symm_apply z)⟩
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := fun r p => e.injective.eq_iff.trans (d.new_overlap r p)

/-- The frontier of a closed cover piece is level-homeomorphic. -/
def ClosedCover.frontierLevelHomeomorph {M : Type*} [TopologicalSpace M] {f : M → ℝ} {b : ℝ}
    {A : Set M} (hA : IsClosed A) (e : A ≃ₜ { x : M // f x ≤ b })
    (he : ∀ x, f (e x) = b ↔ (x : M) ∈ frontier A) : frontier A ≃ₜ { x : M // f x = b } := by
  have hsub : frontier A ⊆ A := by
    intro x hx
    have hc := frontier_subset_closure hx
    rwa [hA.closure_eq] at hc
  let toA : frontier A → A := Set.inclusion hsub
  let toB : { x : M // f x = b } → { x : M // f x ≤ b } := fun x => ⟨x, x.property.le⟩
  refine
    { toFun := fun x => ⟨e (toA x), (he (toA x)).mpr x.property⟩
      invFun := fun y => ⟨e.symm (toB y), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (he (e.symm (toB y))).mp
    rw [e.apply_symm_apply]
    exact y.property
  · intro x
    apply Subtype.ext
    exact congrArg (fun z : A => (z : M)) (e.symm_apply_apply (toA x))
  · intro y
    apply Subtype.ext
    exact congrArg (fun z : { x : M // f x ≤ b } => (z : M)) (e.apply_symm_apply (toB y))
  · exact
      (continuous_subtype_val.comp
            (e.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk
        _
  · exact
      (continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk
        _

/-- The boundary exchange preserves incidence. -/
theorem SurgeryBoundaryPair.exchange_preserves_incidence {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) (r : R)
    (p : PuncturedHandle.UnitSphere E × PuncturedHandle.PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      d.newExteriorMap r = d.newPuncturedMap (PuncturedHandle.exchange E F p) := by
  rw [d.oldPunctured_overlap, d.newPunctured_overlap]
  constructor
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, PuncturedHandle.exchange_boundary q.1 q.2⟩
  · rintro ⟨q, hr, hq⟩
    refine ⟨q, hr, (PuncturedHandle.exchange E F).injective ?_⟩
    exact hq.trans (PuncturedHandle.exchange_boundary q.1 q.2).symm

/-- The boundary-pair complements are homeomorphic. -/
def SurgeryBoundaryPair.complementHomeomorph {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace R]
    [TopologicalSpace X] [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y) :
    d.OldComplement ≃ₜ d.NewComplement :=
  ClosedCover.homeomorphOfClosedPieces d.oldExteriorMap d.newExteriorMap d.oldPuncturedMap
    d.newPuncturedMap d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_newExteriorMap
    d.isClosedEmbedding_oldPuncturedMap d.isClosedEmbedding_newPuncturedMap d.oldComplement_cover
    d.newComplement_cover (PuncturedHandle.exchange E F) d.exchange_preserves_incidence

attribute [local instance 100] Classical.propDecidable in
/-- The chart's boundary levels are homeomorphic. -/
def ManifoldMorse.SignedMorseChart.boundaryLevelHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) :
    frontier ({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.normHandleMap ρ hρ hblock)) ≃ₜ
      { x : M // f x = f p + ρ ^ 2 } :=
  (Homeomorph.setCongr (by rw [c.range_normHandleMap ρ hρ hblock])).trans
    (ClosedCover.frontierLevelHomeomorph
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      e he)

attribute [local instance 100] Classical.propDecidable in
/-- The surgery boundary pair of a signed chart level. -/
def ManifoldMorse.SignedMorseChart.levelSurgeryBoundaryPair {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) :
    SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates
      { x : M //
        f x = f p - ρ ^ 2 ∧
          x ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.normHandleMap ρ hρ hblock)) }
      { x : M // f x = f p - ρ ^ 2 } { x : M // f x = f p + ρ ^ 2 } :=
  (c.attachmentBoundaryData hf ρ hρ hblock hlevel).surgeryBoundaryPair.changeNewBoundary
    (c.boundaryLevelHomeomorph hf ρ hρ hblock e he)
