/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment

/-!
# Ball coordinates and the core attaching map of a Morse handle

For a signed Morse chart `c` at a critical point `p` of `f` (Morse-lemma coordinates
`E ≃ N × P` in which `f = f p - ‖u‖² + ‖v‖²`), `Morse.HandleAttachment` constructs the handle
`c.attachingHandleMap ρ : D(N) × D(P) → M` attached to the sublevel `{f ≤ f p - ρ²}`. This file
re-expresses it on the unit balls written as `PuncturedHandle.UnitBall`, packages its boundary
behaviour as an `AttachmentBoundaryData`, and restricts the attaching map to the core sphere
`S(N) × {0}`: the attaching sphere of the handle in the level `{f = f p - ρ²}` (cf. Milnor,
*Lectures on the h-cobordism theorem*, §3, the left-hand sphere of a critical point).

## Main definitions and results

* `MorseHandle.unitBallHomeomorph` : `PuncturedHandle.UnitBall N ≃ₜ MorseHandle.UnitDisk N`.
* `ManifoldMorse.SignedMorseChart.handleBallCoordinates`,
  `ManifoldMorse.SignedMorseChart.normHandleMap`, `range_normHandleMap` : the handle map on
  `UnitBall N × UnitBall P`, with the same range as `attachingHandleMap`.
* `ManifoldMorse.SignedMorseChart.attachmentBoundaryData` : the boundary data of the
  attachment to the sublevel `{f ≤ f p - ρ²}`.
* `ManifoldMorse.SignedMorseChart.attachingCoreMap` : the attaching sphere
  `u ↦ c.splitChart.symm (ρ • u, 0)` as a map into the level set, smooth as a map into `M`
  (`contMDiff_attachingCoreMap_ambient`) and into the level (`contMDiff_attachingCoreMap`).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3

## Tags

Morse theory, handle, attaching sphere
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

@[expose] public noncomputable section

/-! ### Handle ball coordinates -/

/-- The unit ball homeomorphism of a handle chart. -/
def MorseHandle.unitBallHomeomorph (N : Type*) [NormedAddCommGroup N] :
    PuncturedHandle.UnitBall N ≃ₜ UnitDisk N
    where
  toFun z := ⟨z, mem_closedBall_zero_iff.mpr z.property⟩
  invFun z := ⟨z, mem_closedBall_zero_iff.mp z.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

attribute [local instance 100] Classical.propDecidable in
/-- The ball coordinates of a signed Morse chart's handle. -/
def ManifoldMorse.SignedMorseChart.handleBallCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    (PuncturedHandle.UnitBall c.NegativeCoordinates ×
        PuncturedHandle.UnitBall c.PositiveCoordinates) ≃ₜ
      (MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates) :=
  (MorseHandle.unitBallHomeomorph c.NegativeCoordinates).prodCongr
    (MorseHandle.unitBallHomeomorph c.PositiveCoordinates)

attribute [local instance 100] Classical.propDecidable in
/-- The handle map of a signed chart in norm coordinates. -/
def ManifoldMorse.SignedMorseChart.normHandleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(PuncturedHandle.UnitBall c.NegativeCoordinates ×
        PuncturedHandle.UnitBall c.PositiveCoordinates,
      M) :=
  ⟨fun z => c.attachingHandleMap ρ hρ hblock (c.handleBallCoordinates z),
    (c.attachingHandleMap ρ hρ hblock).continuous.comp c.handleBallCoordinates.continuous⟩

attribute [local instance 100] Classical.propDecidable in
/-- The norm handle map's range. -/
theorem ManifoldMorse.SignedMorseChart.range_normHandleMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Set.range (c.normHandleMap ρ hρ hblock) = Set.range (c.attachingHandleMap ρ hρ hblock) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨c.handleBallCoordinates z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨c.handleBallCoordinates.symm z, ?_⟩
    change
      c.attachingHandleMap ρ hρ hblock
          (c.handleBallCoordinates (c.handleBallCoordinates.symm z)) =
        _
    rw [c.handleBallCoordinates.apply_symm_apply]

/-! ### Attaching maps -/

attribute [local instance 100] Classical.propDecidable in
/-- The boundary data of the handle attachment. -/
def ManifoldMorse.SignedMorseChart.attachmentBoundaryData {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) :
    AttachmentBoundaryData c.NegativeCoordinates c.PositiveCoordinates M f (f p - ρ ^ 2)
    where
  handle := c.normHandleMap ρ hρ hblock
  handle_closed :=
    (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).comp
      c.handleBallCoordinates.isClosedEmbedding
  height_continuous := hf
  lower_frontier := hlevel
  lower_face := fun z => by
    constructor
    · intro hz
      exact (c.attachingHandleMap_lower_iff ρ hρ hblock (c.handleBallCoordinates z)).mp hz.le
    · intro hz
      exact c.attachingHandleMap_boundary_height ρ hρ hblock (c.handleBallCoordinates z) hz
  upper_face := fun z => by
    rw [c.range_normHandleMap ρ hρ hblock]
    exact c.attachingHandleMap_mem_frontier_iff hf ρ hρ hblock (c.handleBallCoordinates z)

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map of the signed chart. -/
def ManifoldMorse.SignedMorseChart.attachingCoreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(PuncturedHandle.UnitSphere c.NegativeCoordinates, { y : M // f y = f p - ρ ^ 2 }) :=
  (c.attachingBoundaryMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map computes the attaching point. -/
theorem ManifoldMorse.SignedMorseChart.attachingCoreMap_coe {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    (c.attachingCoreMap ρ hρ hblock u : M) =
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) := by
  change
    c.splitChart.symm
        ((ρ * Real.sqrt (1 + ‖(0 : c.PositiveCoordinates)‖ ^ 2)) • (u : c.NegativeCoordinates),
          ρ • (0 : c.PositiveCoordinates)) =
      _
  simp

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map is smooth into the ambient manifold. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_attachingCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) := by
  have heq :
    Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) :=
    funext (c.attachingCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (Subtype.val :
        PuncturedHandle.UnitSphere c.NegativeCoordinates → c.NegativeCoordinates) :=
    contMDiff_coe_sphere (E := c.NegativeCoordinates) (n := n)
  have hscalar :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : PuncturedHandle.UnitSphere c.NegativeCoordinates => ρ) :=
    contMDiff_const
  have hnegative :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        ρ • (u : c.NegativeCoordinates)) :=
    hscalar.smul hcoe
  have hcoords :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun u : PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        (ρ • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) :=
    hnegative.prodMk_space contMDiff_const
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro u
  have hh :=
    hblock
      (MorseHandle.modelMap_mem_product hρ
        (⟨(u : c.NegativeCoordinates), Metric.sphere_subset_closedBall u.property⟩,
          (⟨0, by simp⟩ : MorseHandle.UnitDisk c.PositiveCoordinates)))
  simpa [MorseHandle.modelMap] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map is smooth. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (c.attachingCoreMap ρ hρ hblock) := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact
    (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n)
          (c.attachingCoreMap ρ hρ hblock)).mpr
      (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock)
