/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.RegularLevel

/-!
# Handle attachment across a regular level

Closed attachments, punctured handles, surgery boundary pairs, attachment boundary data,
and the radial extension filling the core; with the homology rows
(`lower_homologyOne_subsingleton_of_indices`,
`attachingHomology_subsingleton_of_index`) giving the handle-attachment exact-sequence
fragments: passing an index-λ critical point changes homology only in degrees λ−1, λ.

## Main definitions and results

* `ClosedAttachment.*`, `AttachmentBoundaryData.*`,
  `SurgeryBoundaryPair.*`, `PuncturedHandle.*`, `RadialExtension.*`.
* `ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices` : the
  homology consequence.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3, Thm 3.4
* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.3

## Tags

handle attachment, surgery, radial extension
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

attribute [local instance 100] Classical.propDecidable in
/-- The attaching handle map of a signed Morse chart: the piecewise quadratic map that inserts the handle of the chart along the descending and ascending coordinates across a regular level (Milnor, Morse Theory, Section 3; Hatcher, Algebraic Topology, the index-lambda handle). -/
def ManifoldMorse.SignedMorseChart.attachingHandleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates,
      M)
    where
  toFun z := c.splitChart.symm (MorseHandle.modelMap ρ z)
  continuous_toFun :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
      (MorseHandle.continuous_modelMap ρ)
      (fun z => hblock (MorseHandle.modelMap_mem_product hρ z))

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (c.attachingHandleMap ρ hρ hblock) := by
  intro z w h
  apply MorseHandle.modelMap_injective hρ
  exact
    c.splitChart.toOpenPartialHomeomorph.symm.injOn
      (hblock (MorseHandle.modelMap_mem_product hρ z))
      (hblock (MorseHandle.modelMap_mem_product hρ w)) h

attribute [local instance 100] Classical.propDecidable in
/-- The attaching handle map is a closed embedding: the inserted handle sits cleanly in the manifold, the geometric core of the handle-attachment theorem (Milnor, Morse Theory, Section 3). -/
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) [T2Space M] (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Topology.IsClosedEmbedding (c.attachingHandleMap ρ hρ hblock) :=
  (c.attachingHandleMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.attachingHandleMap_injective ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_quadratic {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) =
      f x +
        (-‖(MorseHandle.modelMap ρ z).1‖ ^ 2 + ‖(MorseHandle.modelMap ρ z).2‖ ^ 2) := by
  change f (c.splitChart.symm (MorseHandle.modelMap ρ z)) = _
  rw [c.splitChart_inverse_equation (hblock (MorseHandle.modelMap_mem_product hρ z))]
  ring

attribute [local instance 100] Classical.propDecidable in
/-- Membership characterization: the image of the attaching handle map is exactly the set where the Morse function has dropped below the level - the sublevel-set change caused by passing the critical point. -/
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_lower_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) ≤ f x - ρ ^ 2 ↔ ‖(z.1 : c.NegativeCoordinates)‖ = 1 := by
  rw [c.attachingHandleMap_quadratic, sub_eq_add_neg, add_le_add_iff_left]
  exact MorseHandle.modelMap_lower_iff hρ z

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) ≤ f x + ρ ^ 2 := by
  rw [c.attachingHandleMap_quadratic]
  exact add_le_add le_rfl (MorseHandle.modelMap_upper hρ z)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.range_attachingHandleMap_mem_nhds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Set.range (c.attachingHandleMap ρ hρ hblock) ∈ 𝓝 p := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hnhds :=
    e.symm.image_mem_nhds hzero
      (MorseHandle.range_modelMap_mem_nhds_zero (N := c.NegativeCoordinates) (P :=
        c.PositiveCoordinates) hρ)
  rw [hinv] at hnhds
  apply Filter.mem_of_superset hnhds
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact ⟨z, rfl⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_interior_range_attachingHandleMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    p ∈ interior (Set.range (c.attachingHandleMap ρ hρ hblock)) :=
  mem_interior_iff_mem_nhds.mpr (c.range_attachingHandleMap_mem_nhds ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_range_attachingHandleMap_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ Set.range (c.attachingHandleMap ρ hρ hblock) ↔
      c.splitChart y ∈ Set.range (MorseHandle.modelMap ρ) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    exact
      (c.splitChart.toOpenPartialHomeomorph.right_inv
          (hblock (MorseHandle.modelMap_mem_product hρ z))).symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change c.splitChart.symm (MorseHandle.modelMap ρ z) = y
    rw [hz]
    exact c.splitChart.toOpenPartialHomeomorph.left_inv hy

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_range_attachingHandleMap_iff_inequalities
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ Set.range (c.attachingHandleMap ρ hρ hblock) ↔
      ‖(c.splitChart y).2‖ ≤ ρ ∧ f p - ρ ^ 2 ≤ f y := by
  rw [c.mem_range_attachingHandleMap_iff ρ hρ hblock hy,
    MorseHandle.mem_range_modelMap_iff hρ]
  apply and_congr_right
  intro _
  rw [c.splitChart_equation hy]
  constructor <;> intro h <;> linarith

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_attachingUnion_iff_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ {z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) ↔
      c.splitChart y ∈
        {z | MorseHandle.quadratic z ≤ -(ρ ^ 2)} ∪
          Set.range (MorseHandle.modelMap ρ) := by
  change
    (f y ≤ f p - ρ ^ 2 ∨ y ∈ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      (MorseHandle.quadratic (c.splitChart y) ≤ -(ρ ^ 2) ∨
        c.splitChart y ∈ Set.range (MorseHandle.modelMap ρ))
  rw [c.mem_range_attachingHandleMap_iff ρ hρ hblock hy]
  apply or_congr_left
  rw [c.splitChart_equation hy]
  unfold MorseHandle.quadratic
  constructor <;> intro h <;> linarith

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_interior_attachingUnion_of_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source)
    (hi :
      c.splitChart y ∈
        interior
          ({z | MorseHandle.quadratic z ≤ -(ρ ^ 2)} ∪
            Set.range (MorseHandle.modelMap ρ))) :
    y ∈ interior ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hp :=
    (c.splitChart.toOpenPartialHomeomorph.continuousAt hy).preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hi)
  apply Filter.mem_of_superset (Filter.inter_mem (c.splitChart.open_source.mem_nhds hy) hp)
  intro z hz
  exact (c.mem_attachingUnion_iff_model ρ hρ hblock hz.1).mpr hz.2

/-- The attachment region of a Morse handle: the annular part of the boundary where the handle is glued, complementary to the disk data. -/
def MorseHandle.attachmentRegion {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) : Set (N × P) :=
  {z | quadratic z ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ)

theorem MorseHandle.continuous_quadratic {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Continuous (quadratic (N := N) (P := P)) := by
  unfold quadratic
  fun_prop

theorem MorseHandle.isClosed_attachmentRegion {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) :
    IsClosed (attachmentRegion (N := N) (P := P) ρ) := by
  have heq :
    attachmentRegion (N := N) (P := P) ρ = {z | quadratic z ≤ -(ρ ^ 2)} ∪ {z | ‖z.2‖ ≤ ρ} := by
    ext z
    exact mem_lower_union_handle_iff hρ z
  rw [heq]
  exact
    (isClosed_le continuous_quadratic continuous_const).union
      (isClosed_le continuous_snd.norm continuous_const)

theorem MorseHandle.notMem_interior_attachmentRegion_of_bounds {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ}
    (hρ : 0 < ρ) (z : N × P) (hq : -(ρ ^ 2) ≤ quadratic z) (hv : ρ ≤ ‖z.2‖) :
    z ∉ interior (attachmentRegion ρ) := by
  intro hi
  have hpath : ContinuousAt (fun r : ℝ => (z.1, r • z.2)) 1 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, (z.1, r • z.2) ∈ attachmentRegion ρ := by
    apply hpath.preimage_mem_nhds
    simpa only [one_smul, Prod.eta] using mem_interior_iff_mem_nhds.mp hi
  obtain ⟨r, hr, hmem⟩ := hnear.exists_gt
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hvpos : 0 < ‖z.2‖ := hρ.trans_le hv
  have hnorm : ‖r • z.2‖ = r * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have hnormlt : ‖z.2‖ < ‖r • z.2‖ := by
    rw [hnorm]
    nlinarith
  have hquadlt : quadratic z < quadratic (z.1, r • z.2) := by
    unfold quadratic
    nlinarith [norm_nonneg (r • z.2), norm_nonneg z.2]
  rcases (mem_lower_union_handle_iff hρ (z.1, r • z.2)).mp hmem with h | h
  · exact (not_lt_of_ge h) (hq.trans_lt hquadlt)
  · exact (not_lt_of_ge h) (hv.trans_lt hnormlt)

theorem MorseHandle.mem_interior_attachmentRegion_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ interior (attachmentRegion ρ) ↔ quadratic z < -(ρ ^ 2) ∨ ‖z.2‖ < ρ := by
  constructor
  · intro hi
    by_cases hq : quadratic z < -(ρ ^ 2)
    · exact Or.inl hq
    by_cases hv : ‖z.2‖ < ρ
    · exact Or.inr hv
    exact
      (notMem_interior_attachmentRegion_of_bounds hρ z (le_of_not_gt hq) (le_of_not_gt hv)
          hi).elim
  · rintro (hq | hv)
    · apply
        interior_maximal (t := {w | quadratic w < -(ρ ^ 2)}) _
          (isOpen_lt continuous_quadratic continuous_const) hq
      intro w hw
      exact (mem_lower_union_handle_iff hρ w).mpr (Or.inl hw.le)
    · apply
        interior_maximal (t := {w : N × P | ‖w.2‖ < ρ}) _
          (isOpen_lt continuous_snd.norm continuous_const) hv
      intro w hw
      exact (mem_lower_union_handle_iff hρ w).mpr (Or.inr hw.le)

theorem MorseHandle.mem_frontier_attachmentRegion_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ frontier (attachmentRegion ρ) ↔
      (quadratic z = -(ρ ^ 2) ∧ ρ ≤ ‖z.2‖) ∨ (‖z.2‖ = ρ ∧ -(ρ ^ 2) ≤ quadratic z) := by
  rw [frontier, (isClosed_attachmentRegion hρ).closure_eq]
  change (z ∈ attachmentRegion ρ ∧ z ∉ interior (attachmentRegion ρ)) ↔ _
  rw [mem_interior_attachmentRegion_iff hρ]
  rw [show z ∈ attachmentRegion ρ ↔ quadratic z ≤ -(ρ ^ 2) ∨ ‖z.2‖ ≤ ρ from
      mem_lower_union_handle_iff hρ z]
  constructor
  · rintro ⟨hmem, hnot⟩
    have hq : -(ρ ^ 2) ≤ quadratic z := le_of_not_gt (fun h => hnot (Or.inl h))
    have hv : ρ ≤ ‖z.2‖ := le_of_not_gt (fun h => hnot (Or.inr h))
    rcases hmem with h | h
    · exact Or.inl ⟨le_antisymm h hq, hv⟩
    · exact Or.inr ⟨le_antisymm h hv, hq⟩
  · rintro (⟨hq, hv⟩ | ⟨hv, hq⟩)
    · refine ⟨Or.inl hq.le, ?_⟩
      rintro (h | h)
      · exact hq.not_lt h
      · exact (not_lt_of_ge hv) h
    · refine ⟨Or.inr hv.le, ?_⟩
      rintro (h | h)
      · exact (not_lt_of_ge hq) h
      · exact hv.not_lt h

theorem MorseHandle.modelMap_mem_frontier_attachmentRegion_iff {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ}
    (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    modelMap ρ z ∈ frontier (attachmentRegion ρ) ↔ ‖(z.2 : P)‖ = 1 := by
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have hnorm : ‖(modelMap ρ z).2‖ = ρ * ‖(z.2 : P)‖ := by
    change ‖ρ • (z.2 : P)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  rw [mem_frontier_attachmentRegion_iff hρ]
  constructor
  · intro hz
    have hlo : ρ ≤ ‖(modelMap ρ z).2‖ := by
      rcases hz with hz | hz
      · exact hz.2
      · exact hz.1.ge
    rw [hnorm] at hlo
    nlinarith
  · intro hz
    refine Or.inr ⟨?_, ?_⟩
    · rw [hnorm, hz, mul_one]
    · exact ((mem_range_modelMap_iff hρ (modelMap ρ z)).mp ⟨z, rfl⟩).2

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_interior_attachingUnion_iff_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ interior ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      c.splitChart y ∈ interior (MorseHandle.attachmentRegion ρ) := by
  constructor
  · intro hi
    apply mem_interior_iff_mem_nhds.mpr
    have ht : c.splitChart y ∈ c.splitChart.target := c.splitChart.map_source' hy
    have hc : ContinuousAt c.splitChart.symm (c.splitChart y) :=
      c.splitChart.toOpenPartialHomeomorph.symm.continuousAt ht
    have hleft : c.splitChart.symm (c.splitChart y) = y := c.splitChart.left_inv' hy
    have hnear :
      c.splitChart.symm ⁻¹'
          interior ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ∈
        𝓝 (c.splitChart y) :=
      hc.preimage_mem_nhds
        (by
          rw [hleft]
          exact isOpen_interior.mem_nhds hi)
    apply Filter.mem_of_superset (Filter.inter_mem (c.splitChart.open_target.mem_nhds ht) hnear)
    intro z hz
    have hmem :=
      (c.mem_attachingUnion_iff_model ρ hρ hblock (c.splitChart.map_target' hz.1)).mp
        (interior_subset hz.2)
    rwa [c.splitChart.right_inv' hz.1] at hmem
  · exact c.mem_interior_attachingUnion_of_model ρ hρ hblock hy

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.mem_frontier_attachingUnion_iff_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ frontier ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      c.splitChart y ∈ frontier (MorseHandle.attachmentRegion ρ) := by
  have hA : IsClosed ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :=
    (isClosed_le hf continuous_const).union
      (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range
  rw [frontier, frontier, hA.closure_eq,
    (MorseHandle.isClosed_attachmentRegion hρ).closure_eq]
  exact
    and_congr (c.mem_attachingUnion_iff_model ρ hρ hblock hy)
      (not_congr (c.mem_interior_attachingUnion_iff_model ρ hρ hblock hy))

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_mem_frontier_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates) :
    c.attachingHandleMap ρ hρ hblock z ∈
        frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      ‖(z.2 : c.PositiveCoordinates)‖ = 1 := by
  have ht := hblock (MorseHandle.modelMap_mem_product hρ z)
  have hy : c.attachingHandleMap ρ hρ hblock z ∈ c.splitChart.source :=
    c.splitChart.map_target' ht
  rw [c.mem_frontier_attachingUnion_iff_model hf ρ hρ hblock hy]
  have heq : c.splitChart (c.attachingHandleMap ρ hρ hblock z) = MorseHandle.modelMap ρ z :=
    c.splitChart.right_inv' ht
  rw [heq, MorseHandle.modelMap_mem_frontier_attachmentRegion_iff hρ]

def ClosedAttachment.Rel {K M : Type*} [TopologicalSpace K] [TopologicalSpace M] (A : Set M)
    (B : Set K) (h : C(K, M)) : A ⊕ K → A ⊕ K → Prop
  | .inl a, .inr k => k ∈ B ∧ (a : M) = h k
  | _, _ => False

abbrev ClosedAttachment.Space {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) :=
  Quot (ClosedAttachment.Rel A B h)

def ClosedAttachment.sumMap {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (h : C(K, M)) : A ⊕ K → ↥(A ∪ Set.range h)
  | .inl a => ⟨a, Or.inl a.2⟩
  | .inr k => ⟨h k, Or.inr ⟨k, rfl⟩⟩

theorem ClosedAttachment.continuous_sumMap {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (h : C(K, M)) : Continuous (sumMap A h) :=
  continuous_sum_dom.mpr ⟨continuous_subtype_val.subtype_mk _, h.continuous.subtype_mk _⟩

theorem ClosedAttachment.sumMap_respects {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) (x y : A ⊕ K)
    (hxy : ClosedAttachment.Rel A B h x y) : sumMap A h x = sumMap A h y := by
  cases x with
  | inl a =>
    cases y with
    | inl a' => exact hxy.elim
    | inr k => exact Subtype.ext hxy.2
  | inr k => cases y <;> exact hxy.elim

def ClosedAttachment.quotientMap {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) : Space A B h → ↥(A ∪ Set.range h) :=
  Quot.lift (sumMap A h) (sumMap_respects A B h)

theorem ClosedAttachment.continuous_quotientMap {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) : Continuous (quotientMap A B h) :=
  continuous_quot_lift (sumMap_respects A B h) (ClosedAttachment.continuous_sumMap A h)

theorem ClosedAttachment.quotientMap_injective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) : Function.Injective (quotientMap A B h) := by
  intro q r
  induction q using Quot.inductionOn with
  | _ x =>
    induction r using Quot.inductionOn with
    | _ y =>
      intro heq
      have heq' := congrArg Subtype.val heq
      cases x with
      | inl a =>
        cases y with
        | inl a' =>
          have haa : a = a' := Subtype.ext heq'
          subst a'
          rfl
        | inr k =>
          change (a : M) = h k at heq'
          have hk : h k ∈ A := by rw [← heq']; exact a.2
          exact Quot.sound ⟨(hface k).mp hk, heq'⟩
      | inr k =>
        cases y with
        | inl a =>
          change h k = (a : M) at heq'
          have hk : h k ∈ A := by rw [heq']; exact a.2
          exact
            (Quot.sound (r := ClosedAttachment.Rel A B h) (a := .inl a) (b := .inr k)
                ⟨(hface k).mp hk, heq'.symm⟩).symm
        | inr k' =>
          have hkk : k = k' := hinj heq'
          subst k'
          rfl

theorem ClosedAttachment.quotientMap_surjective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) :
    Function.Surjective (quotientMap A B h) := by
  rintro ⟨x, hx | ⟨k, rfl⟩⟩
  · exact ⟨Quot.mk _ (.inl ⟨x, hx⟩), rfl⟩
  · exact ⟨Quot.mk _ (.inr k), rfl⟩

def ClosedAttachment.unionHomeomorph {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) [CompactSpace K] [T2Space M] (hA : IsCompact A)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) :
    Space A B h ≃ₜ ↥(A ∪ Set.range h) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  exact
    Continuous.homeoOfEquivCompactToT2 (f :=
      Equiv.ofBijective (quotientMap A B h)
        ⟨quotientMap_injective A B h hinj hface, quotientMap_surjective A B h⟩)
      (continuous_quotientMap A B h)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.attachingHandleMap_boundary_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      MorseHandle.UnitDisk c.NegativeCoordinates ×
        MorseHandle.UnitDisk c.PositiveCoordinates)
    (hz : ‖(z.1 : c.NegativeCoordinates)‖ = 1) :
    f (c.attachingHandleMap ρ hρ hblock z) = f x - ρ ^ 2 := by
  rw [c.attachingHandleMap_quadratic, MorseHandle.modelMap_height hρ z, hz]
  ring

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.SignedMorseChart.attachingBoundaryMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Metric.sphere (0 : c.NegativeCoordinates) 1 ×
        MorseHandle.UnitDisk c.PositiveCoordinates,
      { y : M // f y = f x - ρ ^ 2 })
    where
  toFun
    z :=
    ⟨c.attachingHandleMap ρ hρ hblock (⟨z.1, Metric.sphere_subset_closedBall z.1.2⟩, z.2),
      c.attachingHandleMap_boundary_height ρ hρ hblock _
        (by simpa only [Metric.mem_sphere, dist_zero_right] using z.1.2)⟩
  continuous_toFun :=
    ((c.attachingHandleMap ρ hρ hblock).continuous.comp
          (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
            continuous_snd)).subtype_mk
      _

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.SignedMorseChart.attachingHandleUnionHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) [T2Space M] [CompactSpace M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    ClosedAttachment.Space {y : M | f y ≤ f x - ρ ^ 2}
        {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₜ
      ↥({y : M | f y ≤ f x - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :=
  ClosedAttachment.unionHomeomorph _ _ _ (isClosed_le hf continuous_const).isCompact
    (c.attachingHandleMap_injective ρ hρ hblock)
    (fun z => c.attachingHandleMap_lower_iff ρ hρ hblock z)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.attachingHandleUnion_subset_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    {y : M | f y ≤ f x - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) ⊆
      {y : M | f y ≤ f x + ρ ^ 2} := by
  rintro y (hy | ⟨z, rfl⟩)
  · change f y ≤ f x + ρ ^ 2
    change f y ≤ f x - ρ ^ 2 at hy
    nlinarith [sq_nonneg ρ]
  · exact c.attachingHandleMap_upper ρ hρ hblock z

def RadialExtension.direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    (hx : x ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩

attribute [local instance 100] Classical.propDecidable in
def RadialExtension.radial {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) : F :=
  if hx : x = 0 then 0 else ‖x‖ • (f (direction x hx) : F)

@[simp]
theorem RadialExtension.radial_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) : radial f 0 = 0 := by simp [radial]

theorem RadialExtension.radial_of_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) {x : E} (hx : x ≠ 0) :
    radial f x = ‖x‖ • (f (direction x hx) : F) := by simp [radial, hx]

@[simp]
theorem RadialExtension.norm_radial {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) : ‖radial f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radial_of_ne_zero f hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
    mem_sphere_zero_iff_norm.mp (f (direction x hx)).property, mul_one]

@[simp]
theorem RadialExtension.radial_eq_zero_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) : radial f x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_radial, norm_eq_zero]

theorem RadialExtension.direction_radial {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) {x : E} (hx : x ≠ 0) :
    direction (radial f x) (fun h => hx ((radial_eq_zero_iff f x).mp h)) = f (direction x hx) := by
  apply Subtype.ext
  change ‖radial f x‖⁻¹ • radial f x = (f (direction x hx) : F)
  rw [norm_radial, radial_of_ne_zero f hx, inv_smul_smul₀ (norm_ne_zero_iff.mpr hx)]

@[simp]
theorem RadialExtension.radial_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : radial id x = x := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radial_of_ne_zero id hx]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x

theorem RadialExtension.radial_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Metric.sphere (0 : F) 1 → Metric.sphere (0 : G) 1)
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) :
    radial g (radial f x) = radial (g ∘ f) x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hy : radial f x ≠ 0 := fun h => hx ((radial_eq_zero_iff f x).mp h)
  rw [radial_of_ne_zero g hy, norm_radial, direction_radial f hx, radial_of_ne_zero (g ∘ f) hx]
  rfl

@[simp]
theorem RadialExtension.radial_on_sphere {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : Metric.sphere (0 : E) 1) :
    radial f x = (f x : F) := by
  have hn : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hx : (x : E) ≠ 0 := by
    intro h
    simp [h] at hn
  have hd : direction (x : E) hx = x := by
    apply Subtype.ext
    simp [direction, hn]
  rw [radial_of_ne_zero f hx, hn, hd, one_smul]

theorem RadialExtension.continuous_radial {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1} (hf : Continuous f) :
    Continuous (radial f) := by
  have haway : ContinuousOn (radial f) ({0}ᶜ : Set E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq :
      ({0}ᶜ : Set E).domRestrict (radial f) = fun (x : ({0}ᶜ : Set E)) =>
        ‖(x : E)‖ • (f ((homeomorphUnitSphereProd E x).1) : F) := by
      funext x
      rw [Set.domRestrict_apply, radial_of_ne_zero f x.property]
      have hd : direction (x : E) x.property = (homeomorphUnitSphereProd E x).1 := by
        apply Subtype.ext
        simp [direction]
      rw [hd]
    rw [heq]
    exact
      continuous_subtype_val.norm.smul
        (continuous_subtype_val.comp (hf.comp (homeomorphUnitSphereProd E).continuous.fst))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simpa only [radial_zero, dist_zero_right, norm_radial] using hy
  exact (haway x hx).continuousAt (isOpen_compl_singleton.mem_nhds hx)

def RadialExtension.homeomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1) : E ≃ₜ F
    where
  toFun := radial e
  invFun := radial e.symm
  left_inv
    x := by
    rw [radial_comp]
    have h : (e.symm : Metric.sphere (0 : F) 1 → Metric.sphere (0 : E) 1) ∘ e = id := by
      funext y
      exact e.symm_apply_apply y
    rw [h, radial_id]
  right_inv
    x := by
    rw [radial_comp]
    have h : (e : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) ∘ e.symm = id := by
      funext y
      exact e.apply_symm_apply y
    rw [h, radial_id]
  continuous_toFun := continuous_radial e.continuous
  continuous_invFun := continuous_radial e.symm.continuous

def RadialExtension.closedBallHomeomorph {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1) :
    Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : F) 1 :=
  (homeomorph e).sets
    (by
      ext x
      simp [homeomorph])

@[simp]
theorem RadialExtension.closedBallHomeomorph_on_sphere {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1) (x : Metric.sphere (0 : E) 1) :
    closedBallHomeomorph e ⟨x, Metric.sphere_subset_closedBall x.property⟩ =
      ⟨e x, Metric.sphere_subset_closedBall (e x).property⟩ := by
  apply Subtype.ext
  exact radial_on_sphere e x

abbrev PuncturedHandle.Radius :=
  Set.Ioc (0 : ℝ) 1

abbrev PuncturedHandle.UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

abbrev PuncturedHandle.PuncturedBall (E : Type*) [NormedAddCommGroup E] :=
  { x : E // x ≠ 0 ∧ ‖x‖ ≤ 1 }

def PuncturedHandle.point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : UnitSphere E) (r : Radius) : PuncturedBall E := by
  have hn : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hnorm : ‖(r : ℝ) • (u : E)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1, hn, mul_one]
  refine ⟨(r : ℝ) • (u : E), ?_, ?_⟩
  · exact norm_pos_iff.mp (by rw [hnorm]; exact r.property.1)
  · rw [hnorm]
    exact r.property.2

theorem PuncturedHandle.norm_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : UnitSphere E) (r : Radius) : ‖(point u r : E)‖ = (r : ℝ) := by
  change ‖(r : ℝ) • (u : E)‖ = (r : ℝ)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1,
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

def PuncturedHandle.polar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PuncturedBall E ≃ₜ (UnitSphere E × Radius)
    where
  toFun
    x :=
    (RadialExtension.direction (x : E) x.property.1,
      ⟨‖(x : E)‖, norm_pos_iff.mpr x.property.1, x.property.2⟩)
  invFun p := point p.1 p.2
  left_inv := by
    intro x
    apply Subtype.ext
    change ‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr x.property.1) (x : E)
  right_inv := by
    rintro ⟨u, r⟩
    apply Prod.ext
    · apply Subtype.ext
      change ‖(point u r : E)‖⁻¹ • ((r : ℝ) • (u : E)) = (u : E)
      rw [norm_point, inv_smul_smul₀ r.property.1.ne']
    · apply Subtype.ext
      exact norm_point u r
  continuous_toFun := by
    have hdir :
      Continuous
        (fun x : PuncturedBall E => RadialExtension.direction (x : E) x.property.1) :=
      ((continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property.1)).smul
            continuous_subtype_val).subtype_mk
        _
    exact hdir.prodMk (continuous_subtype_val.norm.subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp continuous_fst)).subtype_mk
      _

def PuncturedHandle.exchange (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (UnitSphere E × PuncturedBall F) ≃ₜ (PuncturedBall E × UnitSphere F) :=
  ((Homeomorph.refl (UnitSphere E)).prodCongr (polar F)).trans
    (((Homeomorph.refl (UnitSphere E)).prodCongr
          (Homeomorph.prodComm (UnitSphere F) Radius)).trans
      ((Homeomorph.prodAssoc (UnitSphere E) Radius (UnitSphere F)).symm.trans
        ((polar E).symm.prodCongr (Homeomorph.refl (UnitSphere F)))))

theorem PuncturedHandle.exchange_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (u : UnitSphere E)
    (v : PuncturedBall F) :
    exchange E F (u, v) =
      (point u ⟨‖(v : F)‖, norm_pos_iff.mpr v.property.1, v.property.2⟩,
        RadialExtension.direction (v : F) v.property.1) :=
  rfl

def PuncturedHandle.boundaryPoint {E : Type*} [NormedAddCommGroup E] (u : UnitSphere E) :
    PuncturedBall E :=
  ⟨u, Metric.ne_of_mem_sphere u.property one_ne_zero, (mem_sphere_zero_iff_norm.mp u.property).le⟩

theorem PuncturedHandle.exchange_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (u : UnitSphere E)
    (v : UnitSphere F) : exchange E F (u, boundaryPoint v) = (boundaryPoint u, v) := by
  rw [exchange_apply]
  have hv : ‖(v : F)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  apply Prod.ext
  · apply Subtype.ext
    change ‖(v : F)‖ • (u : E) = (u : E)
    rw [hv, one_smul]
  · apply Subtype.ext
    change ‖(v : F)‖⁻¹ • (v : F) = (v : F)
    rw [hv, inv_one, one_smul]

abbrev PuncturedHandle.UnitBall (E : Type*) [NormedAddCommGroup E] :=
  { x : E // ‖x‖ ≤ 1 }

def PuncturedHandle.ballZero {E : Type*} [NormedAddCommGroup E] : UnitBall E :=
  ⟨0, by simp⟩

def PuncturedHandle.sphereToBall {E : Type*} [NormedAddCommGroup E] (u : UnitSphere E) :
    UnitBall E :=
  ⟨u, (mem_sphere_zero_iff_norm.mp u.property).le⟩

def PuncturedHandle.puncturedToBall {E : Type*} [NormedAddCommGroup E]
    (u : PuncturedBall E) : UnitBall E :=
  ⟨u, u.property.2⟩

theorem PuncturedHandle.puncturedToBall_injective {E : Type*} [NormedAddCommGroup E] :
    Function.Injective (puncturedToBall (E := E)) := fun _ _ h =>
  Subtype.ext (congrArg (fun z : UnitBall E => (z : E)) h)

def PuncturedHandle.oldBoundary {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : UnitSphere E × UnitSphere F) : UnitSphere E × UnitBall F :=
  (q.1, sphereToBall q.2)

def PuncturedHandle.newBoundary {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : UnitSphere E × UnitSphere F) : UnitBall E × UnitSphere F :=
  (sphereToBall q.1, q.2)

def PuncturedHandle.oldPunctured {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (p : UnitSphere E × PuncturedBall F) : UnitSphere E × UnitBall F :=
  (p.1, puncturedToBall p.2)

def PuncturedHandle.newPunctured {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (p : PuncturedBall E × UnitSphere F) : UnitBall E × UnitSphere F :=
  (puncturedToBall p.1, p.2)

theorem PuncturedHandle.oldPunctured_injective {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] : Function.Injective (oldPunctured (E := E) (F := F)) := by
  intro p q h
  exact
    Prod.ext (congrArg (fun z : UnitSphere E × UnitBall F => z.1) h)
      (puncturedToBall_injective (congrArg (fun z : UnitSphere E × UnitBall F => z.2) h))

theorem PuncturedHandle.newPunctured_injective {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] : Function.Injective (newPunctured (E := E) (F := F)) := by
  intro p q h
  exact
    Prod.ext (puncturedToBall_injective (congrArg (fun z : UnitBall E × UnitSphere F => z.1) h))
      (congrArg (fun z : UnitBall E × UnitSphere F => z.2) h)

def PuncturedHandle.oldPuncturedDomain (E F : Type*) [NormedAddCommGroup E]
    [NormedAddCommGroup F] :
    (UnitSphere E × PuncturedBall F) ≃ₜ { p : UnitSphere E × UnitBall F // (p.2 : F) ≠ 0 }
    where
  toFun p := ⟨oldPunctured p, p.2.property.1⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property, p.val.2.property⟩)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change
      Continuous
        (fun p : UnitSphere E × PuncturedBall F =>
          (p.1, (⟨(p.2 : F), p.2.property.2⟩ : UnitBall F)))
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _

def PuncturedHandle.newPuncturedDomain (E F : Type*) [NormedAddCommGroup E]
    [NormedAddCommGroup F] :
    (PuncturedBall E × UnitSphere F) ≃ₜ { p : UnitBall E × UnitSphere F // (p.1 : E) ≠ 0 }
    where
  toFun p := ⟨newPunctured p, p.1.property.1⟩
  invFun p := (⟨p.val.1, p.property, p.val.1.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change
      Continuous
        (fun p : PuncturedBall E × UnitSphere F =>
          ((⟨(p.1 : E), p.1.property.2⟩ : UnitBall E), p.2))
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  continuous_invFun := by
    apply Continuous.prodMk
    · exact
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    · exact continuous_snd.comp continuous_subtype_val

theorem PuncturedHandle.oldPunctured_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (q : UnitSphere E × UnitSphere F) :
    oldPunctured (q.1, boundaryPoint q.2) = oldBoundary q :=
  rfl

theorem PuncturedHandle.newPunctured_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (q : UnitSphere E × UnitSphere F) :
    newPunctured (boundaryPoint q.1, q.2) = newBoundary q :=
  rfl

def ClosedCover.glue {X Y : Type*} {A B : Set X} (hcover : A ∪ B = Set.univ) (f : A → Y)
    (g : B → Y) : X → Y := by
  classical
    exact fun x =>
    if hx : x ∈ A then f ⟨x, hx⟩
    else g ⟨x, (show x ∈ A ∪ B by rw [hcover]; trivial).resolve_left hx⟩

theorem ClosedCover.glue_left {X Y : Type*} {A B : Set X} (hcover : A ∪ B = Set.univ)
    (f : A → Y) (g : B → Y) (x : A) : glue hcover f g x = f x := by
  classical simp only [glue, dif_pos x.property]

theorem ClosedCover.glue_right {X Y : Type*} {A B : Set X} (hcover : A ∪ B = Set.univ)
    (f : A → Y) (g : B → Y) (hagree : ∀ a : A, ∀ b : B, (a : X) = b → f a = g b) (x : B) :
    glue hcover f g x = g x := by
  classical
  by_cases hx : (x : X) ∈ A
  · rw [glue, dif_pos hx]
    exact hagree ⟨x, hx⟩ x rfl
  · rw [glue, dif_neg hx]

theorem ClosedCover.continuous_glue {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hcover : A ∪ B = Set.univ) (hA : IsClosed A) (hB : IsClosed B) (f : A → Y)
    (g : B → Y) (hf : Continuous f) (hg : Continuous g)
    (hagree : ∀ a : A, ∀ b : B, (a : X) = b → f a = g b) : Continuous (glue hcover f g) := by
  have hleft : ContinuousOn (glue hcover f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (glue hcover f g) = f := funext (fun x => glue_left hcover f g x)
    rw [heq]
    exact hf
  have hright : ContinuousOn (glue hcover f g) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : B.domRestrict (glue hcover f g) = g :=
      funext (fun x => glue_right hcover f g hagree x)
    rw [heq]
    exact hg
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hleft.union_of_isClosed hright hA hB

def ClosedCover.homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {C D : Set Y} (hcover : A ∪ B = Set.univ) (hcover' : C ∪ D = Set.univ)
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) (hD : IsClosed D) (e : A ≃ₜ C)
    (f : B ≃ₜ D) (hcross : ∀ a : A, ∀ b : B, ((e a : C) : Y) = f b ↔ (a : X) = b) : X ≃ₜ Y := by
  let e₀ : A → Y := fun x => e x
  let f₀ : B → Y := fun x => f x
  let e₁ : C → X := fun y => e.symm y
  let f₁ : D → X := fun y => f.symm y
  have hagree : ∀ a : A, ∀ b : B, (a : X) = b → e₀ a = f₀ b := fun a b h => (hcross a b).mpr h
  have hagreeInv : ∀ c : C, ∀ d : D, (c : Y) = d → e₁ c = f₁ d := by
    intro c d h
    apply (hcross (e.symm c) (f.symm d)).mp
    simpa only [e.apply_symm_apply, f.apply_symm_apply] using h
  let F := glue hcover e₀ f₀
  let G := glue hcover' e₁ f₁
  have hleft : Function.LeftInverse G F := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; trivial
    rcases hx with hx | hx
    · calc
        G (F x) = G (e₀ ⟨x, hx⟩) := congrArg G (glue_left hcover e₀ f₀ ⟨x, hx⟩)
        _ = e₁ (e ⟨x, hx⟩) := (glue_left hcover' e₁ f₁ (e ⟨x, hx⟩))
        _ = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    · calc
        G (F x) = G (f₀ ⟨x, hx⟩) := congrArg G (glue_right hcover e₀ f₀ hagree ⟨x, hx⟩)
        _ = f₁ (f ⟨x, hx⟩) := (glue_right hcover' e₁ f₁ hagreeInv (f ⟨x, hx⟩))
        _ = x := congrArg Subtype.val (f.symm_apply_apply ⟨x, hx⟩)
  have hright : Function.RightInverse G F := by
    intro y
    have hy : y ∈ C ∪ D := by rw [hcover']; trivial
    rcases hy with hy | hy
    · calc
        F (G y) = F (e₁ ⟨y, hy⟩) := congrArg F (glue_left hcover' e₁ f₁ ⟨y, hy⟩)
        _ = e₀ (e.symm ⟨y, hy⟩) := (glue_left hcover e₀ f₀ (e.symm ⟨y, hy⟩))
        _ = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    · calc
        F (G y) = F (f₁ ⟨y, hy⟩) := congrArg F (glue_right hcover' e₁ f₁ hagreeInv ⟨y, hy⟩)
        _ = f₀ (f.symm ⟨y, hy⟩) := (glue_right hcover e₀ f₀ hagree (f.symm ⟨y, hy⟩))
        _ = y := congrArg Subtype.val (f.apply_symm_apply ⟨y, hy⟩)
  exact
    { toEquiv := { toFun := F, invFun := G, left_inv := hleft, right_inv := hright }
      continuous_toFun :=
        continuous_glue hcover hA hB e₀ f₀ (continuous_subtype_val.comp e.continuous)
          (continuous_subtype_val.comp f.continuous) hagree
      continuous_invFun :=
        continuous_glue hcover' hC hD e₁ f₁ (continuous_subtype_val.comp e.symm.continuous)
          (continuous_subtype_val.comp f.symm.continuous) hagreeInv }

def ClosedCover.homeomorphOfClosedPieces {R P Q X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace X] [TopologicalSpace Y]
    (r₀ : R → X) (r₁ : R → Y) (p₀ : P → X) (p₁ : Q → Y) (hr₀ : Topology.IsClosedEmbedding r₀)
    (hr₁ : Topology.IsClosedEmbedding r₁) (hp₀ : Topology.IsClosedEmbedding p₀)
    (hp₁ : Topology.IsClosedEmbedding p₁) (hcover₀ : Set.range r₀ ∪ Set.range p₀ = Set.univ)
    (hcover₁ : Set.range r₁ ∪ Set.range p₁ = Set.univ) (e : P ≃ₜ Q)
    (hincidence : ∀ r p, r₀ r = p₀ p ↔ r₁ r = p₁ (e p)) : X ≃ₜ Y := by
  let a₀ := hr₀.isEmbedding.toHomeomorph
  let a₁ := hr₁.isEmbedding.toHomeomorph
  let b₀ := hp₀.isEmbedding.toHomeomorph
  let b₁ := hp₁.isEmbedding.toHomeomorph
  let a : Set.range r₀ ≃ₜ Set.range r₁ := a₀.symm.trans a₁
  let b : Set.range p₀ ≃ₜ Set.range p₁ := b₀.symm.trans (e.trans b₁)
  apply
    homeomorph hcover₀ hcover₁ hr₀.isClosed_range hp₀.isClosed_range hr₁.isClosed_range
      hp₁.isClosed_range a b
  intro x y
  have hx : r₀ (a₀.symm x) = (x : X) := by exact congrArg Subtype.val (a₀.apply_symm_apply x)
  have hy : p₀ (b₀.symm y) = (y : X) := by exact congrArg Subtype.val (b₀.apply_symm_apply y)
  change r₁ (a₀.symm x) = p₁ (e (b₀.symm y)) ↔ (x : X) = (y : X)
  rw [← hincidence, hx, hy]

structure SurgeryBoundaryPair (E F R X Y : Type*) [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] where
  oldExterior : R → X
  newExterior : R → Y
  oldPiece : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitBall F → X
  newPiece : PuncturedHandle.UnitBall E × PuncturedHandle.UnitSphere F → Y
  oldExterior_closed : Topology.IsClosedEmbedding oldExterior
  newExterior_closed : Topology.IsClosedEmbedding newExterior
  oldPiece_closed : Topology.IsClosedEmbedding oldPiece
  newPiece_closed : Topology.IsClosedEmbedding newPiece
  old_cover : Set.range oldExterior ∪ Set.range oldPiece = Set.univ
  new_cover : Set.range newExterior ∪ Set.range newPiece = Set.univ
  boundary : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitSphere F → R
  old_overlap :
    ∀ r p, oldExterior r = oldPiece p ↔ ∃ q, r = boundary q ∧ p = PuncturedHandle.oldBoundary q
  new_overlap :
    ∀ r p, newExterior r = newPiece p ↔ ∃ q, r = boundary q ∧ p = PuncturedHandle.newBoundary q

def SurgeryBoundaryPair.attachingSphere {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) : C(PuncturedHandle.UnitSphere E, X) :=
  ⟨fun u => d.oldPiece (u, PuncturedHandle.ballZero),
    d.oldPiece_closed.continuous.comp (continuous_id.prodMk continuous_const)⟩

def SurgeryBoundaryPair.beltSphere {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) : C(PuncturedHandle.UnitSphere F, Y) :=
  ⟨fun v => d.newPiece (PuncturedHandle.ballZero, v),
    d.newPiece_closed.continuous.comp (continuous_const.prodMk continuous_id)⟩

abbrev SurgeryBoundaryPair.OldComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :=
  (Set.range d.attachingSphere)ᶜ

abbrev SurgeryBoundaryPair.NewComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :=
  (Set.range d.beltSphere)ᶜ

theorem SurgeryBoundaryPair.oldPiece_mem_core_iff {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y)
    (p : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitBall F) :
    d.oldPiece p ∈ Set.range d.attachingSphere ↔ (p.2 : F) = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have hp : (u, (PuncturedHandle.ballZero : PuncturedHandle.UnitBall F)) = p :=
      d.oldPiece_closed.injective hu
    exact
      (congrArg
          (fun z : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitBall F =>
            (z.2 : F))
          hp).symm
  · intro hp
    refine ⟨p.1, ?_⟩
    apply congrArg d.oldPiece
    exact Prod.ext rfl (Subtype.ext hp.symm)

theorem SurgeryBoundaryPair.newPiece_mem_belt_iff {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y)
    (p : PuncturedHandle.UnitBall E × PuncturedHandle.UnitSphere F) :
    d.newPiece p ∈ Set.range d.beltSphere ↔ (p.1 : E) = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hp : ((PuncturedHandle.ballZero : PuncturedHandle.UnitBall E), v) = p :=
      d.newPiece_closed.injective hv
    exact
      (congrArg
          (fun z : PuncturedHandle.UnitBall E × PuncturedHandle.UnitSphere F =>
            (z.1 : E))
          hp).symm
  · intro hp
    refine ⟨p.2, ?_⟩
    apply congrArg d.newPiece
    exact Prod.ext (Subtype.ext hp.symm) rfl

theorem SurgeryBoundaryPair.oldExterior_avoids {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) (r : R) : d.oldExterior r ∈ d.OldComplement := by
  rintro ⟨u, hu⟩
  obtain ⟨q, -, hq⟩ := (d.old_overlap r (u, PuncturedHandle.ballZero)).mp hu.symm
  have hz : (q.2 : F) = 0 :=
    (congrArg
        (fun z : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitBall F =>
          (z.2 : F))
        hq).symm
  exact (Metric.ne_of_mem_sphere q.2.property one_ne_zero) hz

theorem SurgeryBoundaryPair.newExterior_avoids {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) (r : R) : d.newExterior r ∈ d.NewComplement := by
  rintro ⟨v, hv⟩
  obtain ⟨q, -, hq⟩ := (d.new_overlap r (PuncturedHandle.ballZero, v)).mp hv.symm
  have hz : (q.1 : E) = 0 :=
    (congrArg
        (fun z : PuncturedHandle.UnitBall E × PuncturedHandle.UnitSphere F =>
          (z.1 : E))
        hq).symm
  exact (Metric.ne_of_mem_sphere q.1.property one_ne_zero) hz

theorem ClosedCover.isClosedEmbedding_codRestrict {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : Topology.IsClosedEmbedding f) {s : Set B}
    (hs : ∀ x, f x ∈ s) : Topology.IsClosedEmbedding (s.codRestrict f hs) :=
  ⟨hf.isEmbedding.codRestrict s hs, (hf.isClosedMap.codRestrict hs).isClosed_range⟩

def SurgeryBoundaryPair.oldExteriorMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) : R → d.OldComplement :=
  d.OldComplement.codRestrict d.oldExterior d.oldExterior_avoids

def SurgeryBoundaryPair.newExteriorMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) : R → d.NewComplement :=
  d.NewComplement.codRestrict d.newExterior d.newExterior_avoids

def SurgeryBoundaryPair.oldParameterComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :
    (PuncturedHandle.UnitSphere E × PuncturedHandle.PuncturedBall F) ≃ₜ
      (d.oldPiece ⁻¹' d.OldComplement) :=
  (PuncturedHandle.oldPuncturedDomain E F).trans
    (Homeomorph.setCongr
      (by
        ext p
        exact (not_congr (d.oldPiece_mem_core_iff p)).symm))

def SurgeryBoundaryPair.newParameterComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :
    (PuncturedHandle.PuncturedBall E × PuncturedHandle.UnitSphere F) ≃ₜ
      (d.newPiece ⁻¹' d.NewComplement) :=
  (PuncturedHandle.newPuncturedDomain E F).trans
    (Homeomorph.setCongr
      (by
        ext p
        exact (not_congr (d.newPiece_mem_belt_iff p)).symm))

def SurgeryBoundaryPair.oldPuncturedMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :
    PuncturedHandle.UnitSphere E × PuncturedHandle.PuncturedBall F →
      d.OldComplement :=
  d.OldComplement.restrictPreimage d.oldPiece ∘ d.oldParameterComplement

def SurgeryBoundaryPair.newPuncturedMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :
    PuncturedHandle.PuncturedBall E × PuncturedHandle.UnitSphere F →
      d.NewComplement :=
  d.NewComplement.restrictPreimage d.newPiece ∘ d.newParameterComplement

theorem SurgeryBoundaryPair.isClosedEmbedding_oldExteriorMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.oldExteriorMap :=
  ClosedCover.isClosedEmbedding_codRestrict d.oldExterior_closed d.oldExterior_avoids

theorem SurgeryBoundaryPair.isClosedEmbedding_newExteriorMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.newExteriorMap :=
  ClosedCover.isClosedEmbedding_codRestrict d.newExterior_closed d.newExterior_avoids

theorem SurgeryBoundaryPair.isClosedEmbedding_oldPuncturedMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.oldPuncturedMap :=
  (d.oldPiece_closed.restrictPreimage d.OldComplement).comp
    d.oldParameterComplement.isClosedEmbedding

theorem SurgeryBoundaryPair.isClosedEmbedding_newPuncturedMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.newPuncturedMap :=
  (d.newPiece_closed.restrictPreimage d.NewComplement).comp
    d.newParameterComplement.isClosedEmbedding

theorem SurgeryBoundaryPair.oldComplement_cover {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :
    Set.range d.oldExteriorMap ∪ Set.range d.oldPuncturedMap = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz : (z : X) ∈ Set.range d.oldExterior ∪ Set.range d.oldPiece := by
    rw [d.old_cover]
    trivial
  rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · have hpavoid : d.oldPiece p ∈ d.OldComplement := hp.symm ▸ z.property
    have hpne : (p.2 : F) ≠ 0 := fun h => hpavoid ((d.oldPiece_mem_core_iff p).mpr h)
    refine Or.inr ⟨(p.1, ⟨p.2, hpne, p.2.property⟩), Subtype.ext ?_⟩
    exact hp

theorem SurgeryBoundaryPair.newComplement_cover {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) :
    Set.range d.newExteriorMap ∪ Set.range d.newPuncturedMap = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz : (z : Y) ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by
    rw [d.new_cover]
    trivial
  rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · have hpavoid : d.newPiece p ∈ d.NewComplement := hp.symm ▸ z.property
    have hpne : (p.1 : E) ≠ 0 := fun h => hpavoid ((d.newPiece_mem_belt_iff p).mpr h)
    refine Or.inr ⟨(⟨p.1, hpne, p.1.property⟩, p.2), Subtype.ext ?_⟩
    exact hp

theorem SurgeryBoundaryPair.oldPunctured_overlap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) (r : R)
    (p : PuncturedHandle.UnitSphere E × PuncturedHandle.PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      ∃ q, r = d.boundary q ∧ p = (q.1, PuncturedHandle.boundaryPoint q.2) := by
  rw [Subtype.ext_iff]
  change d.oldExterior r = d.oldPiece (PuncturedHandle.oldPunctured p) ↔ _
  rw [d.old_overlap]
  constructor
  · rintro ⟨q, hr, hp⟩
    exact
      ⟨q, hr,
        PuncturedHandle.oldPunctured_injective
          (hp.trans (PuncturedHandle.oldPunctured_boundary q).symm)⟩
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, PuncturedHandle.oldPunctured_boundary q⟩

theorem SurgeryBoundaryPair.newPunctured_overlap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) (r : R)
    (p : PuncturedHandle.PuncturedBall E × PuncturedHandle.UnitSphere F) :
    d.newExteriorMap r = d.newPuncturedMap p ↔
      ∃ q, r = d.boundary q ∧ p = (PuncturedHandle.boundaryPoint q.1, q.2) := by
  rw [Subtype.ext_iff]
  change d.newExterior r = d.newPiece (PuncturedHandle.newPunctured p) ↔ _
  rw [d.new_overlap]
  constructor
  · rintro ⟨q, hr, hp⟩
    exact
      ⟨q, hr,
        PuncturedHandle.newPunctured_injective
          (hp.trans (PuncturedHandle.newPunctured_boundary q).symm)⟩
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, PuncturedHandle.newPunctured_boundary q⟩

structure AttachmentBoundaryData (N P M : Type*) [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  handle : PuncturedHandle.UnitBall N × PuncturedHandle.UnitBall P → M
  handle_closed : Topology.IsClosedEmbedding handle
  height_continuous : Continuous f
  lower_frontier : frontier {x | f x ≤ a} = {x | f x = a}
  lower_face : ∀ z, f (handle z) = a ↔ ‖(z.1 : N)‖ = 1
  upper_face : ∀ z, handle z ∈ frontier ({x | f x ≤ a} ∪ Set.range handle) ↔ ‖(z.2 : P)‖ = 1

abbrev AttachmentBoundaryData.Level {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (_ : AttachmentBoundaryData N P M f a) :=
  { x : M // f x = a }

abbrev AttachmentBoundaryData.region {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : Set M :=
  {x | f x ≤ a} ∪ Set.range d.handle

abbrev AttachmentBoundaryData.Boundary {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) :=
  frontier d.region

abbrev AttachmentBoundaryData.Exterior {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) :=
  { x : M // f x = a ∧ x ∈ d.Boundary }

def AttachmentBoundaryData.oldExterior {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : d.Exterior → d.Level := fun x =>
  ⟨x, x.property.1⟩

def AttachmentBoundaryData.newExterior {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : d.Exterior → d.Boundary := fun x =>
  ⟨x, x.property.2⟩

def AttachmentBoundaryData.oldPiece {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a)
    (z : PuncturedHandle.UnitSphere N × PuncturedHandle.UnitBall P) : d.Level :=
  ⟨d.handle (PuncturedHandle.sphereToBall z.1, z.2),
    (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp z.1.property)⟩

def AttachmentBoundaryData.newPiece {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a)
    (z : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P) : d.Boundary :=
  ⟨d.handle (z.1, PuncturedHandle.sphereToBall z.2),
    (d.upper_face _).mpr (mem_sphere_zero_iff_norm.mp z.2.property)⟩

def AttachmentBoundaryData.boundary {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a)
    (q : PuncturedHandle.UnitSphere N × PuncturedHandle.UnitSphere P) : d.Exterior :=
  ⟨d.handle (PuncturedHandle.sphereToBall q.1, PuncturedHandle.sphereToBall q.2),
    (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp q.1.property),
    (d.upper_face _).mpr (mem_sphere_zero_iff_norm.mp q.2.property)⟩

theorem AttachmentBoundaryData.oldExterior_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.oldExterior :=
  ClosedCover.isClosedEmbedding_codRestrict
    ((isClosed_eq d.height_continuous continuous_const).inter
        isClosed_frontier).isClosedEmbedding_subtypeVal
    (fun x => x.property.1)

theorem AttachmentBoundaryData.newExterior_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.newExterior :=
  ClosedCover.isClosedEmbedding_codRestrict
    ((isClosed_eq d.height_continuous continuous_const).inter
        isClosed_frontier).isClosedEmbedding_subtypeVal
    (fun x => x.property.2)

theorem AttachmentBoundaryData.sphereToBall_closed {N : Type*} [NormedAddCommGroup N] :
    Topology.IsClosedEmbedding (PuncturedHandle.sphereToBall (E := N)) :=
  ClosedCover.isClosedEmbedding_codRestrict
    Metric.isClosed_sphere.isClosedEmbedding_subtypeVal
    (fun u => (mem_sphere_zero_iff_norm.mp u.property).le)

theorem AttachmentBoundaryData.oldPiece_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.oldPiece := by
  exact
    ClosedCover.isClosedEmbedding_codRestrict
      (d.handle_closed.comp (sphereToBall_closed.prodMap Topology.IsClosedEmbedding.id))
      (fun z => (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp z.1.property))

theorem AttachmentBoundaryData.newPiece_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.newPiece := by
  apply ClosedCover.isClosedEmbedding_codRestrict
  exact d.handle_closed.comp (Topology.IsClosedEmbedding.id.prodMap sphereToBall_closed)

/-- The old-exterior piece covers its part of the attachment boundary: the first half of the two-set Mayer-Vietoris cover for the attached handle (Hatcher, Algebraic Topology, the handle-attachment cover). -/
theorem AttachmentBoundaryData.old_cover {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) :
    Set.range d.oldExterior ∪ Set.range d.oldPiece = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : (x : M) ∈ Set.range d.handle
  · obtain ⟨z, hz⟩ := hx
    have hnorm : ‖(z.1 : N)‖ = 1 := (d.lower_face z).mp (hz ▸ x.property)
    refine Or.inr ⟨(⟨z.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, z.2), ?_⟩
    exact Subtype.ext hz
  · have hfront : (x : M) ∈ d.Boundary := by
      have hlow : (x : M) ∈ frontier {y | f y ≤ a} := by
        rw [d.lower_frontier]
        exact x.property
      change (x : M) ∈ frontier d.region
      rw [frontier] at hlow ⊢
      refine ⟨closure_mono Set.subset_union_left hlow.1, ?_⟩
      intro hi
      apply hlow.2
      apply mem_interior_iff_mem_nhds.mpr
      have hnear := mem_interior_iff_mem_nhds.mp hi
      have hout := d.handle_closed.isClosed_range.isOpen_compl.mem_nhds hx
      apply Filter.mem_of_superset (Filter.inter_mem hnear hout)
      intro y hy
      exact hy.1.resolve_right hy.2
    exact Or.inl ⟨⟨x, x.property, hfront⟩, rfl⟩

/-- The new-piece cover half: together with `old_cover` this realizes the handle attachment as a two-open cover, feeding the homology rows. -/
theorem AttachmentBoundaryData.new_cover {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) :
    Set.range d.newExterior ∪ Set.range d.newPiece = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hclosed : IsClosed d.region :=
    (isClosed_le d.height_continuous continuous_const).union d.handle_closed.isClosed_range
  have hx : (x : M) ∈ d.region := by
    have hc := frontier_subset_closure x.property
    rwa [hclosed.closure_eq] at hc
  rcases hx with hx | ⟨z, hz⟩
  · have heq : f x = a := by
      apply le_antisymm hx
      by_contra hn
      have hlt : f x < a := lt_of_not_ge hn
      have hi : (x : M) ∈ interior d.region :=
        interior_maximal (fun y (hy : f y < a) => Or.inl hy.le)
          (isOpen_lt d.height_continuous continuous_const) hlt
      exact x.property.2 hi
    exact Or.inl ⟨⟨x, heq, x.property⟩, rfl⟩
  · have hnorm : ‖(z.2 : P)‖ = 1 := (d.upper_face z).mp (hz ▸ x.property)
    refine Or.inr ⟨(z.1, ⟨z.2, mem_sphere_zero_iff_norm.mpr hnorm⟩), ?_⟩
    exact Subtype.ext hz

theorem AttachmentBoundaryData.old_overlap {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) (r : d.Exterior)
    (z : PuncturedHandle.UnitSphere N × PuncturedHandle.UnitBall P) :
    d.oldExterior r = d.oldPiece z ↔
      ∃ q, r = d.boundary q ∧ z = PuncturedHandle.oldBoundary q := by
  constructor
  · intro h
    have hr : (r : M) = d.handle (PuncturedHandle.sphereToBall z.1, z.2) :=
      congrArg Subtype.val h
    have hnorm : ‖(z.2 : P)‖ = 1 := (d.upper_face _).mp (hr ▸ r.property.2)
    refine ⟨(z.1, ⟨z.2, mem_sphere_zero_iff_norm.mpr hnorm⟩), Subtype.ext hr, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

theorem AttachmentBoundaryData.new_overlap {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) (r : d.Exterior)
    (z : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P) :
    d.newExterior r = d.newPiece z ↔
      ∃ q, r = d.boundary q ∧ z = PuncturedHandle.newBoundary q := by
  constructor
  · intro h
    have hr : (r : M) = d.handle (z.1, PuncturedHandle.sphereToBall z.2) :=
      congrArg Subtype.val h
    have hnorm : ‖(z.1 : N)‖ = 1 := (d.lower_face _).mp (hr ▸ r.property.1)
    refine ⟨(⟨z.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, z.2), Subtype.ext hr, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

def AttachmentBoundaryData.surgeryBoundaryPair {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : AttachmentBoundaryData N P M f a) :
    SurgeryBoundaryPair N P d.Exterior d.Level d.Boundary
    where
  oldExterior := d.oldExterior
  newExterior := d.newExterior
  oldPiece := d.oldPiece
  newPiece := d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := d.newPiece_closed
  old_cover := d.old_cover
  new_cover := d.new_cover
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := d.new_overlap
end Mathoverflow1973
