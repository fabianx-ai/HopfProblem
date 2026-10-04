/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Topology.Homotopy.CellAttachment
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskCollapse
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation

/-!
# Collapsing the lower sublevel set of a Morse surgery to a point

For a Morse surgery datum `d` at a critical point of index `λ`, collapsing the lower sublevel set
`{f ≤ f p - r²}` to the point at infinity of the core disk gives
`ManifoldMorse.MorseSurgeryData.upperCollapseMap : {f ≤ f p + r²} → OnePoint (ℝ^λ)`, and its
restriction `levelCollapseMap` to the upper level, which sends the belt sphere to `0`
(`levelCollapse_zero_iff`) and is the normalised belt normal `collapseNormal` on the new piece
(`levelCollapse_eq_coe_collapseNormal`).  On homology the collapse map composed with the
suspension isomorphism of `OnePoint (ℝ^λ)` is the Morse connecting map
(`upperCollapse_connecting_compare`), its kernel is the image of the lower sublevel set
(`upperCollapse_homology_kernel`), and it is onto in degree `k + 2` when
`H_{k+1}` of the lower set vanishes (`upperCollapse_surjective_of_lower`).  For a sphere `g` in
the upper level transverse to the belt sphere, the intersection points carry separated
neighbourhoods (`CollapseNeighborhoods`, `nonempty_collapseNeighborhoods`) on which the collapse is
the belt normal, and the local Jacobian sign of the collapse equals the intersection sign
(`collapseNormal_comp_sign_of_transverse`).  This is the Morse-theoretic form of the degree
computation of Milnor, *Lectures on the h-cobordism theorem*, §7 (intersection numbers via
`H_*(M_{upper}, M_{lower})`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The collapse map `{f ≤ f p - r²} ∪ range handleMap → OnePoint N` of the handle attachment of
`d`: `∞` on the lower sublevel set, `collapse ∘ fst` on the handle. -/
def ManifoldMorse.MorseSurgeryData.attachmentCollapseMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap),
      OnePoint d.chart.NegativeCoordinates) :=
  ClosedHandleCore.collapseMap _ d.handleMap (isClosed_le hf continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)

attribute [local instance 100] Classical.propDecidable in
/-- The collapse map `{f ≤ f p + r²} → OnePoint N` of `d`, `attachmentCollapseMap` transported by
the attachment homeomorphism. -/
def ManifoldMorse.MorseSurgeryData.upperCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C({ y : M // f y ≤ f p + d.radius ^ 2 }, OnePoint d.chart.NegativeCoordinates) :=
  (d.attachmentCollapseMap hf).comp d.attachmentHomeomorph.symm.toHomotopyEquiv.toFun

attribute [local instance 100] Classical.propDecidable in
/-- `upperCollapseMap hf (attachmentHomeomorph x) = attachmentCollapseMap hf x`. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap)) :
    d.upperCollapseMap hf (d.attachmentHomeomorph x) = d.attachmentCollapseMap hf x := by
  change d.attachmentCollapseMap hf (d.attachmentHomeomorph.symm (d.attachmentHomeomorph x)) = _
  exact congrArg (d.attachmentCollapseMap hf) (d.attachmentHomeomorph.symm_apply_apply x)

attribute [local instance 100] Classical.propDecidable in
/-- `upperCollapseMap hf` is `∞` on the lower sublevel set. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_old {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : { y : M // f y ≤ f p - d.radius ^ 2 }) :
    d.upperCollapseMap hf (d.realizedLowerInclusion x) = (OnePoint.infty) := by
  change
    d.upperCollapseMap hf
        (d.attachmentHomeomorph (ClosedHandleCore.oldInclusion _ d.handleMap x)) =
      (OnePoint.infty)
  rw [d.upperCollapse_realization]
  exact ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ x

attribute [local instance 100] Classical.propDecidable in
/-- `upperCollapseMap hf` on the handle point `handleMap z` is `DiskOnePointCollapse.collapse z.1`.
-/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_handle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z : d.HandleDomain) :
    d.upperCollapseMap hf (d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩) =
      DiskOnePointCollapse.collapse z.1 := by
  exact
    (d.upperCollapse_realization hf
          (ClosedHandleCore.handleInclusion _ d.handleMap z)).trans
      (ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _ z)

attribute [local instance 100] Classical.propDecidable in
/-- The restriction of `upperCollapseMap hf` to the upper level `d.UpperLevel`. -/
def ManifoldMorse.MorseSurgeryData.levelCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(d.UpperLevel, OnePoint d.chart.NegativeCoordinates) :=
  (d.upperCollapseMap hf).comp ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

attribute [local instance 100] Classical.propDecidable in
/-- `levelCollapseMap hf y = attachmentCollapseMap hf x` when `y = attachmentHomeomorph x`. -/
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_realized {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (y : d.UpperLevel) (x : ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap))
    (hy : (y : M) = (d.attachmentHomeomorph x).val) :
    d.levelCollapseMap hf y = d.attachmentCollapseMap hf x := by
  change d.upperCollapseMap hf ⟨y.val, y.property.le⟩ = _
  have heq :
    (⟨y.val, y.property.le⟩ : { z : M // f z ≤ f p + d.radius ^ 2 }) = d.attachmentHomeomorph x :=
    Subtype.ext hy
  rw [heq, d.upperCollapse_realization]

attribute [local instance 100] Classical.propDecidable in
/-- `levelCollapseMap hf` is `∞` on the new exterior of the surgery. -/
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (r) :
    d.levelCollapseMap hf (d.surgery.newExterior r) = (OnePoint.infty) := by
  rw [d.levelCollapse_realized hf _ _ (d.newExterior_eq r)]
  exact ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ ⟨r.val, r.property.1.le⟩

attribute [local instance 100] Classical.propDecidable in
/-- `levelCollapseMap hf` on the new piece point `newPiece z` is the collapse of the unit-ball
coordinate of `z.1`. -/
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.surgery.newPiece z) =
      DiskOnePointCollapse.collapse
        (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1) := by
  rw [d.levelCollapse_realized hf _ _ (d.newPiece_eq z)]
  exact
    ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _
      (d.chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2))

attribute [local instance 100] Classical.propDecidable in
/-- `levelCollapseMap hf x = 0` iff `x` lies on the belt sphere. -/
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : d.UpperLevel) :
    d.levelCollapseMap hf x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ Set.range d.surgery.beltSphere := by
  have hx : x ∈ Set.range d.surgery.newExterior ∪ Set.range d.surgery.newPiece := by
    rw [d.surgery.new_cover]
    trivial
  rcases hx with ⟨r, rfl⟩ | ⟨z, rfl⟩
  · rw [d.levelCollapse_newExterior]
    exact iff_of_false (OnePoint.infty_ne_coe _) (d.surgery.newExterior_avoids r)
  · rw [d.levelCollapse_newPiece, DiskOnePointCollapse.collapse_eq_zero_iff,
      d.surgery.newPiece_mem_belt_iff]
    rfl

attribute [local instance 100] Classical.propDecidable in
/-- `upperCollapseMap hf ∘ coreUnionHomotopyEquiv` is the collapse map of the core cell
presentation. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_coreCell {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.upperCollapseMap hf).comp (d.coreUnionHomotopyEquiv hf).toFun =
      (d.coreCellPresentation hf).collapseMap := by
  apply ContinuousMap.ext
  rintro ⟨x, hx | ⟨u, rfl⟩⟩
  · exact
      (d.upperCollapse_old hf ⟨x, hx⟩).trans
        ((d.coreCellPresentation hf).collapseMap_old ⟨⟨x, Or.inl hx⟩, hx⟩).symm
  · change
      d.upperCollapseMap hf
          (d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩) =
        (d.coreCellPresentation hf).collapseMap ((d.coreCellPresentation hf).cell u)
    rw [d.upperCollapse_handle, (d.coreCellPresentation hf).collapseMap_cell]

attribute [local instance 100] Classical.propDecidable in
/-- On homology, `upperCollapseMap hf` composed with `cellTotalHomologyEquiv hf k` is the collapse
map of the core cell presentation. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapseHomology_coreCell {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k) :
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (d.cellTotalHomologyEquiv hf k a) =
      SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).collapseMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k a) =
      _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    d.upperCollapse_coreCell]

attribute [local instance 100] Classical.propDecidable in
/-- `OnePointCover.sphereConnecting overlapRadius _ k ∘ H_{k+1}(upperCollapseMap hf)` is the
Morse connecting map `morseConnectingMap hf k`. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1)) :
    OnePointCover.sphereConnecting OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a) =
      d.morseConnectingMap hf k a := by
  obtain ⟨b, rfl⟩ := (d.cellTotalHomologyEquiv hf (k + 1)).surjective a
  rw [d.upperCollapseHomology_coreCell, (d.coreCellPresentation hf).collapse_connecting_compare,
    d.morseConnecting_compare]

attribute [local instance 100] Classical.propDecidable in
/-- `OnePointCover.sphereHomologyEquiv overlapRadius _ k ∘ H_{k+2}(upperCollapseMap hf)` is
`morseConnectingMap hf (k + 1)`. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 2)) :
    OnePointCover.sphereHomologyEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2) a) =
      d.morseConnectingMap hf (k + 1) a :=
  d.upperCollapse_connecting_compare hf (k + 1) a

attribute [local instance 100] Classical.propDecidable in
/-- The kernel of `H_{k+1}(upperCollapseMap hf)` is the image of
`lowerRealizationHomologyMap (k + 1)`. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1)) =
      LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) := by
  rw [d.morse_exact_at_upper hf k]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a = 0 ↔
      d.morseConnectingMap hf k a = 0
  rw [← d.upperCollapse_connecting_compare]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact
      (OnePointCover.sphereConnecting_injective OnePointCover.overlapRadius
          OnePointCover.overlapRadius_pos k)
        (h.trans (map_zero _).symm)

attribute [local instance 100] Classical.propDecidable in
/-- For `k ≠ 0`, if `H_k(M_{lower})` is a subsingleton then `morseConnectingMap hf k` is
surjective. -/
theorem ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k)] :
    Function.Surjective (d.morseConnectingMap hf k) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.coreBoundaryHomologyMap k) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_attachingSphere hf k hk] at ha
  exact ha

attribute [local instance 100] Classical.propDecidable in
/-- If `H_{k+1}(M_{lower})` is a subsingleton then `H_{k+2}(upperCollapseMap hf)` is surjective. -/
theorem ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } (k + 1))] :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2)) := by
  intro a
  let C :=
    OnePointCover.sphereHomologyEquiv (N := d.chart.NegativeCoordinates)
      OnePointCover.overlapRadius OnePointCover.overlapRadius_pos k
  obtain ⟨b, hb⟩ := d.morseConnecting_surjective_of_lower hf (k + 1) (by omega) (C a)
  refine ⟨b, C.injective ?_⟩
  exact (d.upperCollapse_homology_equiv_compare hf k b).trans hb

attribute [local instance 100] Classical.propDecidable in
/-- `levelCollapseMap hf` on `beltClosedDiskMap z` is the collapse of the belt face disk
coordinate of `z.1`. -/
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.beltClosedDiskMap z) =
      DiskOnePointCollapse.collapse
        (MorseHandle.beltFaceDiskMap
          (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1)) := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.levelCollapse_newPiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- On the new interior, `levelCollapseMap hf x = (collapseNormal x : OnePoint N)`. -/
theorem ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    {x : d.UpperLevel} (hx : x ∈ d.surgery.NewInterior) :
    d.levelCollapseMap hf x = (d.collapseNormal x : OnePoint d.chart.NegativeCoordinates) := by
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  have hz := (d.beltClosedDiskMap_mem_newInterior_iff z).mp hx
  rw [d.levelCollapse_beltClosedDiskMap,
    DiskOnePointCollapse.collapse_interior _
      ((MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val).mpr hz)]
  unfold collapseNormal
  rw [d.beltNormal_beltClosedDiskMap, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- If `d.beltNormal ∘ g` has invertible differential at `x` and `g x` is on the belt sphere, the
sign of the normal Jacobian of `d.collapseNormal ∘ g` at `x` is the belt intersection sign
`d.beltIntersectionSign m j g x`. -/
theorem ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x).IsInvertible)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    SignType.sign
        (SphereNormalCoordinates.normalJacobian j x
          (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
      d.beltIntersectionSign m j g x := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hA) hx]
  exact
    SphereNormalCoordinates.sign_normalJacobian_smul_pos j x _ hA _
      (MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos)

attribute [local instance 100] Classical.propDecidable in
/-- For a smooth `g : Sᵐ → d.UpperLevel` transverse to the belt sphere, at every belt intersection
point the sign of the normal Jacobian of `d.collapseNormal ∘ g` is the belt intersection sign. -/
theorem ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign_of_transverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        SignType.sign
            (SphereNormalCoordinates.normalJacobian j x
              (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
          d.beltIntersectionSign m j g x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact d.collapseNormal_comp_sign m j g x hAi ⟨v, hv⟩

attribute [local instance 100] Classical.propDecidable in
/-- For a smooth `g : Sᵐ → d.UpperLevel` transverse to the belt sphere, the differential of
`d.collapseNormal ∘ g` is invertible at every belt intersection point. -/
theorem ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x).IsInvertible :=
  by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hAi) ⟨v, hv⟩]
  exact
    SphereNormalCoordinates.normalDerivative_smul_isInvertible A hAi _
      (MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos).ne'

attribute [local instance 100] Classical.propDecidable in
/-- Separated neighbourhoods of the belt intersection points of `g : Sᵐ → d.UpperLevel` for the
function `d.collapseNormal ∘ g`, inside `g⁻¹ (new interior)`. -/
abbrev ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) :=
  LocalDegree.SeparatedNeighborhoods (EuclideanSpace ℝ (Fin m))
    (d.beltIntersectionPoints m g) (d.collapseNormal ∘ g) (g ⁻¹' d.surgery.NewInterior)

attribute [local instance 100] Classical.propDecidable in
/-- For a smooth injective `g : Sᵐ → d.UpperLevel` transverse to the belt sphere,
`d.CollapseNeighborhoods m g` is nonempty. -/
theorem ManifoldMorse.MorseSurgeryData.nonempty_collapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      Nonempty (d.CollapseNeighborhoods m g) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  have hfin := d.finite_beltIntersectionPoints hf n m hdim g hg hinj ht
  apply LocalDegree.nonempty_separatedNeighborhoods (EuclideanSpace ℝ (Fin m)) hfin
  · exact fun x hx => d.contMDiffAt_collapseNormal_comp hf m g hg x hx
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    change d.collapseNormal (g x) = 0
    rw [← hv, d.collapseNormal_belt]
  · exact fun x hx => d.isInvertible_collapseNormal_comp_of_transverse hf n m hdim g hg ht x hx
  · intro x hx
    apply hg.continuous.continuousAt
    apply d.surgery.isOpen_newInterior.mem_nhds
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    exact d.surgery.beltSphere_mem_newInterior v

attribute [local instance 100] Classical.propDecidable in
/-- `levelCollapseMap hf ∘ g : Sᵐ → OnePoint N` for `g : C(Sᵐ, d.UpperLevel)`. -/
def ManifoldMorse.MorseSurgeryData.attachingCollapse {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) :
    C(Hemisphere.Sphere m, OnePoint d.chart.NegativeCoordinates) :=
  (d.levelCollapseMap hf).comp g

attribute [local instance 100] Classical.propDecidable in
/-- `attachingCollapse hf m g x = 0` iff `x` is a belt intersection point of `g`. -/
theorem ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (x : Hemisphere.Sphere m) :
    d.attachingCollapse hf m g x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ d.beltIntersectionPoints m g :=
  d.levelCollapse_zero_iff hf (g x)

attribute [local instance 100] Classical.propDecidable in
/-- `attachingCollapse hf m g` maps the complement of the belt intersection points into
`OnePointCover.oldPatch`. -/
theorem ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_old {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) :
    Set.MapsTo (d.attachingCollapse hf m g) (d.beltIntersectionPoints m g)ᶜ
      OnePointCover.oldPatch := by
  intro x hx hzero
  exact hx ((d.attachingCollapse_zero_iff hf m g x).mp hzero)

attribute [local instance 100] Classical.propDecidable in
/-- `attachingCollapse hf m g` maps each neighbourhood `D.neighborhood i` of a belt intersection
point into `OnePointCover.finitePatch`. -/
theorem ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    Set.MapsTo (d.attachingCollapse hf m g) (D.neighborhood i) OnePointCover.finitePatch := by
  intro x hx
  have hnew : g x ∈ d.surgery.NewInterior := D.neighborhood_subset i hx
  change d.levelCollapseMap hf (g x) ≠ OnePoint.infty
  rw [d.levelCollapse_eq_coe_collapseNormal hf hnew]
  exact OnePoint.coe_ne_infty _

attribute [local instance 100] Classical.propDecidable in
/-- The restriction of `attachingCollapse hf m g` to the overlap
`(intersection points)ᶜ ∩ D.neighborhood i → oldPatch ∩ finitePatch`. -/
def ManifoldMorse.MorseSurgeryData.collapseOverlapMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    C(↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i),
      ↥(OnePointCover.oldPatch (N := d.chart.NegativeCoordinates) ∩
          OnePointCover.finitePatch)) :=
  SingularMayerVietoris.coverRestriction (d.attachingCollapse hf m g) _ _
    (fun _ hx =>
      ⟨d.attachingCollapse_maps_old hf m g hx.1,
        d.attachingCollapse_maps_neighborhood hf m g D i hx.2⟩)

attribute [local instance 100] Classical.propDecidable in
/-- `collapseOverlapMap hf m g D i` is `OnePointCover.overlapHomeomorph ∘ D.overlapMap i`. -/
theorem ManifoldMorse.MorseSurgeryData.collapseOverlapMap_eq {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    d.collapseOverlapMap hf m g D i =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.overlapMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    d.levelCollapseMap hf (g x.val) =
      (OnePointCover.overlapHomeomorph (D.overlapMap i x)).val
  rw [OnePointCover.overlapHomeomorph_apply,
    LocalDegree.SeparatedNeighborhoods.overlapMap_coe]
  exact d.levelCollapse_eq_coe_collapseNormal hf (D.neighborhood_subset i x.property.2)

attribute [local instance 100] Classical.propDecidable in
/-- `collapseOverlapMap hf m g D i ∘ D.overlapSphereEquiv i` is
`OnePointCover.overlapHomeomorph ∘ (D.data i).innerBoundary.map`. -/
theorem ManifoldMorse.MorseSurgeryData.collapseOverlapMap_sphereEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    (d.collapseOverlapMap hf m g D i).comp (D.overlapSphereEquiv i).toFun =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
        (D.data i).innerBoundary.map := by
  rw [d.collapseOverlapMap_eq hf m g D i, ContinuousMap.comp_assoc, D.overlapMap_sphereEquiv]

end
