/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.OnePointCollapse
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover

/-!
# Collapsing the complement of an attached cell to a point

The quotient of the closed unit disk of `N` by its boundary is the one-point compactification
`OnePoint N` (`DiskOnePointCollapse.collapse`, Hatcher, *Algebraic Topology*, Example 0.2 /
Proposition 2.22).  For a cell attached to `A` along its boundary, or a handle
`Dᵏ × Dⁿ⁻ᵏ` attached along `∂Dᵏ × Dⁿ⁻ᵏ`, collapsing `A` to the point at infinity gives a
continuous map `X → OnePoint N` (`EmbeddedCellAttachment.collapseMap`,
`ClosedHandleCore.collapseMap`) which carries the Mayer–Vietoris cover of the cell attachment to
the two-patch cover of `OnePoint N` and is compatible with the connecting homomorphisms
(`EmbeddedCellAttachment.collapse_connecting_compare`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- The collapse `MorseHandle.UnitDisk N → OnePoint N` sending the boundary sphere to `∞` and the
open disk to `N` through the inverse of `univUnitBall`. -/
def DiskOnePointCollapse.collapse {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    C(MorseHandle.UnitDisk N, OnePoint N) :=
  ⟨fun z => interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z),
    interiorHomeomorph.onePointCongr.continuous.comp
      (OnePointCollapse.continuous_collapse boundary boundary_closed)⟩

/-- `collapse z = ∞` when `‖z‖ = 1`. -/
theorem DiskOnePointCollapse.collapse_boundary {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ = 1) :
    collapse z = (OnePoint.infty) := by
  change interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z) = (OnePoint.infty)
  rw [OnePointCollapse.collapse_of_mem boundary hz]
  rfl

/-- `collapse z = (univUnitBall.symm z : OnePoint N)` when `‖z‖ < 1`. -/
theorem DiskOnePointCollapse.collapse_interior {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ < 1) :
    collapse z = ((OpenPartialHomeomorph.univUnitBall.symm (z : N) : N) : OnePoint N) := by
  change interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z) = _
  rw [OnePointCollapse.collapse_of_not_mem boundary ((not_mem_boundary_iff z).mpr hz)]
  rfl

/-- `collapse z = collapse w` iff `z = w` or both `z` and `w` lie on the boundary sphere. -/
theorem DiskOnePointCollapse.collapse_eq_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z w : MorseHandle.UnitDisk N) :
    collapse z = collapse w ↔ z = w ∨ ‖(z : N)‖ = 1 ∧ ‖(w : N)‖ = 1 := by
  change
    interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary z) =
        interiorHomeomorph.onePointCongr (OnePointCollapse.collapse boundary w) ↔
      _
  rw [interiorHomeomorph.onePointCongr.injective.eq_iff, OnePointCollapse.collapse_eq_iff]
  rfl

/-- `collapse (compress x) = (x : OnePoint N)`. -/
theorem DiskOnePointCollapse.collapse_compress {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : collapse (compress x) = (x : OnePoint N) := by
  rw [collapse_interior _ (norm_compress_lt x)]
  exact
    congrArg (fun y : N => (y : OnePoint N))
      (OpenPartialHomeomorph.univUnitBall.left_inv (Set.mem_univ x))

/-- `collapse z = (x : OnePoint N)` iff `z = compress x`. -/
theorem DiskOnePointCollapse.collapse_eq_coe_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) (x : N) :
    collapse z = (x : OnePoint N) ↔ z = compress x := by
  rw [← collapse_compress x, collapse_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact ((ne_of_lt (norm_compress_lt x)) h.2).elim
  · exact Or.inl

/-- `collapse z = (0 : OnePoint N)` iff `z = 0`. -/
theorem DiskOnePointCollapse.collapse_eq_zero_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) :
    collapse z = ((0 : N) : OnePoint N) ↔ (z : N) = 0 := by
  rw [collapse_eq_coe_iff]
  constructor
  · intro hz
    exact (congrArg Subtype.val hz).trans compress_zero
  · intro hz
    exact Subtype.ext (hz.trans compress_zero.symm)

/-- `collapse z = ∞` iff `‖z‖ = 1`. -/
theorem DiskOnePointCollapse.collapse_eq_infty_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : MorseHandle.UnitDisk N) :
    collapse z = (OnePoint.infty) ↔ ‖(z : N)‖ = 1 := by
  by_cases hz : ‖(z : N)‖ = 1
  · rw [collapse_boundary z hz]
    exact iff_of_true rfl hz
  · rw [collapse_interior z ((not_mem_boundary_iff z).mp hz)]
    exact iff_of_false (OnePoint.coe_ne_infty _) hz

/-- On the intersection of the old part `A` and the handle `h`, the constant map `∞` and
`DiskOnePointCollapse.collapse ∘ fst` agree: a handle point in `A` has `‖z.1‖ = 1`. -/
theorem ClosedHandleCore.collapseMaps_agree {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P)
    (haz : oldInclusion A h a = handleInclusion A h z) :
    ((OnePoint.infty) : OnePoint N) = DiskOnePointCollapse.collapse z.1 := by
  have heq : (a : X) = h z := congrArg Subtype.val haz
  have hz := (hface z).mp (heq ▸ a.property)
  exact (DiskOnePointCollapse.collapse_boundary z.1 hz).symm

/-- The collapse map `A ∪ range h → OnePoint N` of a closed handle `h : Dᵏ × Dⁿ⁻ᵏ → X` attached to
the closed set `A` along `∂Dᵏ × Dⁿ⁻ᵏ`: `∞` on `A` and `collapse ∘ fst` on the handle. -/
def ClosedHandleCore.collapseMap {N P X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) :
    C(↥(A ∪ Set.range h), OnePoint N) :=
  ClosedCover.mapOfClosedPieces (oldInclusion A h) (handleInclusion A h) (old_closed A h hA)
    (handle_closed A h hh) (pieces_cover A h) (ContinuousMap.const A (OnePoint.infty))
    (DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface)

/-- `collapseMap` is `∞` on the old part `A`. -/
theorem ClosedHandleCore.collapseMap_old {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A) :
    collapseMap A h hA hh hface (oldInclusion A h a) = (OnePoint.infty) :=
  ClosedCover.mapOfClosedPieces_left (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) a

/-- `collapseMap` on the handle point `h z` is `DiskOnePointCollapse.collapse z.1`. -/
theorem ClosedHandleCore.collapseMap_handle {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    collapseMap A h hA hh hface (handleInclusion A h z) =
      DiskOnePointCollapse.collapse z.1 :=
  ClosedCover.mapOfClosedPieces_right (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) z

/-- On a point of `D.old` in the image of the cell, the constant `∞` and
`DiskOnePointCollapse.collapse` agree. -/
theorem EmbeddedCellAttachment.collapseMaps_agree {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (a : D.old)
    (z : MorseHandle.UnitDisk N) (haz : (a : X) = D.cell z) :
    ((OnePoint.infty) : OnePoint N) = DiskOnePointCollapse.collapse z :=
  (DiskOnePointCollapse.collapse_boundary z ((D.boundary z).mp (haz ▸ a.property))).symm

/-- The collapse map `X → OnePoint N` of an embedded cell attachment: `∞` on `D.old` and
`DiskOnePointCollapse.collapse` on the cell. -/
def EmbeddedCellAttachment.collapseMap {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(X, OnePoint N) :=
  ClosedCover.mapOfClosedPieces Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old (OnePoint.infty))
    DiskOnePointCollapse.collapse D.collapseMaps_agree

/-- `D.collapseMap` is `∞` on `D.old`. -/
theorem EmbeddedCellAttachment.collapseMap_old {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (a : D.old) :
    D.collapseMap a = (OnePoint.infty) :=
  ClosedCover.mapOfClosedPieces_left Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) DiskOnePointCollapse.collapse
    D.collapseMaps_agree a

/-- `D.collapseMap (D.cell z) = DiskOnePointCollapse.collapse z`. -/
theorem EmbeddedCellAttachment.collapseMap_cell {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (z : MorseHandle.UnitDisk N) :
    D.collapseMap (D.cell z) = DiskOnePointCollapse.collapse z :=
  ClosedCover.mapOfClosedPieces_right Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) DiskOnePointCollapse.collapse
    D.collapseMaps_agree z

/-- `D.collapseMap x = ∞` iff `x ∈ D.old`. -/
theorem EmbeddedCellAttachment.collapseMap_infty_iff {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = (OnePoint.infty) ↔ x ∈ D.old := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · exact iff_of_true (D.collapseMap_old ⟨x, hx⟩) hx
  · rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_eq_infty_iff, D.boundary]

/-- `D.collapseMap x = (0 : OnePoint N)` iff `x` is the centre `D.cell 0` of the cell. -/
theorem EmbeddedCellAttachment.collapseMap_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = ((0 : N) : OnePoint N) ↔ D.cell ⟨0, by simp⟩ = x := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · rw [D.collapseMap_old ⟨x, hx⟩]
    constructor
    · intro h
      exact (OnePoint.infty_ne_coe (0 : N) h).elim
    · intro h
      rw [← h, D.boundary] at hx
      simp at hx
  · rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_eq_zero_iff]
    constructor
    · intro hz
      exact congrArg D.cell (Subtype.ext hz.symm)
    · intro hz
      exact (congrArg Subtype.val (D.cell_closed.injective hz)).symm

/-- `D.collapseMap` maps `D.oldNeighborhood` into `OnePointCover.oldPatch`. -/
theorem EmbeddedCellAttachment.collapseMaps_oldNeighborhood {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.oldNeighborhood (OnePointCover.oldPatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ ((0 : N) : OnePoint N)
  intro h
  have heq := (D.collapseMap_eq_zero_iff x).mp h
  rw [← heq, D.cell_mem_oldNeighborhood_iff] at hx
  norm_num at hx

/-- `D.collapseMap` maps `D.diskPatch` into `OnePointCover.finitePatch`. -/
theorem EmbeddedCellAttachment.collapseMaps_diskPatch {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.diskPatch (OnePointCover.finitePatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ OnePoint.infty
  exact fun h => hx ((D.collapseMap_infty_iff x).mp h)

/-- The restriction of `D.collapseMap` to the overlaps,
`oldNeighborhood ∩ diskPatch → oldPatch ∩ finitePatch`. -/
def EmbeddedCellAttachment.collapseOverlapMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(↥(D.oldNeighborhood ∩ D.diskPatch),
      ↥(OnePointCover.oldPatch (N := N) ∩ OnePointCover.finitePatch)) :=
  SingularMayerVietoris.coverRestriction D.collapseMap _ _
    (CoverNaturality.map_intersection _ _ _ _ D.collapseMap D.collapseMaps_oldNeighborhood
      D.collapseMaps_diskPatch)

/-- `collapseOverlapMap` carries `D.overlapSphereEquiv u` to
`OnePointCover.overlapSphereEquiv overlapRadius _ u`. -/
theorem EmbeddedCellAttachment.collapseOverlap_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (u : Metric.sphere (0 : N) 1) :
    D.collapseOverlapMap (D.overlapSphereEquiv u) =
      OnePointCover.overlapSphereEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos u := by
  apply Subtype.ext
  change
    D.collapseMap (D.cell (DiskAnnulus.middleDisk u)) =
      ((OnePointCover.overlapRadius • (u : N) : N) : OnePoint N)
  rw [D.collapseMap_cell,
    DiskOnePointCollapse.collapse_interior _ (DiskAnnulus.middleDisk_mem u).2]
  apply congrArg (OnePoint.some : N → OnePoint N)
  change
    (Real.sqrt (1 - ‖(3 / 4 : ℝ) • (u : N)‖ ^ 2))⁻¹ • ((3 / 4 : ℝ) • (u : N)) =
      OnePointCover.overlapRadius • (u : N)
  rw [DiskAnnulus.norm_middle, smul_smul]
  rfl

/-- `collapseOverlapMap ∘ overlapSphereEquiv = OnePointCover.overlapSphereEquiv overlapRadius _`
as maps from the sphere. -/
theorem EmbeddedCellAttachment.collapseOverlap_comp_sphere {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) :
    D.collapseOverlapMap.comp D.overlapSphereEquiv.toFun =
      (OnePointCover.overlapSphereEquiv (N := N) OnePointCover.overlapRadius
          OnePointCover.overlapRadius_pos).toFun :=
  ContinuousMap.ext D.collapseOverlap_sphere

/-- On homology, `collapseOverlapMap` carries `D.overlapHomologyEquiv k a` to
`OnePointCover.overlapHomologyEquiv overlapRadius _ k a`. -/
theorem EmbeddedCellAttachment.collapse_overlapHomology_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (D.overlapHomologyEquiv k a) =
      OnePointCover.overlapHomologyEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k a := by
  change
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap _ k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    D.collapseOverlap_comp_sphere]

/-- Naturality of the connecting maps: `OnePointCover.sphereConnecting overlapRadius _ k` of
`H_{k+1}(collapseMap) a` equals `D.cellConnectingMap k a`. -/
theorem EmbeddedCellAttachment.collapse_connecting_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    OnePointCover.sphereConnecting OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap D.collapseMap (k + 1) a) =
      D.cellConnectingMap k a := by
  apply
    (OnePointCover.overlapHomologyEquiv (N := N) OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k).injective
  change
    OnePointCover.overlapHomologyEquiv _ _ k
        ((OnePointCover.overlapHomologyEquiv _ _ k).symm _) =
      OnePointCover.overlapHomologyEquiv _ _ k ((D.overlapHomologyEquiv k).symm _)
  rw [LinearEquiv.apply_symm_apply, ← D.collapse_overlapHomology_compare,
    LinearEquiv.apply_symm_apply]
  exact
    (SingularMayerVietoris.connectingHomomorphism_naturality_apply D.collapseMap
        D.oldNeighborhood D.diskPatch OnePointCover.oldPatch OnePointCover.finitePatch
        D.collapseMaps_oldNeighborhood D.collapseMaps_diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover OnePointCover.oldPatch_open
        OnePointCover.finitePatch_open OnePointCover.cover k a).symm

end
