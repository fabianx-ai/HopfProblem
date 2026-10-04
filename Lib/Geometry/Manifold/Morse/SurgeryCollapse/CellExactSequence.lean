/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.Topology.Homotopy.CellAttachment
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents

/-!
# The long exact sequence of an attached cell

For a cell `Dᵏ` embedded in `X` and attached to `A = X ∖ int Dᵏ` along its boundary sphere
(`EmbeddedCellAttachment N X`), Mayer–Vietoris for the cover by a neighbourhood of `A` and the
open cell gives the exact sequence
`… → H_{k+1}(X) → H_k(S) → H_k(A) → H_k(X) → …` with connecting map
`EmbeddedCellAttachment.cellConnectingMap` (`cell_exact_at_old`, `cell_exact_at_ambient`,
`cell_exact_at_sphere`); this is the homology sequence of the pair `(X, A)` with
`H_*(X, A) ≅ H̃_{*-1}(S)`, cf. Hatcher, *Algebraic Topology*, Example 2.43 / Proposition 2.22.
In degree `0` the inclusion `A → X` induces a bijection on `H₀` when the sphere is
path-connected (`MorseCancellation.cell_oldHomologyMap_zero_bijective`), and an injection when
the attaching sphere lies in one path component of `A`
(`cell_oldHomologyMap_injective_of_attaching_component`), so `A` is path-connected when `X` is
(`cell_old_pathConnected_of_attaching_component`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- The homology isomorphism `H_k(S(N)) ≃ H_k(oldNeighborhood ∩ diskPatch)` induced by the
homotopy equivalence `D.overlapSphereEquiv`. -/
def EmbeddedCellAttachment.overlapHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(D.oldNeighborhood ∩ D.diskPatch)) k :=
  SingularHomology.homotopyEquivHomologyEquiv D.overlapSphereEquiv k

/-- The connecting homomorphism `H_{k+1}(X) → H_k(S(N))` of the cell attachment `D`: the
Mayer–Vietoris connecting map of the cover `(oldNeighborhood, diskPatch)` followed by
`(D.overlapHomologyEquiv k)⁻¹`. -/
def EmbeddedCellAttachment.cellConnectingMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (D.overlapHomologyEquiv k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k)

/-- The first component of the Mayer–Vietoris left map of `D` on `overlapHomologyEquiv k a`,
transported by `(D.oldHomologyEquiv k)⁻¹`, is `D.attachingHomologyMap k a`. -/
theorem EmbeddedCellAttachment.coverLeft_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    (D.oldHomologyEquiv k).symm
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k a)).1 =
      D.attachingHomologyMap k a := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap D.oldRetraction k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          k (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap D.attachingSphere k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap (D.overlapOldMap.comp D.overlapSphereEquiv.toFun) k
        a =
      _
  rw [D.overlapOldMap_comp_sphere]

/-- For `k ≠ 0`, the Mayer–Vietoris left map of `D` on `overlapHomologyEquiv k a` is
`(oldHomologyEquiv k (attachingHomologyMap k a), 0)`. -/
theorem EmbeddedCellAttachment.coverLeft_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
        (D.overlapHomologyEquiv k a) =
      (D.oldHomologyEquiv k (D.attachingHomologyMap k a), 0) := by
  let := D.diskPatch_homology_subsingleton k hk
  apply Prod.ext
  · exact (D.oldHomologyEquiv k).symm_apply_eq.mp (D.coverLeft_old k a)
  · exact Subsingleton.elim _ _

/-- `D.cellConnectingMap k a = 0` iff the Mayer–Vietoris connecting map of `D` vanishes on `a`. -/
theorem EmbeddedCellAttachment.cellConnecting_eq_zero_iff {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    D.cellConnectingMap k a = 0 ↔
      SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
          D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k a =
        0 := by
  change (D.overlapHomologyEquiv k).symm _ = 0 ↔ _ = 0
  constructor
  · intro h
    exact (D.overlapHomologyEquiv k).symm.injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

/-- Exactness at `H_k(A)`, `k ≠ 0`: the image of `attachingHomologyMap k : H_k(S) → H_k(A)` is the
kernel of `oldHomologyMap k : H_k(A) → H_k(X)`. -/
theorem EmbeddedCellAttachment.cell_exact_at_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.attachingHomologyMap k) = LinearMap.ker (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch k)
        (D.overlapHomologyEquiv k s)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k s)) =
        0 at hzero
    rw [D.coverLeft_formula k hk, D.coverRight_old] at hzero
    exact hzero
  · intro ha
    have hpair :
      (D.oldHomologyEquiv k a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
            (D.oldHomologyEquiv k a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover k] at hpair
    obtain ⟨c, hc⟩ := hpair
    refine ⟨(D.overlapHomologyEquiv k).symm c, ?_⟩
    have hc' :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm c)) =
        (D.oldHomologyEquiv k a, 0) := by
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    rw [D.coverLeft_formula k hk] at hc'
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        hc'
    exact (D.oldHomologyEquiv k).injective heq

/-- Exactness at `H_{k+1}(X)`: the image of `oldHomologyMap (k + 1) : H_{k+1}(A) → H_{k+1}(X)` is
the kernel of `cellConnectingMap k : H_{k+1}(X) → H_k(S)`. -/
theorem EmbeddedCellAttachment.cell_exact_at_ambient {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ) :
    LinearMap.range (D.oldHomologyMap (k + 1)) = LinearMap.ker (D.cellConnectingMap k) := by
  rw [← D.range_coverRight (k + 1) (Nat.succ_ne_zero k),
    SingularMayerVietoris.exact_at_ambient D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover k]
  ext a
  exact (D.cellConnecting_eq_zero_iff k a).symm

/-- `a` is in the image of `cellConnectingMap k` iff `overlapHomologyEquiv k a` is in the image of
the Mayer–Vietoris connecting map of `D`. -/
theorem EmbeddedCellAttachment.mem_range_cellConnecting {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    a ∈ LinearMap.range (D.cellConnectingMap k) ↔
      D.overlapHomologyEquiv k a ∈
        LinearMap.range
          (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
            D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change _ = D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm _)
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (D.overlapHomologyEquiv k).symm _ = a
    rw [hx, LinearEquiv.symm_apply_apply]

/-- For `k ≠ 0`, the Mayer–Vietoris left map of `D` vanishes on `overlapHomologyEquiv k a` iff
`attachingHomologyMap k a = 0`. -/
theorem EmbeddedCellAttachment.coverLeft_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k a) =
        0 ↔
      D.attachingHomologyMap k a = 0 := by
  rw [D.coverLeft_formula k hk]
  constructor
  · intro h
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        h
    exact (D.oldHomologyEquiv k).injective (heq.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]
    rfl

/-- Exactness at `H_k(S)`, `k ≠ 0`: the image of `cellConnectingMap k : H_{k+1}(X) → H_k(S)` is
the kernel of `attachingHomologyMap k : H_k(S) → H_k(A)`. -/
theorem EmbeddedCellAttachment.cell_exact_at_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.cellConnectingMap k) = LinearMap.ker (D.attachingHomologyMap k) := by
  ext a
  rw [D.mem_range_cellConnecting k,
    SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k]
  exact D.coverLeft_eq_zero_iff k hk a

/-- If the sphere `S(N)` is path-connected, the connecting map `cellConnectingMap 0 : H₁(X) → H₀(S)`
is zero. -/
theorem EmbeddedCellAttachment.cellConnecting_zero_apply {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)]
    (a : SingularMayerVietoris.SingularHomology X 1) : D.cellConnectingMap 0 a = 0 := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  have hc :
    D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a) ∈
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    rw [←
      SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
        D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0]
    exact (D.mem_range_cellConnecting 0 _).mp ⟨a, rfl⟩
  change
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
        (D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a)) =
      0 at hc
  have h := congrArg Prod.snd hc
  rw [SingularMayerVietoris.leftHomologyMap_apply] at h
  have hz : SingularMayerVietoris.singularHomologyMap q 0 (D.cellConnectingMap 0 a) = 0 := by
    rw [SingularHomology.singularHomologyMap_comp]
    exact neg_eq_zero.mp h
  apply SphereHomology.singularHomologyMap_zero_injective q
  exact hz.trans (map_zero _).symm

/-- If the sphere `S(N)` is path-connected, `D.oldHomologyMap 0 : H₀(A) → H₀(X)` is injective. -/
theorem MorseCancellation.cell_oldHomologyMap_zero_injective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Injective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpair :
    (D.oldHomologyEquiv 0 a, 0) ∈
      LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.oldHomologyEquiv 0 a, 0) =
        0
    rw [D.coverRight_old]
    exact ha
  rw [←
    SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover 0] at hpair
  obtain ⟨c, hc⟩ := hpair
  have hq :
    SingularMayerVietoris.singularHomologyMap q 0 ((D.overlapHomologyEquiv 0).symm c) = 0 := by
    have h := congrArg Prod.snd hc
    rw [SingularMayerVietoris.leftHomologyMap_apply] at h
    rw [SingularHomology.singularHomologyMap_comp]
    change
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
          (D.overlapHomologyEquiv 0 ((D.overlapHomologyEquiv 0).symm c)) =
        0
    rw [LinearEquiv.apply_symm_apply]
    exact neg_eq_zero.mp h
  have hz : (D.overlapHomologyEquiv 0).symm c = 0 :=
    SphereHomology.singularHomologyMap_zero_injective q (hq.trans (map_zero _).symm)
  have hc0 : c = 0 := by
    apply (D.overlapHomologyEquiv 0).symm.injective
    exact hz.trans (map_zero _).symm
  rw [hc0, map_zero] at hc
  apply (D.oldHomologyEquiv 0).injective
  exact (congrArg Prod.fst hc).symm.trans (map_zero _).symm

/-- If the sphere `S(N)` is path-connected, `D.oldHomologyMap 0 : H₀(A) → H₀(X)` is surjective. -/
theorem MorseCancellation.cell_oldHomologyMap_zero_surjective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Surjective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  intro a
  obtain ⟨⟨b, c⟩, hbc⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover a
  obtain ⟨z, hz⟩ := SphereHomology.singularHomologyMap_zero_surjective q c
  let v := D.overlapHomologyEquiv 0 z
  have hv :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
        v =
      c := by
    rw [SingularHomology.singularHomologyMap_comp] at hz
    exact hz
  have hzero :=
    LinearMap.congr_fun
      (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0) v
  change
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0 v) =
      0 at hzero
  rw [SingularMayerVietoris.leftHomologyMap_apply, SingularMayerVietoris.rightHomologyMap_apply,
    map_neg, hv] at hzero
  have hrel :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) 0
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          0 v) =
      SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.diskPatch) 0 c := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hzero
  refine
    ⟨(D.oldHomologyEquiv 0).symm
        (b +
          SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.inclusion Set.inter_subset_left) 0 v),
      ?_⟩
  rw [← D.coverRight_old, LinearEquiv.apply_symm_apply,
    SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero, map_add, hrel]
  exact hbc

/-- If the sphere `S(N)` is path-connected, `D.oldHomologyMap 0 : H₀(A) → H₀(X)` is bijective. -/
theorem MorseCancellation.cell_oldHomologyMap_zero_bijective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Bijective (D.oldHomologyMap 0) :=
  ⟨cell_oldHomologyMap_zero_injective D, cell_oldHomologyMap_zero_surjective D⟩

/-- The map `H₀(S(N)) → H₀(diskPatch)` induced by the inclusion of the sphere into the disk patch
through `D.overlapSphereEquiv`. -/
def MorseCancellation.cellDiskBoundaryHomologyMap {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.diskPatch 0 :=
  SingularMayerVietoris.singularHomologyMap
    ((ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun) 0

/-- `D.oldHomologyMap 0 a = 0` iff `a = attachingHomologyMap 0 z` for some `z ∈ H₀(S(N))` with
`cellDiskBoundaryHomologyMap D z = 0`. -/
theorem MorseCancellation.cell_oldHomologyMap_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (a : SingularMayerVietoris.SingularHomology D.old 0) :
    D.oldHomologyMap 0 a = 0 ↔
      ∃ z : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0,
        D.attachingHomologyMap 0 z = a ∧ cellDiskBoundaryHomologyMap D z = 0 := by
  constructor
  · intro ha
    have hp :
      (D.oldHomologyEquiv 0 a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.oldHomologyEquiv 0 a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover 0] at hp
    obtain ⟨c, hc⟩ := hp
    let z := (D.overlapHomologyEquiv 0).symm c
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      dsimp [z]
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    refine ⟨z, ?_, ?_⟩
    · rw [← D.coverLeft_old, hL, LinearEquiv.symm_apply_apply]
    · have hs := congrArg Prod.snd hL
      rw [SingularMayerVietoris.leftHomologyMap_apply] at hs
      change SingularMayerVietoris.singularHomologyMap _ 0 z = 0
      rw [SingularHomology.singularHomologyMap_comp]
      exact neg_eq_zero.mp hs
  · rintro ⟨z, hza, hz⟩
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      apply Prod.ext
      · exact (D.oldHomologyEquiv 0).symm_apply_eq.mp ((D.coverLeft_old 0 z).trans hza)
      · rw [SingularMayerVietoris.leftHomologyMap_apply]
        rw [cellDiskBoundaryHomologyMap, SingularHomology.singularHomologyMap_comp] at hz
        exact neg_eq_zero.mpr hz
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0)
        (D.overlapHomologyEquiv 0 z)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.overlapHomologyEquiv 0 z)) =
        0 at hzero
    rw [hL, D.coverRight_old] at hzero
    exact hzero

/-- If every attaching point `D.attachingSphere u` is joined in `A` to the point `p`, then
`D.oldHomologyMap 0 : H₀(A) → H₀(X)` is injective. -/
theorem MorseCancellation.cell_oldHomologyMap_injective_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) :
    Function.Injective (D.oldHomologyMap 0) := by
  let c : C(D.diskPatch, D.old) := ContinuousMap.const _ p
  have heq :
    D.attachingHomologyMap 0 =
      (SingularMayerVietoris.singularHomologyMap c 0).comp (cellDiskBoundaryHomologyMap D) := by
    apply homologyZero_linearMap_ext
    intro u
    change
      SingularMayerVietoris.singularHomologyMap D.attachingSphere 0
          (SingularHomology.pointClass u) =
        SingularMayerVietoris.singularHomologyMap c 0
          (SingularMayerVietoris.singularHomologyMap _ 0 (SingularHomology.pointClass u))
    rw [SingularHomology.singularHomologyMap_pointClass,
      SingularHomology.singularHomologyMap_pointClass,
      SingularHomology.singularHomologyMap_pointClass]
    exact (pointClass_eq_iff_joined _ _).mpr (hcomponent u)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨z, hza, hz⟩ := (cell_oldHomologyMap_zero_iff D a).mp ha
  rw [← hza, heq, LinearMap.comp_apply, hz, map_zero]

/-- If `X` is path-connected and every attaching point `D.attachingSphere u` is joined in `A` to a
point `p`, then `A = D.old` is path-connected. -/
theorem MorseCancellation.cell_old_pathConnected_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) [PathConnectedSpace X] (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) : PathConnectedSpace D.old := by
  let : Nonempty D.old := ⟨p⟩
  exact
    pathConnectedSpace_of_homologyZero_injective (SingularMayerVietoris.subtypeInclusion D.old)
      (cell_oldHomologyMap_injective_of_attaching_component D p hcomponent)

end
