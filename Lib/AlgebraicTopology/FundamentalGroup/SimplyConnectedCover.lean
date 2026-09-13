/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# The simply connected covering construction

  The simply connected cover: for a path-connected, locally path-connected and
  semilocally simply connected space, the space of homotopy classes of paths from
  a basepoint, covering `X` by endpoint evaluation (Hatcher, Algebraic Topology,
  Section 1.3 prerequisites).
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Paths in simply connected charts -/

/-- Two paths contained in a simply connected subset are homotopic. -/
theorem SimplyConnectedCover.homotopic_of_mem {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s)
    (hq : ∀ t, q t ∈ s) : Path.Homotopic p q := by
  let : SimplyConnectedSpace s := hs
  have hx : x ∈ s := by simpa using hp 0
  have hy : y ∈ s := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let q' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have h :=
    (SimplyConnectedSpace.paths_homotopic p' q').map
      (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap s X)
  have hp' : p'.map continuous_subtype_val = p := by ext t; rfl
  have hq' : q'.map continuous_subtype_val = q := by ext t; rfl
  exact hp' ▸ hq' ▸ h

/-- The concatenation of two paths contained in a set stays in the set. -/
theorem SimplyConnectedCover.trans_mem {X : Type*} [TopologicalSpace X] {s : Set X} {x y z : X}
    (p : Path x y) (q : Path y z) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ∀ t, p.trans q t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [Path.trans_range]
  exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hq)

/-- A chosen path from the basepoint to `x` inside the simply connected chart `U i`. -/
def SimplyConnectedCover.chartPath {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i) (i : ι) (x : X)
    (hx : x ∈ U i) : Path o x :=
  ((hs i).isPathConnected.joinedIn o (ho i) x hx).somePath

/-- The chosen chart path stays inside its chart. -/
theorem SimplyConnectedCover.chartPath_mem {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i) (i : ι)
    (x : X) (hx : x ∈ U i) (t : (unitInterval)) : chartPath U hs o ho i x hx t ∈ U i :=
  JoinedIn.somePath_mem _ t

/-- Chart paths to the same point through different charts agree up to homotopy when intersections are path connected. -/
theorem SimplyConnectedCover.chartPath_homotopic {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) (i j : ι) (x : X) (hi : x ∈ U i)
    (hj : x ∈ U j) : Path.Homotopic (chartPath U hs o ho i x hi) (chartPath U hs o ho j x hj) := by
  let h := (hinter i j).joinedIn o ⟨ho i, ho j⟩ x ⟨hi, hj⟩
  exact
    (homotopic_of_mem (hs i) _ h.somePath (chartPath_mem U hs o ho i x hi)
          (fun t => (h.somePath_mem t).1)).trans
      (homotopic_of_mem (hs j) h.somePath _ (fun t => (h.somePath_mem t).2)
        (chartPath_mem U hs o ho j x hj))

/-- Casting a transitivity of path-homotopy classes along endpoint equalities splits into the transitivity of the casts. -/
theorem SimplyConnectedCover.quotient_cast_trans {X : Type*} [TopologicalSpace X]
    {o x y o' x' y' : X} (p : Path.Homotopic.Quotient o x) (q : Path.Homotopic.Quotient x y)
    (ho : o' = o) (hx : x' = x) (hy : y' = y) :
    (p.trans q).cast ho hy = (p.cast ho hx).trans (q.cast hx hy) := by
  cases ho
  cases hx
  cases hy
  simp

/-- A section of path-homotopy classes commutes with casting along an equality of endpoints. -/
theorem SimplyConnectedCover.quotient_cast_section {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) {x y : X} (h : x = y) : (F y).cast rfl h = F x := by
  cases h
  simp

/-- Section transitivity along a full path follows from the hypothesis on the unit subpath. -/
theorem SimplyConnectedCover.section_subpath_zero_one {X : Type*} [TopologicalSpace X] {o x y : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) (p : Path x y)
    (h :
      Path.Homotopic.Quotient.trans (F (p 0)) (Path.Homotopic.Quotient.mk (p.subpath 0 1)) =
        F (p 1)) :
    Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y := by
  have hp :
    (Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm p.target.symm =
      Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_cast, Path.subpath_zero_one]
    rfl
  have h' := congrArg (fun q : Path.Homotopic.Quotient o (p 1) => q.cast rfl p.target.symm) h
  rw [quotient_cast_trans _ _ rfl p.source.symm p.target.symm,
    quotient_cast_section F p.source.symm, hp, quotient_cast_section F p.target.symm] at h'
  exact h'

/-- Path-homotopy-class sections that are transitive inside each chart of a simply connected open cover are transitive along all paths. -/
theorem SimplyConnectedCover.section_trans_of_open_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (o : X)
    (F : ∀ x, Path.Homotopic.Quotient o x)
    (hF :
      ∀ i {x y : X} (p : Path x y),
        (∀ t, p t ∈ U i) →
          Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y)
    {x y : X} (p : Path x y) :
    Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y := by
  have hpre : Set.univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i => (hopen i).preimage p.continuous)
      hpre
  have hwalk :
    ∀ k : ℕ,
      Path.Homotopic.Quotient.trans (F (p 0)) (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))) =
        F (p (t k)) := by
    intro k
    induction k with
    | zero =>
      rw [ht0, Path.subpath_self, Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.trans_refl]
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : ∀ s, p.subpath (t k) (t (k + 1)) s ∈ U i := by
        apply Set.range_subset_iff.mp
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact Set.image_subset_iff.mpr hi
      have hconcat :
        Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (p.subpath 0 (t k)))
            (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
          Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      calc
        Path.Homotopic.Quotient.trans (F (p 0))
              (Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1)))) =
            Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.trans (F (p 0))
                (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))))
              (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) := by
          rw [Path.Homotopic.Quotient.trans_assoc, hconcat]
        _ =
            Path.Homotopic.Quotient.trans (F (p (t k)))
              (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) := by rw [ih]
        _ = F (p (t (k + 1))) := hF i _ hmem
  have h := hwalk n
  rw [hn n le_rfl] at h
  exact section_subpath_zero_one F p h
end Mathoverflow1973
