/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.FundamentalGroup.SimplyConnectedCover
/-!
# The two-sheeted simply connected cover over a two-open cover

  The two-sheeted simply connected cover attached to a two-open van Kampen cover:
  based sections, sheet membership, and the path-lifting lemmas used to split the
  fundamental group action (Hatcher, Algebraic Topology, Section 1.3).
-/



open Set Function Filter Manifold Topology

noncomputable section

/-! ### Induction on path-homotopy classes -/

/-- Properties of path-homotopy classes are stable under endpoint casts. -/
theorem TriangleRegularBaseFundamentalGroup.pathClass_property_cast {X : Type*}
    [TopologicalSpace X] (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop) {x y x' y' : X}
    (q : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) (hq : P q) : P (q.cast hx hy) :=
  by
  cases hx
  cases hy
  simpa using hq

/-- A property holding at reflexivity, under transitivity, and inside each chart of an open cover holds of all path classes. -/
theorem TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop)
    (h_refl : ∀ x, P (Path.Homotopic.Quotient.refl x))
    (h_trans :
      ∀ {x y z : X} {p : Path.Homotopic.Quotient x y} {q : Path.Homotopic.Quotient y z},
        P p → P q → P (p.trans q))
    (h_local :
      ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i → P (Path.Homotopic.Quotient.mk p)) :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y), P q := by
  intro x y q
  obtain ⟨p⟩ := q
  have hpre : Set.univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i => (hopen i).preimage p.continuous)
      hpre
  have hwalk : ∀ k : ℕ, P (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))) := by
    intro k
    induction k with
    | zero =>
      rw [ht0, Path.subpath_self, Path.Homotopic.Quotient.mk_refl]
      exact h_refl (p 0)
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : Set.range (p.subpath (t k) (t (k + 1))) ⊆ U i := by
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact Set.image_subset_iff.mpr hi
      have hconcat :
        Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (p.subpath 0 (t k)))
            (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
          Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      rw [← hconcat]
      exact h_trans ih (h_local i _ hmem)
  have hfull := hwalk n
  rw [hn n le_rfl] at hfull
  have hp :
    (Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm p.target.symm =
      Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_cast, Path.subpath_zero_one]
    rfl
  have htransport := pathClass_property_cast P _ p.source.symm p.target.symm hfull
  rwa [hp] at htransport

/-- Cancelling a class on the left by its inverse inside a transitivity. -/
theorem TriangleRegularBaseFundamentalGroup.quotient_symm_trans_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- Right cancellation of a common transitivity factor in path classes. -/
theorem TriangleRegularBaseFundamentalGroup.quotient_trans_right_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} {p q : Path.Homotopic.Quotient x y}
    (r : Path.Homotopic.Quotient y z) (h : p.trans r = q.trans r) : p = q := by
  have h' := congrArg (fun a : Path.Homotopic.Quotient x z => a.trans r.symm) h
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using h'

/-! ### Loop classes from a section -/

/-- The based loop `F x · p · (F y)⁻¹` of a path class against a section `F`. -/
def TriangleRegularBaseFundamentalGroup.basedLoop {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ x, Path.Homotopic.Quotient o x) {x y : X} (p : Path.Homotopic.Quotient x y) :
    FundamentalGroup X o :=
  ((F x).trans p).trans (F y).symm

/-- The based loop `p · q⁻¹` comparing two classes to the same point. -/
def TriangleRegularBaseFundamentalGroup.pathDifference {X : Type*} [TopologicalSpace X] {o x : X}
    (p q : Path.Homotopic.Quotient o x) : FundamentalGroup X o :=
  p.trans q.symm

/-- The based loop of the trivial class is trivial. -/
@[simp]
theorem TriangleRegularBaseFundamentalGroup.basedLoop_refl {X : Type*} [TopologicalSpace X]
    {o : X} (F : ∀ x, Path.Homotopic.Quotient o x) (x : X) :
    basedLoop F (Path.Homotopic.Quotient.refl x) = 1 := by
  simp only [basedLoop, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def]

/-- The based loop map reverses transitivity into multiplication. -/
theorem TriangleRegularBaseFundamentalGroup.basedLoop_trans {X : Type*} [TopologicalSpace X]
    {o x y z : X} (F : ∀ x, Path.Homotopic.Quotient o x) (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : basedLoop F (p.trans q) = basedLoop F q * basedLoop F p :=
  by
  simp only [basedLoop, FundamentalGroup.mul_def, Path.Homotopic.Quotient.trans_assoc,
    quotient_symm_trans_cancel]

/-- The based loop of `p` expressed through the path differences of `a` and `b`. -/
theorem TriangleRegularBaseFundamentalGroup.basedLoop_comparison {X : Type*} [TopologicalSpace X]
    {o x y : X} (F : ∀ z, Path.Homotopic.Quotient o z) (a : Path.Homotopic.Quotient o x)
    (b : Path.Homotopic.Quotient o y) (p : Path.Homotopic.Quotient x y) (h : a.trans p = b) :
    basedLoop F p = (pathDifference (F y) b)⁻¹ * pathDifference (F x) a := by
  apply
    (@eq_inv_mul_iff_mul_eq (FundamentalGroup X o) _ (basedLoop F p) (pathDifference (F y) b)
        (pathDifference (F x) a)).2
  apply quotient_trans_right_cancel b
  simp only [basedLoop, pathDifference, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc, quotient_symm_trans_cancel,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  rw [← h, quotient_symm_trans_cancel]

/-! ### The two-chart simply connected cover -/

/-- A two-open-set cover by simply connected pieces with path-connected intersection and a common basepoint. -/
structure TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover (X : Type*)
    [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = Set.univ
  simplyU : IsSimplyConnected (U : Set X)
  simplyV : IsSimplyConnected (V : Set X)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

/-- A chosen basepoint-to-`x` path inside `U`. -/
def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathU {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.U) : Path D.base x :=
  (D.simplyU.isPathConnected.joinedIn D.base D.baseU x hx).somePath

/-- A chosen basepoint-to-`x` path inside `V`. -/
def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathV {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.V) : Path D.base x :=
  (D.simplyV.isPathConnected.joinedIn D.base D.baseV x hx).somePath

/-- The chosen `U`-path stays inside `U`. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathU_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.U) (t : (unitInterval)) : D.pathU x hx t ∈ D.U :=
  JoinedIn.somePath_mem _ t

/-- The chosen `V`-path stays inside `V`. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathV_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.V) (t : (unitInterval)) : D.pathV x hx t ∈ D.V :=
  JoinedIn.somePath_mem _ t

/-- Chosen `U`-paths are transitive along paths inside `U`. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathU_trans {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x y : X} (hx : x ∈ D.U) (hy : y ∈ D.U) (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    (Path.Homotopic.Quotient.mk (D.pathU x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathU y hy) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  exact
    SimplyConnectedCover.homotopic_of_mem D.simplyU _ _
      (SimplyConnectedCover.trans_mem _ _ (D.pathU_mem x hx) hp) (D.pathU_mem y hy)

/-- Chosen `V`-paths are transitive along paths inside `V`. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathV_trans {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x y : X} (hx : x ∈ D.V) (hy : y ∈ D.V) (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    (Path.Homotopic.Quotient.mk (D.pathV x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathV y hy) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  exact
    SimplyConnectedCover.homotopic_of_mem D.simplyV _ _
      (SimplyConnectedCover.trans_mem _ _ (D.pathV_mem x hx) hp) (D.pathV_mem y hy)

/-- The loop class comparing the `U`- and `V`-paths to an overlap point. -/
def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hxU : x ∈ D.U) (hxV : x ∈ D.V) : FundamentalGroup X D.base :=
  (Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
    (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm

/-- The switch class is constant on joined points of the overlap. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass_eq_of_joinedIn
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) {x y : X} (hxU : x ∈ D.U)
    (hxV : x ∈ D.V) (hyU : y ∈ D.U) (hyV : y ∈ D.V) (hxy : JoinedIn ((D.U : Set X) ∩ D.V) x y) :
    D.switchClass x hxU hxV = D.switchClass y hyU hyV := by
  let p := hxy.somePath
  have hU := D.pathU_trans hxU hyU p (fun t => (hxy.somePath_mem t).1)
  have hV := D.pathV_trans hxV hyV p (fun t => (hxy.somePath_mem t).2)
  apply
    TriangleRegularBaseFundamentalGroup.quotient_trans_right_cancel
      (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  change
    ((Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
            (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV)) =
      ((Path.Homotopic.Quotient.mk (D.pathU y hyU)).trans
            (Path.Homotopic.Quotient.mk (D.pathV y hyV)).symm).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  rw [Path.Homotopic.Quotient.trans_assoc, ← hV,
    TriangleRegularBaseFundamentalGroup.quotient_symm_trans_cancel, hU]
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- The switch class at the basepoint is trivial. -/
@[simp]
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass_base {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) :
    D.switchClass D.base D.baseU D.baseV = 1 := by
  have hU :
    Path.Homotopic.Quotient.mk (D.pathU D.base D.baseU) = Path.Homotopic.Quotient.refl D.base := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem _ _) (fun _ => D.baseU)
  have hV :
    Path.Homotopic.Quotient.mk (D.pathV D.base D.baseV) = Path.Homotopic.Quotient.refl D.base := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact SimplyConnectedCover.homotopic_of_mem D.simplyV _ _ (D.pathV_mem _ _) (fun _ => D.baseV)
  simp only [switchClass, hU, hV, Path.Homotopic.Quotient.trans_symm, FundamentalGroup.one_def]

/-- A point outside `U` lies in `V`. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.memV_of_not_memU {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x : X} (hx : x ∉ D.U) : x ∈ D.V := by
  have h : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact h.resolve_left hx

/-- A basepoint section of path classes using the `U`-path on `U` and the `V`-path elsewhere. -/
def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) : Path.Homotopic.Quotient D.base x := by
  classical
    exact
    if hx : x ∈ D.U then Path.Homotopic.Quotient.mk (D.pathU x hx)
    else Path.Homotopic.Quotient.mk (D.pathV x (D.memV_of_not_memU hx))

/-- On `U` the section is the chosen `U`-path class. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection_eq_U {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x : X} (hx : x ∈ D.U) : D.basedSection x = Path.Homotopic.Quotient.mk (D.pathU x hx) := by
  simp only [basedSection, dif_pos hx]

/-- Off `U` the section is the chosen `V`-path class. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection_eq_V {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x : X} (hxU : x ∉ D.U) (hxV : x ∈ D.V) :
    D.basedSection x = Path.Homotopic.Quotient.mk (D.pathV x hxV) := by
  simp only [basedSection, dif_neg hxU]

/-- The section at the basepoint is the trivial class. -/
@[simp]
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection_base {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) :
    D.basedSection D.base = Path.Homotopic.Quotient.refl D.base := by
  rw [D.basedSection_eq_U D.baseU]
  apply Path.Homotopic.Quotient.eq.mpr
  exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem _ _) (fun _ => D.baseU)

/-- The path difference against the `U`-path lies in any subgroup containing the switch classes. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.comparisonU_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base)) {x : X} (hx : x ∈ D.U) :
    TriangleRegularBaseFundamentalGroup.pathDifference (D.basedSection x)
        (Path.Homotopic.Quotient.mk (D.pathU x hx)) ∈
      H := by
  rw [D.basedSection_eq_U hx]
  simpa only [TriangleRegularBaseFundamentalGroup.pathDifference,
    Path.Homotopic.Quotient.trans_symm, FundamentalGroup.one_def] using H.one_mem

/-- The path difference against the `V`-path lies in any subgroup containing the switch classes. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.comparisonV_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) {x : X}
    (hx : x ∈ D.V) :
    TriangleRegularBaseFundamentalGroup.pathDifference (D.basedSection x)
        (Path.Homotopic.Quotient.mk (D.pathV x hx)) ∈
      H := by
  by_cases hxU : x ∈ D.U
  · rw [D.basedSection_eq_U hxU]
    exact hH x hxU hx
  · rw [D.basedSection_eq_V hxU hx]
    simpa only [TriangleRegularBaseFundamentalGroup.pathDifference,
      Path.Homotopic.Quotient.trans_symm, FundamentalGroup.one_def] using H.one_mem

/-- The based loop of a path inside `U` lies in the subgroup. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedLoop_mem_of_path_in_U
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base)) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈
      H := by
  have hx : x ∈ D.U := by simpa using hp 0
  have hy : y ∈ D.U := by simpa using hp 1
  rw [TriangleRegularBaseFundamentalGroup.basedLoop_comparison D.basedSection
      (Path.Homotopic.Quotient.mk (D.pathU x hx)) (Path.Homotopic.Quotient.mk (D.pathU y hy))
      (Path.Homotopic.Quotient.mk p) (D.pathU_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonU_mem H hy)) (D.comparisonU_mem H hx)

/-- The based loop of a path inside `V` lies in the subgroup containing the switch classes. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedLoop_mem_of_path_in_V
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) {x y : X}
    (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈
      H := by
  have hx : x ∈ D.V := by simpa using hp 0
  have hy : y ∈ D.V := by simpa using hp 1
  rw [TriangleRegularBaseFundamentalGroup.basedLoop_comparison D.basedSection
      (Path.Homotopic.Quotient.mk (D.pathV x hx)) (Path.Homotopic.Quotient.mk (D.pathV y hy))
      (Path.Homotopic.Quotient.mk p) (D.pathV_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonV_mem H hH hy)) (D.comparisonV_mem H hH hx)

/-- A subgroup of the fundamental group containing all switch classes is everything. -/
theorem
  TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.subgroup_eq_top_of_switchClass_mem
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) : H = ⊤ := by
  let W : Bool → Set X := fun b => if b then D.V else D.U
  have hopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact D.U.isOpen
    · exact D.V.isOpen
  have hcover : ⋃ b, W b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩
  have hall :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection q ∈ H := by
    apply
      TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover W hopen hcover
        (fun q => TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection q ∈ H)
    · intro x
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_refl]
      exact H.one_mem
    · intro x y z p q hp hq
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_trans]
      exact H.mul_mem hq hp
    · intro b x y p hp
      cases b
      · exact D.basedLoop_mem_of_path_in_U H p (fun t => hp ⟨t, rfl⟩)
      · exact D.basedLoop_mem_of_path_in_V H hH p (fun t => hp ⟨t, rfl⟩)
  apply top_unique
  intro q _
  have hq := hall q
  have hrefl : (Path.Homotopic.Quotient.refl D.base).symm = Path.Homotopic.Quotient.refl D.base :=
    by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  simpa only [TriangleRegularBaseFundamentalGroup.basedLoop, D.basedSection_base,
    Path.Homotopic.Quotient.refl_trans, hrefl, Path.Homotopic.Quotient.trans_refl] using hq

/-- The switch class equals the loop formed by any `U`-path followed by the reverse of any `V`-path. -/
theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass_eq_of_paths
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) {x : X} (hxU : x ∈ D.U)
    (hxV : x ∈ D.V) (p q : Path D.base x) (hp : ∀ t, p t ∈ D.U) (hq : ∀ t, q t ∈ D.V) :
    D.switchClass x hxU hxV =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.trans q.symm)) := by
  have hU : Path.Homotopic.Quotient.mk (D.pathU x hxU) = Path.Homotopic.Quotient.mk p :=
    Path.Homotopic.Quotient.eq.mpr
      (SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem x hxU) hp)
  have hV : Path.Homotopic.Quotient.mk (D.pathV x hxV) = Path.Homotopic.Quotient.mk q :=
    Path.Homotopic.Quotient.eq.mpr
      (SimplyConnectedCover.homotopic_of_mem D.simplyV _ _ (D.pathV_mem x hxV) hq)
  simp only [switchClass, hU, hV, FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
