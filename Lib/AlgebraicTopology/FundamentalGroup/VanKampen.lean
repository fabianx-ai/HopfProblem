/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.FundamentalGroup.TwoSimplyConnectedCover
import Lib.AlgebraicTopology.FundamentalGroup.SimplyConnectedCover
/-!
# The Seifert-van Kampen theorem for a two-open cover

  The Seifert-van Kampen theorem for a two-open cover in pushout form: the
  fundamental group of `U cup V` (both open, `U cap V` path connected, common
  base point) is the amalgamated free product of `pi_1 U` and `pi_1 V` over
  `pi_1 (U cap V)`, including the uniqueness half (Hatcher, Algebraic Topology,
  Theorem 1.20).
-/

open Set Function Filter Manifold Topology

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Local and global path values -/

/-- A subpath of a path staying in `s` on `Icc a b` stays in `s`. -/
theorem FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t ∈ Set.Icc a b, p t ∈ s) : ∀ t, p.subpath a b t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [p.range_subpath_of_le a b hab]
  exact Set.image_subset_iff.mpr hp

/-- A path value: a family of paths indexed by a type ι, together with the data that each lies in a designated open set — the local half of a van Kampen decomposition. -/
structure FundamentalGroup.VanKampen.LocalPathValue {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (G : Type*) [Group G] where
  value : ∀ i {x y : X} (p : Path x y), (∀ t, p t ∈ U i) → G
  refl : ∀ i (x : X) (hx : ∀ t, Path.refl x t ∈ U i), value i (Path.refl x) hx = 1
  trans :
    ∀ i {x y z : X} (p : Path x y) (q : Path y z) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
      (hpq : ∀ t, p.trans q t ∈ U i), value i (p.trans q) hpq = value i p hp * value i q hq
  subpath_mul :
    ∀ i {x y : X} (p : Path x y) (a b c : (unitInterval)) (_ : a ≤ b) (_ : b ≤ c)
      (hab : ∀ t, p.subpath a b t ∈ U i) (hbc : ∀ t, p.subpath b c t ∈ U i)
      (hac : ∀ t, p.subpath a c t ∈ U i),
      value i (p.subpath a c) hac = value i (p.subpath a b) hab * value i (p.subpath b c) hbc
  compatible :
    ∀ i j {x y : X} (p : Path x y) (hi : ∀ t, p t ∈ U i) (hj : ∀ t, p t ∈ U j),
      value i p hi = value j p hj

/-- Local path values are unchanged by endpoint casts. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.value_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (i : ι) {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hp : ∀ t, p t ∈ U i) (hp' : ∀ t, p.cast hx hy t ∈ U i) :
    L.value i (p.cast hx hy) hp' = L.value i p hp := by
  cases hx
  cases hy
  rfl

/-- A local path value is homotopy invariant when it agrees on homotopic paths within a chart. -/
def FundamentalGroup.VanKampen.LocalPathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
    (H : Path.Homotopy p q), (∀ s, H s ∈ U i) → L.value i p hp = L.value i q hq

/-- A path value into a group: a path in `X` together with the requirement that homotopic paths take the same value in `G` — the lemma-bearing wrapper for the van Kampen amalgamation. -/
structure FundamentalGroup.VanKampen.PathValue (X : Type*) [TopologicalSpace X] (G : Type*)
    [Group G] where
  value : ∀ {x y : X}, Path x y → G
  refl : ∀ x, value (Path.refl x) = 1
  trans : ∀ {x y z : X} (p : Path x y) (q : Path y z), value (p.trans q) = value p * value q
  subpath_mul :
    ∀ {x y : X} (p : Path x y) (a b c : (unitInterval)),
      a ≤ b → b ≤ c → value (p.subpath a c) = value (p.subpath a b) * value (p.subpath b c)

/-- A global path value is unchanged by endpoint casts. -/
theorem FundamentalGroup.VanKampen.PathValue.value_cast {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) {x y x' y' : X}
    (p : Path x y) (hx : x' = x) (hy : y' = y) : V.value (p.cast hx hy) = V.value p := by
  cases hx
  cases hy
  rfl

/-- Restricting to the whole interval recovers the value. -/
@[simp]
theorem FundamentalGroup.VanKampen.PathValue.value_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    {x y : X} (p : Path x y) : V.value (p.subpath 0 1) = V.value p := by
  rw [Path.subpath_zero_one, V.value_cast]

/-- A global path value extends a local one when they agree on paths inside each chart. -/
def FundamentalGroup.VanKampen.PathValue.Extends {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i), V.value p = L.value i p hp

/-- A path value is homotopy invariant when homotopic paths have equal values. -/
def FundamentalGroup.VanKampen.PathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) : Prop :=
  ∀ {x y : X} (p q : Path x y), Path.Homotopic p q → V.value p = V.value q

/-- A two-open van Kampen cover: open sets `U`, `V` covering `X`, all three of `U`, `V`, `U ∩ V` path connected, with a common base point lying in both (Hatcher, Algebraic Topology, Theorem 1.20 setup). -/
structure FundamentalGroup.VanKampen.TwoOpenCover (X : Type*) [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = Set.univ
  pathConnectedU : IsPathConnected (U : Set X)
  pathConnectedV : IsPathConnected (V : Set X)
  pathConnectedIntersection : IsPathConnected ((U : Set X) ∩ V)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

/-! ### The two-open cover setup -/

/-- The `Bool`-indexed pair of open charts. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : Bool → TopologicalSpace.Opens X
  | false => D.U
  | true => D.V

/-- The basepoint lies in each chart. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.base_mem_chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) : D.base ∈ D.chart i := by
  cases i
  · exact D.baseU
  · exact D.baseV

/-- Each chart is open. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.chart_open {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) : IsOpen (D.chart i : Set X) :=
  (D.chart i).isOpen

/-- The two charts cover the space. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.chart_cover {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : ⋃ i, (D.chart i : Set X) = Set.univ := by
  apply subset_antisymm (Set.subset_univ _)
  intro x _
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩

/-- Every point lies in `U` or `V`. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.mem_U_or_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : X) : x ∈ D.U ∨ x ∈ D.V := by
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact hx

/-- A chosen basepoint-to-`x` path inside whichever chart contains `x`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.rawPathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical
    exact
    if h : x ∈ (D.U : Set X) ∩ D.V then
      (D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath
    else
      if hU : x ∈ D.U then (D.pathConnectedU.joinedIn D.base D.baseU x hU).somePath
      else
        (D.pathConnectedV.joinedIn D.base D.baseV x ((D.mem_U_or_V x).resolve_left hU)).somePath

/-- The chosen path stays inside the chart containing its endpoint. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.rawPathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.rawPathTo x t ∈ D.chart i := by
  classical
    cases i with
  | false =>
    change D.rawPathTo x t ∈ D.U
    change x ∈ D.U at hx
    unfold rawPathTo
    by_cases h : x ∈ (D.U : Set X) ∩ D.V
    · rw [dif_pos h]
      exact
        ((D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).1
    · rw [dif_neg h, dif_pos hx]
      exact JoinedIn.somePath_mem _ t
  | true =>
    change D.rawPathTo x t ∈ D.V
    change x ∈ D.V at hx
    unfold rawPathTo
    by_cases h : x ∈ (D.U : Set X) ∩ D.V
    · rw [dif_pos h]
      exact
        ((D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).2
    · have hnU : x ∉ D.U := fun hU => h ⟨hU, hx⟩
      rw [dif_neg h, dif_neg hnU]
      exact JoinedIn.somePath_mem _ t

/-- The chosen basepoint path, normalized to be constant at the basepoint. -/
def FundamentalGroup.VanKampen.TwoOpenCover.pathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical exact if h : x = D.base then (Path.refl D.base).cast rfl h else D.rawPathTo x

/-- The chosen path at the basepoint is the constant path. -/
@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.pathTo_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.pathTo D.base = Path.refl D.base := by
  classical simp [pathTo]

/-- The normalized path stays inside the chart containing its endpoint. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.pathTo x t ∈ D.chart i := by
  classical
  unfold pathTo
  split_ifs
  · exact D.base_mem_chart i
  · exact D.rawPathTo_mem i x hx t

/-- The intersection `U ∩ V` as an open set. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.overlap {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : TopologicalSpace.Opens X :=
  D.U ⊓ D.V

/-- The basepoint viewed in `U`. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseUPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.U :=
  ⟨D.base, D.baseU⟩

/-- The basepoint viewed in `V`. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseVPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.V :=
  ⟨D.base, D.baseV⟩

/-- The basepoint viewed in the overlap. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseOverlapPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.overlap :=
  ⟨D.base, D.baseU, D.baseV⟩

/-- The basepoint viewed in chart `i`. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseChart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) : D.chart i :=
  ⟨D.base, D.base_mem_chart i⟩

/-- The fundamental group of `U` at the basepoint. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.UGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  FundamentalGroup D.U D.baseUPoint

/-- The fundamental group of `V` at the basepoint. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.VGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  FundamentalGroup D.V D.baseVPoint

/-- The fundamental group of the overlap at the basepoint. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.OverlapGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  FundamentalGroup D.overlap D.baseOverlapPoint

/-- The inclusion of the overlap into `U`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapToU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.overlap, D.U) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of the overlap into `V`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapToV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.overlap, D.V) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of `U` into `X`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.inclusionU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of `V` into `X`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.inclusionV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.V, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The fundamental-group map induced by the overlap inclusion into `U`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.OverlapGroup →* D.UGroup :=
  FundamentalGroup.map D.overlapToU D.baseOverlapPoint

/-- The fundamental-group map induced by the overlap inclusion into `V`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.OverlapGroup →* D.VGroup :=
  FundamentalGroup.map D.overlapToV D.baseOverlapPoint

/-- The fundamental-group map induced by the `U` inclusion. -/
def FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.UGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionU D.baseUPoint

/-- The fundamental-group map induced by the `V` inclusion. -/
def FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.VGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionV D.baseVPoint

/-- The two routes from the overlap to the ambient group agree. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.inclusionHomU.comp D.overlapHomU = D.inclusionHomV.comp D.overlapHomV := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Maps `fU` and `fV` are compatible when they agree on overlap classes. -/
def FundamentalGroup.VanKampen.TwoOpenCover.Compatible {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) {G : Type*} [Group G] (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) : Prop :=
  fU.comp D.overlapHomU = fV.comp D.overlapHomV

/-! ### Paths inside a subset -/

/-- A path lying in `S` viewed as a path inside `S`. -/
def FundamentalGroup.VanKampen.pathIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩
    where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- The subspace path computes as the ambient path. -/
@[simp]
theorem FundamentalGroup.VanKampen.pathIn_apply {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (t : (unitInterval)) :
    (pathIn p hx hy hp t : X) = p t :=
  rfl

/-- Mapping the subspace path out recovers the ambient path. -/
@[simp]
theorem FundamentalGroup.VanKampen.pathIn_map {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) :
    (pathIn p hx hy hp).map continuous_subtype_val = p := by
  ext t
  rfl

/-- The constant path inside `S` is constant. -/
@[simp]
theorem FundamentalGroup.VanKampen.pathIn_refl {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (hx : x ∈ S) (hp : ∀ t, Path.refl x t ∈ S) :
    pathIn (Path.refl x) hx hx hp = Path.refl (⟨x, hx⟩ : S) := by
  ext t
  rfl

/-- Concatenation inside `S` computes inside `S`. -/
@[simp]
theorem FundamentalGroup.VanKampen.pathIn_trans {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y z : X} (p : Path x y) (q : Path y z) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (hpq : ∀ t, p.trans q t ∈ S) :
    pathIn (p.trans q) hx hz hpq = (pathIn p hx hy hp).trans (pathIn q hy hz hq) := by
  ext t
  simp only [pathIn_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- A homotopy inside `S` descends to a homotopy of subspace paths. -/
def FundamentalGroup.VanKampen.homotopyIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p q : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (H : Path.Homotopy p q) (hH : ∀ s, H s ∈ S) :
    Path.Homotopy (pathIn p hx hy hp) (pathIn q hx hy hq)
    where
  toFun s := ⟨H s, hH s⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.apply_zero t)
  map_one_left t := Subtype.ext (H.apply_one t)
  prop' s _t ht := Subtype.ext (H.eq_fst s ht)

/-- The composite of two `S`-valued homotopies stays in `S`. -/
theorem FundamentalGroup.VanKampen.homotopy_trans_mem {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} {p q r : Path x y} (H : Path.Homotopy p q) (K : Path.Homotopy q r)
    (hH : ∀ s, H s ∈ S) (hK : ∀ s, K s ∈ S) : ∀ s, H.trans K s ∈ S := by
  intro s
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

/-- The transRefl homotopy stays in `S` along an `S`-path. -/
theorem FundamentalGroup.VanKampen.homotopy_transRefl_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ S) :
    ∀ s, Path.Homotopy.transRefl p s ∈ S := by
  intro s
  exact hp _

/-- The subpath-transitivity-refl homotopy stays in `S`. -/
theorem FundamentalGroup.VanKampen.homotopy_subpathTransSubpathRefl_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpathRefl p a b c s ∈ S := by
  intro s
  let m := Set.Icc.convexComb b c s.1
  have ham : a ≤ m := hab.trans (Set.Icc.le_convexComb hbc s.1)
  have hmc : m ≤ c := Set.Icc.convexComb_le hbc s.1
  change ((p.subpath a m).trans (p.subpath m c)) s.2 ∈ S
  apply SimplyConnectedCover.trans_mem
  · exact subpath_mem_of_mem_Icc p ham (fun t ht => hp t ⟨ht.1, ht.2.trans hmc⟩)
  · exact subpath_mem_of_mem_Icc p hmc (fun t ht => hp t ⟨ham.trans ht.1, ht.2⟩)

/-- The subpath-transitivity homotopy stays in `S`. -/
theorem FundamentalGroup.VanKampen.homotopy_subpathTransSubpath_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpath p a b c s ∈ S :=
  homotopy_trans_mem _ _ (homotopy_subpathTransSubpathRefl_mem p a b c hab hbc hp)
    (homotopy_transRefl_mem _ (subpath_mem_of_mem_Icc p (hab.trans hbc) hp))

/-- Subpaths staying in `S` mean the original path stays in `S` on the interval. -/
theorem FundamentalGroup.VanKampen.mem_Icc_of_subpath_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b)
    (hp : ∀ t, p.subpath a b t ∈ S) : ∀ t ∈ Set.Icc a b, p t ∈ S := by
  have hr := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hr
  intro t ht
  exact hr ⟨t, ht, rfl⟩

/-- The subpath-transitivity homotopy carried out inside `S`. -/
def FundamentalGroup.VanKampen.subpathTransSubpathIn {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (ha : p a ∈ S)
    (hb : p b ∈ S) (hc : p c ∈ S) (hpab : ∀ t, p.subpath a b t ∈ S)
    (hpbc : ∀ t, p.subpath b c t ∈ S) (hpac : ∀ t, p.subpath a c t ∈ S) :
    Path.Homotopy ((pathIn (p.subpath a b) ha hb hpab).trans (pathIn (p.subpath b c) hb hc hpbc))
      (pathIn (p.subpath a c) ha hc hpac) :=
  (homotopyIn _ _ ha hc (SimplyConnectedCover.trans_mem _ _ hpab hpbc) hpac
        (Path.Homotopy.subpathTransSubpath p a b c)
        (homotopy_subpathTransSubpath_mem p a b c hab hbc
          (mem_Icc_of_subpath_mem p (hab.trans hbc) hpac))).cast
    (pathIn_trans _ _ ha hb hc hpab hpbc _) rfl

/-- Homomorphisms out of the fundamental group agree once they agree on both charts. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.hom_ext {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (f g : FundamentalGroup X D.base →* G) (hU : f.comp D.inclusionHomU = g.comp D.inclusionHomU)
    (hV : f.comp D.inclusionHomV = g.comp D.inclusionHomV) : f = g := by
  let F (x : X) : Path.Homotopic.Quotient D.base x := Path.Homotopic.Quotient.mk (D.pathTo x)
  have hlocal :
    ∀ (i : Bool) {x y : X} (p : Path x y),
      (∀ t, p t ∈ D.chart i) →
        f (TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)) =
          g (TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)) := by
    intro i x y p hp
    have hx : x ∈ D.chart i := by simpa using hp 0
    have hy : y ∈ D.chart i := by simpa using hp 1
    let l : Path D.base D.base := ((D.pathTo x).trans p).trans (D.pathTo y).symm
    have hl : ∀ t, l t ∈ D.chart i :=
      SimplyConnectedCover.trans_mem _ _
        (SimplyConnectedCover.trans_mem _ _ (D.pathTo_mem i x hx) hp)
        (fun t => D.pathTo_mem i y hy (unitInterval.symm t))
    let l' : Path (D.baseChart i) (D.baseChart i) :=
      FundamentalGroup.VanKampen.pathIn l (D.base_mem_chart i) (D.base_mem_chart i) hl
    have hmap :
      (Path.Homotopic.Quotient.mk l').map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(D.chart i, X)) =
        TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p) := by
      change
        Path.Homotopic.Quotient.mk (l'.map continuous_subtype_val) =
          TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)
      rw [show l'.map continuous_subtype_val = l from
          FundamentalGroup.VanKampen.pathIn_map _ _ _ _]
      rfl
    cases i with
    | false =>
      have h := DFunLike.congr_fun hU (Path.Homotopic.Quotient.mk l')
      exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
    | true =>
      have h := DFunLike.congr_fun hV (Path.Homotopic.Quotient.mk l')
      exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
  have hall :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      f (TriangleRegularBaseFundamentalGroup.basedLoop F q) =
        g (TriangleRegularBaseFundamentalGroup.basedLoop F q) := by
    apply
      TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover
        (fun i => (D.chart i : Set X)) D.chart_open D.chart_cover
        (fun q =>
          f (TriangleRegularBaseFundamentalGroup.basedLoop F q) =
            g (TriangleRegularBaseFundamentalGroup.basedLoop F q))
    · intro x
      simp only [TriangleRegularBaseFundamentalGroup.basedLoop_refl, map_one]
    · intro x y z p q hp hq
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_trans, map_mul, map_mul, hp, hq]
    · intro i x y p hp
      exact hlocal i p (Set.range_subset_iff.mp hp)
  have hbase : F D.base = Path.Homotopic.Quotient.refl D.base := by
    simp only [F, D.pathTo_base, Path.Homotopic.Quotient.mk_refl]
  have hsymm : (Path.Homotopic.Quotient.refl D.base).symm = Path.Homotopic.Quotient.refl D.base :=
    by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  apply MonoidHom.ext
  intro q
  simpa only [TriangleRegularBaseFundamentalGroup.basedLoop, hbase,
    Path.Homotopic.Quotient.refl_trans, hsymm, Path.Homotopic.Quotient.trans_refl] using hall q

/-! ### Closing paths through the basepoint -/

/-- A chosen basepoint path to a point of chart `i`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.chartPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path (D.baseChart i) x :=
  FundamentalGroup.VanKampen.pathIn (D.pathTo x.val) (D.base_mem_chart i) x.property
    (D.pathTo_mem i x.val x.property)

/-- The chart path at the basepoint is constant. -/
@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.chartPath_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :
    D.chartPath i (D.baseChart i) = Path.refl (D.baseChart i) := by
  simp only [chartPath, baseChart, D.pathTo_base, FundamentalGroup.VanKampen.pathIn_refl]

/-- The homotopy class of the chart path. -/
def FundamentalGroup.VanKampen.TwoOpenCover.chartPathClass {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path.Homotopic.Quotient (D.baseChart i) x :=
  Path.Homotopic.Quotient.mk (D.chartPath i x)

/-- The chart path class at the basepoint is trivial. -/
@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.chartPathClass_base {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :
    D.chartPathClass i (D.baseChart i) = Path.Homotopic.Quotient.refl (D.baseChart i) := by
  simp only [chartPathClass, D.chartPath_base, Path.Homotopic.Quotient.mk_refl]

/-- A path in chart `i` closed to a loop via the chart paths. -/
def FundamentalGroup.VanKampen.TwoOpenCover.closePath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) {x y : D.chart i} (p : Path x y) :
    FundamentalGroup (D.chart i) (D.baseChart i) :=
  TriangleRegularBaseFundamentalGroup.basedLoop (D.chartPathClass i)
    (Path.Homotopic.Quotient.mk p)

/-- Closing the constant path gives the identity. -/
@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.closePath_refl {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    D.closePath i (Path.refl x) = 1 :=
  TriangleRegularBaseFundamentalGroup.basedLoop_refl _ _

/-- Closing a composite path multiplies in reverse order. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.closePath_trans {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) {x y z : D.chart i} (p : Path x y)
    (q : Path y z) : D.closePath i (p.trans q) = D.closePath i q * D.closePath i p := by
  exact
    TriangleRegularBaseFundamentalGroup.basedLoop_trans (D.chartPathClass i)
      (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q)

/-- Closing depends only on the homotopy class. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.closePath_homotopic {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool)
    {x y : D.chart i} {p q : Path x y} (hpq : Path.Homotopic p q) :
    D.closePath i p = D.closePath i q := by
  unfold closePath
  rw [Path.Homotopic.Quotient.eq.mpr hpq]

/-- Closing a loop at the basepoint returns its class. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.closePath_loop {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool)
    (p : Path (D.baseChart i) (D.baseChart i)) : D.closePath i p = Path.Homotopic.Quotient.mk p :=
  by
  simp only [closePath, TriangleRegularBaseFundamentalGroup.basedLoop, D.chartPathClass_base,
    Path.Homotopic.Quotient.refl_trans]
  exact Path.Homotopic.Quotient.trans_refl _

/-- The homomorphism from the fundamental group of chart `i` to `G` induced by the chosen group element `fU`/`fV` on that side. -/
def FundamentalGroup.VanKampen.TwoOpenCover.chartHom {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) : FundamentalGroup (D.chart i) (D.baseChart i) →* G := by
  cases i
  · exact fU
  · exact fV

/-- The value in `G` that chart `i` assigns to a path `p` staying inside chart `i`: the image of `p` under the chart homomorphism. -/
def FundamentalGroup.VanKampen.TwoOpenCover.localValue {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.chart i) : G :=
  (D.chartHom fU fV i
      (D.closePath i
        (FundamentalGroup.VanKampen.pathIn (S := (D.chart i : Set X)) p (by simpa using hp 0)
          (by simpa using hp 1) hp)))⁻¹

/-- The local value of a constant path is one. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_refl {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) (x : X) (hx : ∀ t, Path.refl x t ∈ D.chart i) :
    D.localValue fU fV i (Path.refl x) hx = 1 := by
  simp only [localValue, FundamentalGroup.VanKampen.pathIn_refl, D.closePath_refl, map_one,
    inv_one]

/-- The local value of a composite path is the product. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_trans {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (hpq : ∀ t, p.trans q t ∈ D.chart i) :
    D.localValue fU fV i (p.trans q) hpq =
      D.localValue fU fV i p hp * D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  have hz : z ∈ D.chart i := by simpa using hq 1
  unfold localValue
  rw [FundamentalGroup.VanKampen.pathIn_trans p q hx hy hz hp hq hpq, D.closePath_trans, map_mul,
    mul_inv_rev]

/-- The local value splits multiplicatively along a subpath decomposition. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y)
    (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (hpab : ∀ t, p.subpath a b t ∈ D.chart i)
    (hpbc : ∀ t, p.subpath b c t ∈ D.chart i) (hpac : ∀ t, p.subpath a c t ∈ D.chart i) :
    D.localValue fU fV i (p.subpath a c) hpac =
      D.localValue fU fV i (p.subpath a b) hpab * D.localValue fU fV i (p.subpath b c) hpbc := by
  have ha : p a ∈ D.chart i := by simpa using hpab 0
  have hb : p b ∈ D.chart i := by simpa using hpab 1
  have hc : p c ∈ D.chart i := by simpa using hpbc 1
  have H :=
    FundamentalGroup.VanKampen.subpathTransSubpathIn p a b c hab hbc ha hb hc hpab hpbc hpac
  unfold localValue
  rw [← D.closePath_homotopic i ⟨H⟩, D.closePath_trans, map_mul, mul_inv_rev]

/-- The local value is invariant under homotopies inside the chart. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (H : Path.Homotopy p q)
    (hH : ∀ s, H s ∈ D.chart i) : D.localValue fU fV i p hp = D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  unfold localValue
  rw [D.closePath_homotopic i ⟨FundamentalGroup.VanKampen.homotopyIn p q hx hy hp hq H hH⟩]

/-- The overlap path: the path through `U ∩ V` witnessing compatibility of the two local values along the cover. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : D.overlap) : Path D.baseOverlapPoint x :=
  FundamentalGroup.VanKampen.pathIn (S := (D.overlap : Set X)) (D.pathTo x.val) ⟨D.baseU, D.baseV⟩
    x.property
    (fun t =>
      ⟨D.pathTo_mem Bool.false x.val x.property.1 t, D.pathTo_mem Bool.true x.val x.property.2 t⟩)

/-- The overlap path mapped into `U` is the chart path. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.overlapPath_map_U {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToU.continuous = D.chartPath Bool.false (D.overlapToU x) := by
  ext t
  rfl

/-- The overlap path mapped into `V` is the chart path. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.overlapPath_map_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToV.continuous = D.chartPath Bool.true (D.overlapToV x) := by
  ext t
  rfl

/-- A path in the overlap closed to an overlap group element. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapClose {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.OverlapGroup :=
  TriangleRegularBaseFundamentalGroup.basedLoop
    (fun x => Path.Homotopic.Quotient.mk (D.overlapPath x)) (Path.Homotopic.Quotient.mk p)

/-- The `U` map of a closed overlap path is its `U` closing. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomU (D.overlapClose p) = D.closePath Bool.false (p.map D.overlapToU.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToU.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.false (D.overlapToU x)).trans (p.map D.overlapToU.continuous)).trans
          (D.chartPath Bool.false (D.overlapToU y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_U, D.overlapPath_map_U]
  rfl

/-- The `V` map of a closed overlap path is its `V` closing. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomV (D.overlapClose p) = D.closePath Bool.true (p.map D.overlapToV.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToV.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.true (D.overlapToV x)).trans (p.map D.overlapToV.continuous)).trans
          (D.chartPath Bool.true (D.overlapToV y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_V, D.overlapPath_map_V]
  rfl

/-- Compatible maps give equal local values on paths in both charts. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_compatible_UV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ D.U) (hV : ∀ t, p t ∈ D.V) :
    D.localValue fU fV Bool.false p hU = D.localValue fU fV Bool.true p hV := by
  have hxU : x ∈ D.U := by simpa using hU 0
  have hxV : x ∈ D.V := by simpa using hV 0
  have hyU : y ∈ D.U := by simpa using hU 1
  have hyV : y ∈ D.V := by simpa using hV 1
  let pI :=
    FundamentalGroup.VanKampen.pathIn (S := (D.overlap : Set X)) p ⟨hxU, hxV⟩ ⟨hyU, hyV⟩
      (fun t => ⟨hU t, hV t⟩)
  have hpU : pI.map D.overlapToU.continuous = FundamentalGroup.VanKampen.pathIn p hxU hyU hU := by
    ext t
    rfl
  have hpV : pI.map D.overlapToV.continuous = FundamentalGroup.VanKampen.pathIn p hxV hyV hV := by
    ext t
    rfl
  have h := DFunLike.congr_fun hf (D.overlapClose pI)
  change fU (D.overlapHomU (D.overlapClose pI)) = fV (D.overlapHomV (D.overlapClose pI)) at h
  have hU' := congrArg fU ((D.overlapHomU_close pI).trans (congrArg (D.closePath Bool.false) hpU))
  have hV' := congrArg fV ((D.overlapHomV_close pI).trans (congrArg (D.closePath Bool.true) hpV))
  exact congrArg (fun a : G => a⁻¹) (hU'.symm.trans (h.trans hV'))

/-- Compatibility of the two local values: when the induced homomorphisms agree on the overlap, the local values assemble to a well-defined value on the whole loop (the glueing condition of van Kampen). -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_compatible {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i j : Bool) {x y : X}
    (p : Path x y) (hi : ∀ t, p t ∈ D.chart i) (hj : ∀ t, p t ∈ D.chart j) :
    D.localValue fU fV i p hi = D.localValue fU fV j p hj := by
  cases i <;> cases j
  · rfl
  · exact D.localValue_compatible_UV fU fV hf p hi hj
  · exact (D.localValue_compatible_UV fU fV hf p hj hi).symm
  · rfl

/-- The local path value assembled from compatible chart maps. -/
def FundamentalGroup.VanKampen.TwoOpenCover.localPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    FundamentalGroup.VanKampen.LocalPathValue (fun i => (D.chart i : Set X)) G
    where
  value := D.localValue fU fV
  refl := D.localValue_refl fU fV
  trans := D.localValue_trans fU fV
  subpath_mul := D.localValue_subpath_mul fU fV
  compatible := D.localValue_compatible fU fV hf

/-- The local path value is homotopy invariant within charts. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.localPathValue fU fV hf).HomotopyInvariant :=
  D.localValue_homotopy fU fV

/-- The local value of a chart loop is the image of its class. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.localValue_map_loop {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool)
    (p : Path (D.baseChart i) (D.baseChart i)) :
    D.localValue fU fV i (p.map continuous_subtype_val) (fun t => (p t).property) =
      (D.chartHom fU fV i (Path.Homotopic.Quotient.mk p))⁻¹ := by
  unfold localValue
  apply
    congrArg (fun a : FundamentalGroup (D.chart i) (D.baseChart i) => (D.chartHom fU fV i a)⁻¹)
  rw [D.closePath_loop]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- A homotopy-invariant path value induces a homomorphism on the fundamental group. -/
def FundamentalGroup.VanKampen.PathValue.fundamentalGroupHom {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) (hV : V.HomotopyInvariant)
    (o : X) : FundamentalGroup X o →* G
    where
  toFun :=
    _root_.Quotient.lift (fun p : Path o o => (V.value p)⁻¹)
      (fun p q h => congrArg (fun a : G => a⁻¹) (hV p q h))
  map_one' := by
    change (V.value (Path.refl o))⁻¹ = 1
    rw [V.refl, inv_one]
  map_mul' := by
    intro a b
    obtain ⟨p⟩ := a
    obtain ⟨q⟩ := b
    change (V.value (q.trans p))⁻¹ = (V.value p)⁻¹ * (V.value q)⁻¹
    rw [V.trans, mul_inv_rev]

/-- A point of the subinterval is reached inside `S`. -/
theorem FundamentalGroup.VanKampen.mem_of_subpath_mem {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t, p.subpath a b t ∈ s) {t : (unitInterval)} (ht : t ∈ Set.Icc a b) : p t ∈ s := by
  have hsub : Set.range (p.subpath a b) ⊆ s := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hsub
  exact hsub ⟨t, ht, rfl⟩

/-- Subpath membership is monotone in the interval. -/
theorem FundamentalGroup.VanKampen.subpath_mem_mono {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b c d : (unitInterval)} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c)
    (hdb : d ≤ b) {s : Set X} (hp : ∀ t, p.subpath a b t ∈ s) : ∀ t, p.subpath c d t ∈ s := by
  apply subpath_mem_of_mem_Icc p hcd
  intro t ht
  exact mem_of_subpath_mem p hab hp ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- Every loop in a space covered by open sets through a common point is homotopic to a
concatenation of loops each of which lies in a single member of the cover: the
subdivision half of the Seifert-van Kampen theorem (Hatcher, Theorem 1.20). -/
theorem FundamentalGroup.VanKampen.exists_path_subdivision {X : Type*} [TopologicalSpace X]
    {ι : Type*} {U : ι → Set X} (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    {x y : X} (p : Path x y) :
    ∃ t : ℕ → (unitInterval),
      t 0 = 0 ∧
        Monotone t ∧ (∃ n, t n = 1) ∧ ∀ n, ∃ i, ∀ s ∈ Set.Icc (t n) (t (n + 1)), p s ∈ U i := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i ↦ (hopen i).preimage p.continuous)
      (by
        intro s _
        have hs : p s ∈ ⋃ i, U i := by rw [hcover]; trivial
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  exact ⟨t, ht0, hmono, ⟨n, hn n le_rfl⟩, fun n ↦ hsub n⟩

/-! ### Primitives along a path -/

/-- `F` is a primitive for `p` when increments on chart pieces give local values. -/
def FundamentalGroup.VanKampen.LocalPathValue.IsPrimitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

/-- `F` is a primitive up to time `r`. -/
def FundamentalGroup.VanKampen.LocalPathValue.IsPrimitiveUpTo {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) (r : (unitInterval)) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → b ≤ r → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

/-- The trivial function is a primitive up to time zero. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.isPrimitiveUpTo_zero {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) {x y : X} (p : Path x y) :
    L.IsPrimitiveUpTo p (fun _ ↦ 1) 0 := by
  intro a b hab hb i hi
  have ha0 : a = 0 := le_antisymm (hab.trans hb) bot_le
  have hb0 : b = 0 := le_antisymm hb bot_le
  subst a
  subst b
  simp only [Path.subpath_self, L.refl, mul_one]

/-- A primitive up to `a` extends across a chart interval `[a, b]`. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.exists_primitiveUpTo_step {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} {a b : (unitInterval)} (_hab : a ≤ b) (i : ι)
    (hi : ∀ t ∈ Set.Icc a b, p t ∈ U i) (hF : L.IsPrimitiveUpTo p F a) :
    ∃ H : (unitInterval) → G, H 0 = F 0 ∧ L.IsPrimitiveUpTo p H b := by
  classical
  let memi (s t : (unitInterval)) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ∀ u, p.subpath s t u ∈ U i :=
    FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc p hst
      (fun u hu ↦ hi u ⟨has.trans hu.1, hu.2.trans htb⟩)
  let H (t : (unitInterval)) : G :=
    if hta : t ≤ a then F t
    else
      if htb : t ≤ b then F a * L.value i (p.subpath a t) (memi a t le_rfl (le_of_not_ge hta) htb)
      else 1
  have hleft (t : (unitInterval)) (hta : t ≤ a) : H t = F t := by exact dif_pos hta
  have hright (t : (unitInterval)) (hat : a ≤ t) (htb : t ≤ b) :
    H t = F a * L.value i (p.subpath a t) (memi a t le_rfl hat htb) := by
    by_cases hta : t ≤ a
    · have ht : t = a := le_antisymm hta hat
      subst t
      rw [hleft a le_rfl]
      simp only [Path.subpath_self, L.refl, mul_one]
    · dsimp only [H]
      rw [dif_neg hta, dif_pos htb]
  refine ⟨H, hleft 0 bot_le, ?_⟩
  intro s t hst htb j hj
  by_cases hta : t ≤ a
  · rw [hleft t hta, hleft s (hst.trans hta)]
    exact hF s t hst hta j hj
  have hat : a ≤ t := le_of_not_ge hta
  by_cases hsa : s ≤ a
  · have hjsa : ∀ u, p.subpath s a u ∈ U j :=
      FundamentalGroup.VanKampen.subpath_mem_mono p hst hsa le_rfl hat hj
    have hjat : ∀ u, p.subpath a t u ∈ U j :=
      FundamentalGroup.VanKampen.subpath_mem_mono p hst hat hsa le_rfl hj
    calc
      H t = F a * L.value i (p.subpath a t) (memi a t le_rfl hat htb) := hright t hat htb
      _ = F a * L.value j (p.subpath a t) hjat := by rw [L.compatible i j (p.subpath a t) _ hjat]
      _ = (F s * L.value j (p.subpath s a) hjsa) * L.value j (p.subpath a t) hjat := by
        rw [hF s a hsa le_rfl j hjsa]
      _ = F s * L.value j (p.subpath s t) hj := by
        rw [L.subpath_mul j p s a t hsa hat hjsa hjat hj, mul_assoc]
      _ = H s * L.value j (p.subpath s t) hj := by rw [hleft s hsa]
  · have has : a ≤ s := le_of_not_ge hsa
    rw [hright t hat htb, hright s has (hst.trans htb)]
    rw [L.compatible j i (p.subpath s t) hj (memi s t has hst htb)]
    rw [L.subpath_mul i p a s t has hst (memi a s le_rfl has (hst.trans htb))
        (memi s t has hst htb) (memi a t le_rfl hat htb)]
    exact (mul_assoc _ _ _).symm

/-- Every path admits a primitive along an open cover. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.exists_primitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    ∃ F : (unitInterval) → G, F 0 = 1 ∧ L.IsPrimitive p F := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroup.VanKampen.exists_path_subdivision hopen hcover p
  have hprefix : ∀ m, ∃ F : (unitInterval) → G, F 0 = 1 ∧ L.IsPrimitiveUpTo p F (t m) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ ↦ 1, rfl, ?_⟩
      rw [ht0]
      exact L.isPrimitiveUpTo_zero p
    | succ m ih =>
      obtain ⟨F, hF0, hF⟩ := ih
      obtain ⟨i, hi⟩ := hsub m
      obtain ⟨H, hH0, hH⟩ := L.exists_primitiveUpTo_step p (hmono m.le_succ) i hi hF
      exact ⟨H, hH0.trans hF0, hH⟩
  obtain ⟨F, hF0, hF⟩ := hprefix n
  refine ⟨F, hF0, ?_⟩
  intro a b hab i hi
  exact hF a b hab (by rw [hn]; exact le_top) i hi

/-- Primitives of a path are unique up to the initial value. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.primitive_unique {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) {F H : (unitInterval) → G}
    (hF : L.IsPrimitive p F) (hH : L.IsPrimitive p H) (h0 : F 0 = H 0) : F = H := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroup.VanKampen.exists_path_subdivision hopen hcover p
  have hprefix : ∀ m, ∀ s ≤ t m, F s = H s := by
    intro m
    induction m with
    | zero =>
      intro s hs
      have hs0 : s = 0 := le_antisymm (by simpa only [ht0] using hs) bot_le
      simpa only [hs0] using h0
    | succ m ih =>
      intro s hs
      by_cases hst : s ≤ t m
      · exact ih s hst
      have hts : t m ≤ s := le_of_not_ge hst
      obtain ⟨i, hi⟩ := hsub m
      have hlocal : ∀ u, p.subpath (t m) s u ∈ U i :=
        FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc p hts
          (fun u hu ↦ hi u ⟨hu.1, hu.2.trans hs⟩)
      rw [hF (t m) s hts i hlocal, hH (t m) s hts i hlocal, ih (t m) le_rfl]
  funext s
  exact hprefix n s (by rw [hn]; exact le_top)

/-! ### Subpath combinatorics -/

/-- Convex combination is monotone on the interval. -/
theorem FundamentalGroup.VanKampen.convexComb_monotone {a b : (unitInterval)} (hab : a ≤ b) :
    Monotone (Set.Icc.convexComb a b) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + s * b ≤ (1 - (t : ℝ)) * a + t * b
  have hab' : (a : ℝ) ≤ b := hab
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hst')]

/-- Convex combinations compose by acting on endpoints. -/
theorem FundamentalGroup.VanKampen.convexComb_comp (a b s t u : (unitInterval)) :
    Set.Icc.convexComb a b (Set.Icc.convexComb s t u) =
      Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u := by
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  ring

/-- A subpath of a subpath is the subpath over combined endpoints. -/
theorem FundamentalGroup.VanKampen.subpath_subpath {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (a b s t : (unitInterval)) :
    (p.subpath a b).subpath s t =
      p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) := by
  ext u
  change
    p (Set.Icc.convexComb a b (Set.Icc.convexComb s t u)) =
      p (Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u)
  rw [convexComb_comp]

/-- The midpoint of the unit interval. -/
def FundamentalGroup.VanKampen.intervalHalf : (unitInterval) :=
  ⟨1 / 2, by norm_num⟩

/-- The first half of a composite path is the first path. -/
theorem FundamentalGroup.VanKampen.trans_convexComb_first_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) (t : (unitInterval)) :
    (p.trans q) (Set.Icc.convexComb 0 intervalHalf t) = p t := by
  have ht : (Set.Icc.convexComb 0 intervalHalf t : ℝ) ≤ 1 / 2 := by
    change (1 - (t : ℝ)) * 0 + t * (1 / 2) ≤ 1 / 2
    linarith [t.2.2]
  rw [← Path.extend_apply (p.trans q), Path.extend_trans_of_le_half p q ht]
  have heq : 2 * (Set.Icc.convexComb 0 intervalHalf t : ℝ) = t := by
    change 2 * ((1 - (t : ℝ)) * 0 + t * (1 / 2)) = t
    ring
  rw [heq, Path.extend_apply]

/-- The second half of a composite path is the second path. -/
theorem FundamentalGroup.VanKampen.trans_convexComb_second_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) (t : (unitInterval)) :
    (p.trans q) (Set.Icc.convexComb intervalHalf 1 t) = q t := by
  have ht : 1 / 2 ≤ (Set.Icc.convexComb intervalHalf 1 t : ℝ) := by
    change 1 / 2 ≤ (1 - (t : ℝ)) * (1 / 2) + t * 1
    linarith [t.2.1]
  rw [← Path.extend_apply (p.trans q), Path.extend_trans_of_half_le p q ht]
  have heq : 2 * (Set.Icc.convexComb intervalHalf 1 t : ℝ) - 1 = t := by
    change 2 * ((1 - (t : ℝ)) * (1 / 2) + t * 1) - 1 = t
    ring
  rw [heq, Path.extend_apply]

/-- A composite path at the midpoint is the middle endpoint. -/
@[simp]
theorem FundamentalGroup.VanKampen.trans_apply_intervalHalf {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) : (p.trans q) intervalHalf = y := by
  simpa using trans_convexComb_first_half p q 1

/-- The first-half subpath of a composite is the first path. -/
theorem FundamentalGroup.VanKampen.trans_subpath_first_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath 0 intervalHalf =
      p.cast (p.trans q).source (trans_apply_intervalHalf p q) := by
  ext t
  exact trans_convexComb_first_half p q t

/-- The second-half subpath of a composite is the second path. -/
theorem FundamentalGroup.VanKampen.trans_subpath_second_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath intervalHalf 1 =
      q.cast (trans_apply_intervalHalf p q) (p.trans q).target := by
  ext t
  exact trans_convexComb_second_half p q t

/-- Local values depend only on the path, not the membership proof. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.value_eq_of_path_eq {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (i : ι) {x y : X} {p q : Path x y}
    (h : p = q) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i) : L.value i p hp = L.value i q hq := by
  cases h
  rfl

/-- A primitive restricts to a primitive of each subpath. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.isPrimitive_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} (hF : L.IsPrimitive p F) (a b : (unitInterval)) (hab : a ≤ b) :
    L.IsPrimitive (p.subpath a b) (fun t => (F a)⁻¹ * F (Set.Icc.convexComb a b t)) := by
  intro s t hst i hi
  have heq := FundamentalGroup.VanKampen.subpath_subpath p a b s t
  have hlocal : ∀ v, p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) v ∈ U i := by
    intro v
    rw [← heq]
    exact hi v
  have hv := L.value_eq_of_path_eq i heq hi hlocal
  have hstep :=
    hF (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t)
      (FundamentalGroup.VanKampen.convexComb_monotone hab hst) i hlocal
  change
    (F a)⁻¹ * F (Set.Icc.convexComb a b t) =
      ((F a)⁻¹ * F (Set.Icc.convexComb a b s)) * L.value i ((p.subpath a b).subpath s t) hi
  rw [hv, hstep, mul_assoc]
  rfl

/-! ### Transport and extension -/

/-- The primitive transport of a path through the local values. -/
def FundamentalGroup.VanKampen.LocalPathValue.transport {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : (unitInterval) → G :=
  (L.exists_primitive hopen hcover p).choose

/-- The transport starts at the identity. -/
@[simp]
theorem FundamentalGroup.VanKampen.LocalPathValue.transport_zero {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.transport hopen hcover p 0 = 1 :=
  (L.exists_primitive hopen hcover p).choose_spec.1

/-- The transport is a primitive of the path. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.transport_isPrimitive {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.IsPrimitive p (L.transport hopen hcover p) :=
  (L.exists_primitive hopen hcover p).choose_spec.2

/-- Transport over a subpath is the relative increment. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.transport_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b : (unitInterval)) (hab : a ≤ b)
    (t : (unitInterval)) :
    L.transport hopen hcover (p.subpath a b) t =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p (Set.Icc.convexComb a b t) := by
  apply
    congrFun
      (L.primitive_unique hopen hcover (p.subpath a b)
        (L.transport_isPrimitive hopen hcover (p.subpath a b))
        (L.isPrimitive_subpath p (L.transport_isPrimitive hopen hcover p) a b hab) ?_)
      t
  simp only [transport_zero, Set.Icc.convexComb_zero, inv_mul_cancel]

/-- The terminal value of the transport, the global value of the path. -/
def FundamentalGroup.VanKampen.LocalPathValue.rawValue {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] {U : ι → Set X} (L : FundamentalGroup.VanKampen.LocalPathValue U G)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : G :=
  L.transport hopen hcover p 1

/-- The raw value is unchanged by endpoint casts. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y) :
    L.rawValue hopen hcover (p.cast hx hy) = L.rawValue hopen hcover p := by
  cases hx
  cases hy
  rfl

/-- The raw value over the whole interval is the raw value. -/
@[simp]
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.rawValue hopen hcover (p.subpath 0 1) = L.rawValue hopen hcover p := by
  rw [Path.subpath_zero_one, L.rawValue_cast]

/-- The raw value of a subpath is the transport increment. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b : (unitInterval))
    (hab : a ≤ b) :
    L.rawValue hopen hcover (p.subpath a b) =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p b := by
  simpa only [rawValue, Set.Icc.convexComb_one] using L.transport_subpath hopen hcover p a b hab 1

/-- On a chart path the raw value is the local value. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_local {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (i : ι) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
    L.rawValue hopen hcover p = L.value i p hp := by
  have hs : ∀ t, p.subpath 0 1 t ∈ U i := fun t => hp _
  have h := L.transport_isPrimitive hopen hcover p 0 1 (by exact zero_le_one) i hs
  rw [L.transport_zero, one_mul] at h
  change L.rawValue hopen hcover p = _ at h
  have hc : ∀ t, p.cast p.source p.target t ∈ U i := hp
  exact
    h.trans
      ((L.value_eq_of_path_eq i (Path.subpath_zero_one p) hs hc).trans
        (L.value_cast i p p.source p.target hp hc))

/-- The raw value of the constant path is one. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_refl {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (x : X) : L.rawValue hopen hcover (Path.refl x) = 1 := by
  have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hp : ∀ t, Path.refl x t ∈ U i := fun _ => hi
  rw [L.rawValue_local hopen hcover i (Path.refl x) hp, L.refl]

/-- The raw value splits multiplicatively along subpaths. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) :
    L.rawValue hopen hcover (p.subpath a c) =
      L.rawValue hopen hcover (p.subpath a b) * L.rawValue hopen hcover (p.subpath b c) := by
  rw [L.rawValue_subpath hopen hcover p a c (hab.trans hbc),
    L.rawValue_subpath hopen hcover p a b hab, L.rawValue_subpath hopen hcover p b c hbc,
    mul_assoc, mul_inv_cancel_left]

/-- The raw value of a composite path is the product. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.rawValue_trans {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y z : X} (p : Path x y) (q : Path y z) :
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover p * L.rawValue hopen hcover q :=
  by
  calc
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover ((p.trans q).subpath 0 1) :=
      (L.rawValue_subpath_zero_one hopen hcover (p.trans q)).symm
    _ =
        L.rawValue hopen hcover ((p.trans q).subpath 0 FundamentalGroup.VanKampen.intervalHalf) *
          L.rawValue hopen hcover
            ((p.trans q).subpath FundamentalGroup.VanKampen.intervalHalf 1) :=
      (L.rawValue_subpath_mul hopen hcover (p.trans q) 0 FundamentalGroup.VanKampen.intervalHalf 1
        unitInterval.nonneg' unitInterval.le_one')
    _ = L.rawValue hopen hcover p * L.rawValue hopen hcover q := by
      rw [FundamentalGroup.VanKampen.trans_subpath_first_half,
        FundamentalGroup.VanKampen.trans_subpath_second_half, L.rawValue_cast, L.rawValue_cast]

/-- The global path value extending the local one. -/
def FundamentalGroup.VanKampen.LocalPathValue.extension {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : FundamentalGroup.VanKampen.PathValue X G
    where
  value := L.rawValue hopen hcover
  refl := L.rawValue_refl hopen hcover
  trans := L.rawValue_trans hopen hcover
  subpath_mul := L.rawValue_subpath_mul hopen hcover

/-- The extension agrees with the local value on chart paths. -/
theorem FundamentalGroup.VanKampen.LocalPathValue.extension_extends {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : (L.extension hopen hcover).Extends L := by
  intro i x y p hp
  exact L.rawValue_local hopen hcover i p hp

/-! ### Homotopy invariance via squares -/

/-- The horizontal path of a square map at height `s`. -/
def FundamentalGroup.VanKampen.squareHorizontal {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s : (unitInterval)) : Path (F (s, 0)) (F (s, 1))
    where
  toFun t := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- The vertical path of a square map at time `t`. -/
def FundamentalGroup.VanKampen.squareVertical {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (t : (unitInterval)) : Path (F (0, t)) (F (1, t))
    where
  toFun s := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

/-- Two paths between corners of the square are homotopic. -/
def FundamentalGroup.VanKampen.squarePathHomotopy {x y : (unitInterval) × (unitInterval)}
    (p q : Path x y) : Path.Homotopy p q
    where
  toFun
    u := (Set.Icc.convexComb (p u.2).1 (q u.2).1 u.1, Set.Icc.convexComb (p u.2).2 (q u.2).2 u.1)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact
        Set.Icc.continuous_convexComb_prod.comp
          (((p.continuous.comp continuous_snd).fst).prodMk
            (((q.continuous.comp continuous_snd).fst).prodMk continuous_fst))
    · exact
        Set.Icc.continuous_convexComb_prod.comp
          (((p.continuous.comp continuous_snd).snd).prodMk
            (((q.continuous.comp continuous_snd).snd).prodMk continuous_fst))
  map_zero_left u := by simp
  map_one_left u := by simp
  prop' r u hu := by rcases hu with rfl | rfl <;> simp

/-- Convex combinations stay in the interval. -/
theorem FundamentalGroup.VanKampen.convexComb_mem_Icc {s t u v : (unitInterval)}
    (hu : u ∈ Set.Icc s t) (hv : v ∈ Set.Icc s t) (r : (unitInterval)) :
    Set.Icc.convexComb u v r ∈ Set.Icc s t := by
  change (Set.Icc.convexComb u v r : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ)
  exact
    convex_Icc (s : ℝ) (t : ℝ) (show (u : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hu)
      (show (v : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hv) (unitInterval.one_minus_nonneg r)
      (unitInterval.nonneg r) (sub_add_cancel _ _)

/-- The square path homotopy stays inside a rectangle containing both paths. -/
theorem FundamentalGroup.VanKampen.squarePathHomotopy_mem_rectangle
    {x y : (unitInterval) × (unitInterval)} (p q : Path x y) (s t a b : (unitInterval))
    (hp : ∀ u, p u ∈ Set.Icc s t ×ˢ Set.Icc a b) (hq : ∀ u, q u ∈ Set.Icc s t ×ˢ Set.Icc a b)
    (u : (unitInterval) × (unitInterval)) :
    squarePathHomotopy p q u ∈ Set.Icc s t ×ˢ Set.Icc a b :=
  ⟨convexComb_mem_Icc (hp u.2).1 (hq u.2).1 u.1, convexComb_mem_Icc (hp u.2).2 (hq u.2).2 u.1⟩

/-- The horizontal-then-vertical boundary path of a rectangle. -/
def FundamentalGroup.VanKampen.rectangleHorizontalVertical (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b).trans
    ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)

/-- The vertical-then-horizontal boundary path of a rectangle. -/
def FundamentalGroup.VanKampen.rectangleVerticalHorizontal (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t).trans
    ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)

/-- The horizontal-vertical path maps to the composite of edge subpaths. -/
theorem FundamentalGroup.VanKampen.rectangleHorizontalVertical_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleHorizontalVertical s t a b).map F.continuous =
      ((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t) := by
  exact
    Path.map_trans
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b)
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)
      F.continuous

/-- The vertical-horizontal path maps to the composite of edge subpaths. -/
theorem FundamentalGroup.VanKampen.rectangleVerticalHorizontal_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleVerticalHorizontal s t a b).map F.continuous =
      ((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b) := by
  exact
    Path.map_trans
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t)
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)
      F.continuous

/-- The horizontal-vertical path stays inside the rectangle. -/
theorem FundamentalGroup.VanKampen.rectangleHorizontalVertical_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleHorizontalVertical s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨le_rfl, hst⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, hab, le_rfl⟩

/-- The vertical-horizontal path stays inside the rectangle. -/
theorem FundamentalGroup.VanKampen.rectangleVerticalHorizontal_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleVerticalHorizontal s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, le_rfl, hab⟩
  · intro u
    exact ⟨⟨hst, le_rfl⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩

/-- The two boundary paths around a mapped rectangle are homotopic. -/
def FundamentalGroup.VanKampen.rectangleBoundaryHomotopy {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    Path.Homotopy (((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t))
      (((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b)) :=
  ((squarePathHomotopy (rectangleHorizontalVertical s t a b)
            (rectangleVerticalHorizontal s t a b)).map
        F).cast
    (rectangleHorizontalVertical_map F s t a b) (rectangleVerticalHorizontal_map F s t a b)

/-- The boundary homotopy computes the rectangle path at each parameter. -/
theorem FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_apply {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval))
    (u : (unitInterval) × (unitInterval)) :
    rectangleBoundaryHomotopy F s t a b u =
      F
        (squarePathHomotopy (rectangleHorizontalVertical s t a b)
          (rectangleVerticalHorizontal s t a b) u) :=
  rfl

/-- The boundary homotopy stays inside a set containing the rectangle. -/
theorem FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_mem {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) (hst : s ≤ t)
    (hab : a ≤ b) {A : Set X} (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ A)
    (u : (unitInterval) × (unitInterval)) : rectangleBoundaryHomotopy F s t a b u ∈ A := by
  rw [rectangleBoundaryHomotopy_apply]
  exact
    hcell _
      (squarePathHomotopy_mem_rectangle _ _ s t a b
        (rectangleHorizontalVertical_mem s t a b hst hab)
        (rectangleVerticalHorizontal_mem s t a b hst hab) u)

/-- A rectangle inside a chart has equal boundary path values. -/
theorem FundamentalGroup.VanKampen.PathValue.square_cell_of_local {X : Type*} [TopologicalSpace X]
    {ι G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hExt : V.Extends L)
    (hL : L.HomotopyInvariant) (i : ι) (F : C((unitInterval) × (unitInterval), X))
    (s t a b : (unitInterval)) (hst : s ≤ t) (hab : a ≤ b)
    (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ U i) :
    V.value ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath a b) *
        V.value ((FundamentalGroup.VanKampen.squareVertical F b).subpath s t) =
      V.value ((FundamentalGroup.VanKampen.squareVertical F a).subpath s t) *
        V.value ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath a b) := by
  let H := FundamentalGroup.VanKampen.rectangleBoundaryHomotopy F s t a b
  have hH : ∀ u, H u ∈ U i :=
    FundamentalGroup.VanKampen.rectangleBoundaryHomotopy_mem F s t a b hst hab hcell
  have hp :
    ∀ u,
      ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath a b).trans
          ((FundamentalGroup.VanKampen.squareVertical F b).subpath s t) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_zero_left u)).mp (hH (0, u))
  have hq :
    ∀ u,
      ((FundamentalGroup.VanKampen.squareVertical F a).subpath s t).trans
          ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath a b) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_one_left u)).mp (hH (1, u))
  calc
    _ =
        V.value
          (((FundamentalGroup.VanKampen.squareHorizontal F s).subpath a b).trans
            ((FundamentalGroup.VanKampen.squareVertical F b).subpath s t)) :=
      (V.trans _ _).symm
    _ = L.value i _ hp := (hExt i _ hp)
    _ = L.value i _ hq := (hL i _ _ hp hq H hH)
    _ =
        V.value
          (((FundamentalGroup.VanKampen.squareVertical F a).subpath s t).trans
            ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath a b)) :=
      (hExt i _ hq).symm
    _ = _ := V.trans _ _

/-- A constant path has value one. -/
theorem FundamentalGroup.VanKampen.PathValue.value_eq_one_of_constant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    {x y : X} (p : Path x y) (hp : ∀ t, p t = x) : V.value p = 1 := by
  have hy : y = x := p.target.symm.trans (hp 1)
  subst y
  have heq : p = Path.refl x := by
    ext t
    exact hp t
  rw [heq, V.refl]

/-- A strip subdivision preserves the path value across a chart cell decomposition. -/
theorem FundamentalGroup.VanKampen.PathValue.square_strip {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    (F : C((unitInterval) × (unitInterval), X)) (s t : (unitInterval)) (d : ℕ → (unitInterval))
    (hmono : Monotone d) (n : ℕ)
    (hcell :
      ∀ k < n,
        V.value ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath (d k) (d (k + 1))) *
            V.value ((FundamentalGroup.VanKampen.squareVertical F (d (k + 1))).subpath s t) =
          V.value ((FundamentalGroup.VanKampen.squareVertical F (d k)).subpath s t) *
            V.value
              ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath (d k) (d (k + 1)))) :
    V.value ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
        V.value ((FundamentalGroup.VanKampen.squareVertical F (d n)).subpath s t) =
      V.value ((FundamentalGroup.VanKampen.squareVertical F (d 0)).subpath s t) *
        V.value ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath (d 0) (d n)) := by
  induction n with
  | zero => simp only [Path.subpath_self, V.refl, one_mul, mul_one]
  | succ n ih =>
    have hprev := ih (fun k hk => hcell k (Nat.lt_succ_of_lt hk))
    rw [V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)),
      V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))]
    calc
      _ =
          V.value ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value
                ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath (d n) (d (n + 1))) *
              V.value ((FundamentalGroup.VanKampen.squareVertical F (d (n + 1))).subpath s t)) :=
        mul_assoc _ _ _
      _ =
          V.value ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value ((FundamentalGroup.VanKampen.squareVertical F (d n)).subpath s t) *
              V.value
                ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath (d n) (d (n + 1)))) := by
        rw [hcell n (Nat.lt_succ_self n)]
      _ =
          (V.value ((FundamentalGroup.VanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
              V.value ((FundamentalGroup.VanKampen.squareVertical F (d n)).subpath s t)) *
            V.value
              ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath (d n) (d (n + 1))) :=
        (mul_assoc _ _ _).symm
      _ =
          (V.value ((FundamentalGroup.VanKampen.squareVertical F (d 0)).subpath s t) *
              V.value ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath (d 0) (d n))) *
            V.value
              ((FundamentalGroup.VanKampen.squareHorizontal F t).subpath (d n) (d (n + 1))) := by
        rw [hprev]
      _ = _ := mul_assoc _ _ _

/-- The value of a homotopy level equals the value of its evaluation path. -/
theorem FundamentalGroup.VanKampen.PathValue.value_squareHorizontal_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s : (unitInterval)) :
    V.value (FundamentalGroup.VanKampen.squareHorizontal H.toContinuousMap s) =
      V.value (H.eval s) := by
  have heq :
    FundamentalGroup.VanKampen.squareHorizontal H.toContinuousMap s =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  rw [heq, V.value_cast]

/-- The left edge of a path homotopy has trivial subpath value. -/
theorem FundamentalGroup.VanKampen.PathValue.value_squareVertical_homotopy_zero {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroup.VanKampen.squareVertical H.toContinuousMap 0).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 0) = H (s, 0)
  simp only [Path.Homotopy.source]

/-- The right edge of a path homotopy has trivial subpath value. -/
theorem FundamentalGroup.VanKampen.PathValue.value_squareVertical_homotopy_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroup.VanKampen.squareVertical H.toContinuousMap 1).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 1) = H (s, 1)
  simp only [Path.Homotopy.target]

/-- Homotopic paths have equal values when the value extends a homotopy-invariant local one. -/
theorem FundamentalGroup.VanKampen.PathValue.value_eq_of_homotopy_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroup.VanKampen.PathValue X G)
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (hExt : V.Extends L) (hL : L.HomotopyInvariant) {x y : X}
    (p q : Path x y) (H : Path.Homotopy p q) : V.value p = V.value q := by
  have hpre : Set.univ ⊆ ⋃ i, H ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨d, hd0, hdmono, ⟨n, hn⟩, hrect⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => (hopen i).preimage (ContinuousMapClass.map_continuous H)) hpre
  have hstep (k : ℕ) : V.value (H.eval (d k)) = V.value (H.eval (d (k + 1))) := by
    have hstrip :=
      V.square_strip H.toContinuousMap (d k) (d (k + 1)) d hdmono n
        (fun m _ => by
          obtain ⟨i, hi⟩ := hrect k m
          exact
            V.square_cell_of_local L hExt hL i H.toContinuousMap (d k) (d (k + 1)) (d m)
              (d (m + 1)) (hdmono (Nat.le_succ k)) (hdmono (Nat.le_succ m)) hi)
    rw [hd0, hn n le_rfl] at hstrip
    simpa only [V.value_subpath_zero_one, V.value_squareVertical_homotopy_zero,
      V.value_squareVertical_homotopy_one, V.value_squareHorizontal_homotopy, mul_one,
      one_mul] using hstrip
  have hwalk : ∀ k, V.value (H.eval (d 0)) = V.value (H.eval (d k)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact ih.trans (hstep k)
  have hfinish := hwalk n
  simpa only [hd0, hn n le_rfl, Path.Homotopy.eval_zero, Path.Homotopy.eval_one] using hfinish

/-- A path value extending a homotopy-invariant local value along an open cover is homotopy invariant. -/
theorem FundamentalGroup.VanKampen.PathValue.homotopyInvariant_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroup.VanKampen.PathValue X G)
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (hExt : V.Extends L) (hL : L.HomotopyInvariant) :
    V.HomotopyInvariant := by
  intro x y p q h
  obtain ⟨H⟩ := h
  exact V.value_eq_of_homotopy_of_open_cover L hopen hcover hExt hL p q H

/-! ### The van Kampen lift -/

/-- The global path value assembled from compatible chart homomorphisms. -/
def FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroup.VanKampen.PathValue X G :=
  (D.localPathValue fU fV hf).extension D.chart_open D.chart_cover

/-- The global path value extends the local path value. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue_extends {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).Extends (D.localPathValue fU fV hf) :=
  (D.localPathValue fU fV hf).extension_extends D.chart_open D.chart_cover

/-- The global path value is homotopy invariant. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.globalPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).HomotopyInvariant :=
  FundamentalGroup.VanKampen.PathValue.homotopyInvariant_of_open_cover (D.globalPathValue fU fV hf)
    (D.localPathValue fU fV hf) D.chart_open D.chart_cover (D.globalPathValue_extends fU fV hf)
    (D.localPathValue_homotopyInvariant fU fV hf)

/-- The induced homomorphism from the fundamental group to `G` — the van Kampen lift. -/
def FundamentalGroup.VanKampen.TwoOpenCover.lift {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroup X D.base →* G :=
  (D.globalPathValue fU fV hf).fundamentalGroupHom (D.globalPathValue_homotopyInvariant fU fV hf)
    D.base

/-- The lift computes the inverse local value on a chart loop. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.lift_mk_of_mem {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i : Bool) (p : Path D.base D.base)
    (hp : ∀ t, p t ∈ D.chart i) :
    D.lift fU fV hf (Path.Homotopic.Quotient.mk p) = (D.localValue fU fV i p hp)⁻¹ :=
  congrArg (fun a : G => a⁻¹) (D.globalPathValue_extends fU fV hf i p hp)

/-- The lift restricts to `fU` on `U` loops. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.lift_comp_inclusionU {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomU = fU := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.false (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

/-- The lift restricts to `fV` on `V` loops. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.lift_comp_inclusionV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomV = fV := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.true (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

/-- The fundamental group of chart `i`. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.ChartGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :=
  FundamentalGroup (D.chart i) (D.baseChart i)

/-- The overlap homomorphism into chart `i`. -/
def FundamentalGroup.VanKampen.TwoOpenCover.overlapHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : (i : Bool) → D.OverlapGroup →* D.ChartGroup i
  | false => D.overlapHomU
  | true => D.overlapHomV

/-- The chart homomorphism into the ambient fundamental group. -/
def FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    (i : Bool) → D.ChartGroup i →* FundamentalGroup X D.base
  | false => D.inclusionHomU
  | true => D.inclusionHomV

/-- Both routes from the overlap to the ambient group coincide. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_comp_overlapHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :
    (D.inclusionHom i).comp (D.overlapHom i) = D.inclusionHomU.comp D.overlapHomU := by
  cases i
  · rfl
  · exact D.inclusionHom_compatible.symm

/-! ### The pushout isomorphism -/

/-- The amalgamated pushout of the two chart groups over the overlap. -/
abbrev FundamentalGroup.VanKampen.TwoOpenCover.Pushout {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  Monoid.PushoutI D.overlapHom

/-- The `U` chart map into the pushout. -/
def FundamentalGroup.VanKampen.TwoOpenCover.pushoutOfU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.UGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.false

/-- The `V` chart map into the pushout. -/
def FundamentalGroup.VanKampen.TwoOpenCover.pushoutOfV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.VGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.true

/-- The overlap map into the pushout. -/
def FundamentalGroup.VanKampen.TwoOpenCover.pushoutBase {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.OverlapGroup →* D.Pushout :=
  Monoid.PushoutI.base D.overlapHom

/-- The `U` pushout map factors through the overlap. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutOfU_comp_overlapHomU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.pushoutOfU.comp D.overlapHomU = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.false

/-- The `V` pushout map factors through the overlap. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutOfV_comp_overlapHomV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.pushoutOfV.comp D.overlapHomV = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.true

/-- The pushout maps are compatible on the overlap. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutOf_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.Compatible D.pushoutOfU D.pushoutOfV :=
  D.pushoutOfU_comp_overlapHomU.trans D.pushoutOfV_comp_overlapHomV.symm

/-- The map from the pushout of `pi_1 U` and `pi_1 V` over `pi_1 (U ∩ V)` to `pi_1 (U ∪ V)` induced by the inclusions (Hatcher, Algebraic Topology, Theorem 1.20). -/
def FundamentalGroup.VanKampen.TwoOpenCover.pushoutToFundamentalGroup {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.Pushout →* FundamentalGroup X D.base :=
  Monoid.PushoutI.lift D.inclusionHom (D.inclusionHomU.comp D.overlapHomU)
    D.inclusionHom_comp_overlapHom

/-- The pushout-to-group map computes the inclusion on generators. -/
@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutToFundamentalGroup_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool)
    (g : D.ChartGroup i) :
    D.pushoutToFundamentalGroup (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  Monoid.PushoutI.lift_of _ _ _ g

/-- The pushout map composed with a chart inclusion is the chart homomorphism. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) :
    D.pushoutToFundamentalGroup.comp (Monoid.PushoutI.of i) = D.inclusionHom i := by
  ext g
  exact D.pushoutToFundamentalGroup_of i g

/-- The pushout map restricts to the `U` homomorphism. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_ofU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfU = D.inclusionHomU :=
  D.pushoutToFundamentalGroup_comp_of Bool.false

/-- The pushout map restricts to the `V` homomorphism. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_ofV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfV = D.inclusionHomV :=
  D.pushoutToFundamentalGroup_comp_of Bool.true

/-- The map from `pi_1 (U ∪ V)` to the pushout induced by sending a loop to its subdivided product of local loops (the uniqueness half of van Kampen). -/
def FundamentalGroup.VanKampen.TwoOpenCover.fundamentalGroupToPushout {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    FundamentalGroup X D.base →* D.Pushout :=
  D.lift D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The lift to the pushout restricts to the `U` pushout map. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionU
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomU = D.pushoutOfU :=
  D.lift_comp_inclusionU D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The lift to the pushout restricts to the `V` pushout map. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionV
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomV = D.pushoutOfV :=
  D.lift_comp_inclusionV D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The two comparison maps compose to the identity on the pushout. -/
theorem
  FundamentalGroup.VanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup = MonoidHom.id D.Pushout := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i
  · change
      (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp D.pushoutOfU =
        (MonoidHom.id D.Pushout).comp D.pushoutOfU
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofU,
      D.fundamentalGroupToPushout_comp_inclusionU, MonoidHom.id_comp]
  · change
      (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp D.pushoutOfV =
        (MonoidHom.id D.Pushout).comp D.pushoutOfV
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofV,
      D.fundamentalGroupToPushout_comp_inclusionV, MonoidHom.id_comp]

/-- The two comparison maps compose to the identity on the fundamental group. -/
theorem
  FundamentalGroup.VanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.fundamentalGroupToPushout =
      MonoidHom.id (FundamentalGroup X D.base) := by
  apply D.hom_ext
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionU,
      D.pushoutToFundamentalGroup_comp_ofU, MonoidHom.id_comp]
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionV,
      D.pushoutToFundamentalGroup_comp_ofV, MonoidHom.id_comp]

/-- The Seifert-van Kampen isomorphism: the fundamental group of `U ∪ V` is the pushout of `pi_1 U` and `pi_1 V` over `pi_1 (U ∩ V)` (Hatcher, Algebraic Topology, Theorem 1.20). -/
def FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.Pushout ≃* FundamentalGroup X D.base
    where
  toFun := D.pushoutToFundamentalGroup
  invFun := D.fundamentalGroupToPushout
  left_inv g := DFunLike.congr_fun D.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup g
  right_inv g := DFunLike.congr_fun D.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout g
  map_mul' := D.pushoutToFundamentalGroup.map_mul

/-- The pushout equivalence computes the inclusion on generators. -/
@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.pushoutEquiv_of {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (g : D.ChartGroup i) :
    D.pushoutEquiv (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  D.pushoutToFundamentalGroup_of i g

/-- The `U` inclusion is surjective when the `V` overlap map is. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (hV : Function.Surjective D.overlapHomV) : Function.Surjective D.inclusionHomU := by
  intro γ
  obtain ⟨q, rfl⟩ := D.pushoutEquiv.surjective γ
  induction q using Monoid.PushoutI.induction_on with
  | of i g =>
    cases i with
    | false => exact ⟨g, (D.pushoutEquiv_of Bool.false g).symm⟩
    | true =>
      obtain ⟨a, rfl⟩ := hV g
      exact
        ⟨D.overlapHomU a,
          (DFunLike.congr_fun D.inclusionHom_compatible a).trans
            (D.pushoutEquiv_of Bool.true (D.overlapHomV a)).symm⟩
  | base a =>
    refine ⟨D.overlapHomU a, ?_⟩
    exact
      (D.pushoutEquiv_of Bool.false (D.overlapHomU a)).symm.trans
        (congrArg D.pushoutEquiv (Monoid.PushoutI.of_apply_eq_base D.overlapHom Bool.false a))
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

/-! ### Two-open cover corollaries -/

/-- A space covered by two path-connected opens (meeting in a common base point, per
`FundamentalGroup.VanKampen.TwoOpenCover`) is path connected. -/
theorem SphereHomology.twoOpenCover_pathConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩

/-- Van Kampen for a two-open cover: if both opens are simply connected, the
fundamental group of the covered space at the cover base point is trivial
(Hatcher, Algebraic Topology, Theorem 1.20). -/
theorem SphereHomology.twoOpenCover_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] (g : FundamentalGroup X D.base) : g = 1 := by
  have h :
    MonoidHom.id (FundamentalGroup X D.base) =
      (1 : FundamentalGroup X D.base →* FundamentalGroup X D.base) := by
    apply D.hom_ext
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomU a = 1
      rw [ha, map_one]
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomV a = 1
      rw [ha, map_one]
  exact DFunLike.congr_fun h g
