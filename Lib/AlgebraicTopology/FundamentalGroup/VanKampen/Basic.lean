/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar, Fabian Franz
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.UnitInterval

/-!
# Path foundations for the two-open-cover van Kampen theorem

This module contains generic path, homotopy-class, and two-open-cover constructions used to prove
the fundamental-group van Kampen universal property. It contains no proof-specific cover or
relator data.

The path-factorization argument was adapted from Sebastian Kumar's Mathlib PR 28246, source commit
`037ad801e1e5a5b7aa1750957c07f7769812effc`.
-/

@[expose] public noncomputable section

open Set Function Topology
open scoped ContinuousMap Interval

theorem Path.trans_mem {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) {s : Set X} (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ∀ t, p.trans q t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [Path.trans_range]
  exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hq)

theorem FundamentalGroup.VanKampen.subpath_mem_of_mem_Icc {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t ∈ Set.Icc a b, p t ∈ s) : ∀ t, p.subpath a b t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [p.range_subpath_of_le a b hab]
  exact Set.image_subset_iff.mpr hp

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

theorem FundamentalGroup.VanKampen.LocalPathValue.value_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) (i : ι) {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hp : ∀ t, p t ∈ U i) (hp' : ∀ t, p.cast hx hy t ∈ U i) :
    L.value i (p.cast hx hy) hp' = L.value i p hp := by
  cases hx
  cases hy
  rfl

def FundamentalGroup.VanKampen.LocalPathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
    (H : Path.Homotopy p q), (∀ s, H s ∈ U i) → L.value i p hp = L.value i q hq

structure FundamentalGroup.VanKampen.PathValue (X : Type*) [TopologicalSpace X] (G : Type*)
    [Group G] where
  value : ∀ {x y : X}, Path x y → G
  refl : ∀ x, value (Path.refl x) = 1
  trans : ∀ {x y z : X} (p : Path x y) (q : Path y z), value (p.trans q) = value p * value q
  subpath_mul :
    ∀ {x y : X} (p : Path x y) (a b c : (unitInterval)),
      a ≤ b → b ≤ c → value (p.subpath a c) = value (p.subpath a b) * value (p.subpath b c)

theorem FundamentalGroup.VanKampen.PathValue.value_cast {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) {x y x' y' : X}
    (p : Path x y) (hx : x' = x) (hy : y' = y) : V.value (p.cast hx hy) = V.value p := by
  cases hx
  cases hy
  rfl

@[simp]
theorem FundamentalGroup.VanKampen.PathValue.value_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G)
    {x y : X} (p : Path x y) : V.value (p.subpath 0 1) = V.value p := by
  rw [Path.subpath_zero_one, V.value_cast]

def FundamentalGroup.VanKampen.PathValue.Extends {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i), V.value p = L.value i p hp

def FundamentalGroup.VanKampen.PathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.PathValue X G) : Prop :=
  ∀ {x y : X} (p q : Path x y), Path.Homotopic p q → V.value p = V.value q

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

abbrev FundamentalGroup.VanKampen.TwoOpenCover.chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : Bool → TopologicalSpace.Opens X
  | false => D.U
  | true => D.V

theorem FundamentalGroup.VanKampen.TwoOpenCover.base_mem_chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) : D.base ∈ D.chart i := by
  cases i
  · exact D.baseU
  · exact D.baseV

theorem FundamentalGroup.VanKampen.TwoOpenCover.chart_open {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) : IsOpen (D.chart i : Set X) :=
  (D.chart i).isOpen

theorem FundamentalGroup.VanKampen.TwoOpenCover.chart_cover {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : ⋃ i, (D.chart i : Set X) = Set.univ := by
  apply subset_antisymm (Set.subset_univ _)
  intro x _
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩

theorem FundamentalGroup.VanKampen.TwoOpenCover.mem_U_or_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : X) : x ∈ D.U ∨ x ∈ D.V := by
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact hx

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

def FundamentalGroup.VanKampen.TwoOpenCover.pathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical exact if h : x = D.base then (Path.refl D.base).cast rfl h else D.rawPathTo x

@[simp]
theorem FundamentalGroup.VanKampen.TwoOpenCover.pathTo_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.pathTo D.base = Path.refl D.base := by
  classical simp [pathTo]

theorem FundamentalGroup.VanKampen.TwoOpenCover.pathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.pathTo x t ∈ D.chart i := by
  classical
  unfold pathTo
  split_ifs
  · exact D.base_mem_chart i
  · exact D.rawPathTo_mem i x hx t

abbrev FundamentalGroup.VanKampen.TwoOpenCover.overlap {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : TopologicalSpace.Opens X :=
  D.U ⊓ D.V

abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseUPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.U :=
  ⟨D.base, D.baseU⟩

abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseVPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.V :=
  ⟨D.base, D.baseV⟩

abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseOverlapPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.overlap :=
  ⟨D.base, D.baseU, D.baseV⟩

abbrev FundamentalGroup.VanKampen.TwoOpenCover.baseChart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) (i : Bool) : D.chart i :=
  ⟨D.base, D.base_mem_chart i⟩

abbrev FundamentalGroup.VanKampen.TwoOpenCover.UGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  FundamentalGroup D.U D.baseUPoint

abbrev FundamentalGroup.VanKampen.TwoOpenCover.VGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  FundamentalGroup D.V D.baseVPoint

abbrev FundamentalGroup.VanKampen.TwoOpenCover.OverlapGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) :=
  FundamentalGroup D.overlap D.baseOverlapPoint

def FundamentalGroup.VanKampen.TwoOpenCover.overlapToU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.overlap, D.U) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def FundamentalGroup.VanKampen.TwoOpenCover.overlapToV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.overlap, D.V) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def FundamentalGroup.VanKampen.TwoOpenCover.inclusionU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def FundamentalGroup.VanKampen.TwoOpenCover.inclusionV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : C(D.V, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def FundamentalGroup.VanKampen.TwoOpenCover.overlapHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.OverlapGroup →* D.UGroup :=
  FundamentalGroup.map D.overlapToU D.baseOverlapPoint

def FundamentalGroup.VanKampen.TwoOpenCover.overlapHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.OverlapGroup →* D.VGroup :=
  FundamentalGroup.map D.overlapToV D.baseOverlapPoint

def FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.UGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionU D.baseUPoint

def FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : D.VGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionV D.baseVPoint

theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHom_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    D.inclusionHomU.comp D.overlapHomU = D.inclusionHomV.comp D.overlapHomV := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

def FundamentalGroup.VanKampen.TwoOpenCover.Compatible {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) {G : Type*} [Group G] (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) : Prop :=
  fU.comp D.overlapHomU = fV.comp D.overlapHomV

def FundamentalGroup.VanKampen.pathIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩
    where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp]
theorem FundamentalGroup.VanKampen.pathIn_apply {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (t : (unitInterval)) :
    (pathIn p hx hy hp t : X) = p t :=
  rfl

@[simp]
theorem FundamentalGroup.VanKampen.pathIn_map {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) :
    (pathIn p hx hy hp).map continuous_subtype_val = p := by
  ext t
  rfl

@[simp]
theorem FundamentalGroup.VanKampen.pathIn_refl {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (hx : x ∈ S) (hp : ∀ t, Path.refl x t ∈ S) :
    pathIn (Path.refl x) hx hx hp = Path.refl (⟨x, hx⟩ : S) := by
  ext t
  rfl

@[simp]
theorem FundamentalGroup.VanKampen.pathIn_trans {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y z : X} (p : Path x y) (q : Path y z) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (hpq : ∀ t, p.trans q t ∈ S) :
    pathIn (p.trans q) hx hz hpq = (pathIn p hx hy hp).trans (pathIn q hy hz hq) := by
  ext t
  simp only [pathIn_apply, Path.trans_apply]
  split_ifs <;> rfl

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

theorem FundamentalGroup.VanKampen.homotopy_trans_mem {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} {p q r : Path x y} (H : Path.Homotopy p q) (K : Path.Homotopy q r)
    (hH : ∀ s, H s ∈ S) (hK : ∀ s, K s ∈ S) : ∀ s, H.trans K s ∈ S := by
  intro s
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

theorem FundamentalGroup.VanKampen.homotopy_transRefl_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ S) :
    ∀ s, Path.Homotopy.transRefl p s ∈ S := by
  intro s
  exact hp _

theorem FundamentalGroup.VanKampen.homotopy_subpathTransSubpathRefl_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpathRefl p a b c s ∈ S := by
  intro s
  let m := Set.Icc.convexComb b c s.1
  have ham : a ≤ m := hab.trans (Set.Icc.le_convexComb hbc s.1)
  have hmc : m ≤ c := Set.Icc.convexComb_le hbc s.1
  change ((p.subpath a m).trans (p.subpath m c)) s.2 ∈ S
  apply Path.trans_mem
  · exact subpath_mem_of_mem_Icc p ham (fun t ht => hp t ⟨ht.1, ht.2.trans hmc⟩)
  · exact subpath_mem_of_mem_Icc p hmc (fun t ht => hp t ⟨ham.trans ht.1, ht.2⟩)

theorem FundamentalGroup.VanKampen.homotopy_subpathTransSubpath_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpath p a b c s ∈ S :=
  homotopy_trans_mem _ _ (homotopy_subpathTransSubpathRefl_mem p a b c hab hbc hp)
    (homotopy_transRefl_mem _ (subpath_mem_of_mem_Icc p (hab.trans hbc) hp))

theorem FundamentalGroup.VanKampen.mem_Icc_of_subpath_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b)
    (hp : ∀ t, p.subpath a b t ∈ S) : ∀ t ∈ Set.Icc a b, p t ∈ S := by
  have hr := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hr
  intro t ht
  exact hr ⟨t, ht, rfl⟩

def FundamentalGroup.VanKampen.subpathTransSubpathIn {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (ha : p a ∈ S)
    (hb : p b ∈ S) (hc : p c ∈ S) (hpab : ∀ t, p.subpath a b t ∈ S)
    (hpbc : ∀ t, p.subpath b c t ∈ S) (hpac : ∀ t, p.subpath a c t ∈ S) :
    Path.Homotopy ((pathIn (p.subpath a b) ha hb hpab).trans (pathIn (p.subpath b c) hb hc hpbc))
      (pathIn (p.subpath a c) ha hc hpac) :=
  (homotopyIn _ _ ha hc (Path.trans_mem _ _ hpab hpbc) hpac
        (Path.Homotopy.subpathTransSubpath p a b c)
        (homotopy_subpathTransSubpath_mem p a b c hab hbc
          (mem_Icc_of_subpath_mem p (hab.trans hbc) hpac))).cast
    (pathIn_trans _ _ ha hb hc hpab hpbc _) rfl

theorem FundamentalGroup.VanKampen.PathClass.pathClass_property_cast {X : Type*}
    [TopologicalSpace X] (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop) {x y x' y' : X}
    (q : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) (hq : P q) : P (q.cast hx hy) :=
  by
  cases hx
  cases hy
  simpa using hq

theorem FundamentalGroup.VanKampen.PathClass.pathClass_induction_of_open_cover {X : Type*}
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

theorem FundamentalGroup.VanKampen.PathClass.quotient_symm_trans_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem FundamentalGroup.VanKampen.PathClass.quotient_trans_right_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} {p q : Path.Homotopic.Quotient x y}
    (r : Path.Homotopic.Quotient y z) (h : p.trans r = q.trans r) : p = q := by
  have h' := congrArg (fun a : Path.Homotopic.Quotient x z => a.trans r.symm) h
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using h'

def FundamentalGroup.VanKampen.PathClass.basedLoop {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ x, Path.Homotopic.Quotient o x) {x y : X} (p : Path.Homotopic.Quotient x y) :
    FundamentalGroup X o :=
  ((F x).trans p).trans (F y).symm

def FundamentalGroup.VanKampen.PathClass.pathDifference {X : Type*} [TopologicalSpace X] {o x : X}
    (p q : Path.Homotopic.Quotient o x) : FundamentalGroup X o :=
  p.trans q.symm

@[simp]
theorem FundamentalGroup.VanKampen.PathClass.basedLoop_refl {X : Type*} [TopologicalSpace X]
    {o : X} (F : ∀ x, Path.Homotopic.Quotient o x) (x : X) :
    basedLoop F (Path.Homotopic.Quotient.refl x) = 1 := by
  simp only [basedLoop, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def]

theorem FundamentalGroup.VanKampen.PathClass.basedLoop_trans {X : Type*} [TopologicalSpace X]
    {o x y z : X} (F : ∀ x, Path.Homotopic.Quotient o x) (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : basedLoop F (p.trans q) = basedLoop F q * basedLoop F p :=
  by
  simp only [basedLoop, FundamentalGroup.mul_def, Path.Homotopic.Quotient.trans_assoc,
    quotient_symm_trans_cancel]

theorem FundamentalGroup.VanKampen.PathClass.basedLoop_comparison {X : Type*} [TopologicalSpace X]
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

theorem FundamentalGroup.VanKampen.TwoOpenCover.hom_ext {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (f g : FundamentalGroup X D.base →* G) (hU : f.comp D.inclusionHomU = g.comp D.inclusionHomU)
    (hV : f.comp D.inclusionHomV = g.comp D.inclusionHomV) : f = g := by
  let F (x : X) : Path.Homotopic.Quotient D.base x := Path.Homotopic.Quotient.mk (D.pathTo x)
  have hlocal :
    ∀ (i : Bool) {x y : X} (p : Path x y),
      (∀ t, p t ∈ D.chart i) →
        f (FundamentalGroup.VanKampen.PathClass.basedLoop F (Path.Homotopic.Quotient.mk p)) =
          g (FundamentalGroup.VanKampen.PathClass.basedLoop F (Path.Homotopic.Quotient.mk p)) := by
    intro i x y p hp
    have hx : x ∈ D.chart i := by simpa using hp 0
    have hy : y ∈ D.chart i := by simpa using hp 1
    let l : Path D.base D.base := ((D.pathTo x).trans p).trans (D.pathTo y).symm
    have hl : ∀ t, l t ∈ D.chart i :=
      Path.trans_mem _ _
        (Path.trans_mem _ _ (D.pathTo_mem i x hx) hp)
        (fun t => D.pathTo_mem i y hy (unitInterval.symm t))
    let l' : Path (D.baseChart i) (D.baseChart i) :=
      FundamentalGroup.VanKampen.pathIn l (D.base_mem_chart i) (D.base_mem_chart i) hl
    have hmap :
      (Path.Homotopic.Quotient.mk l').map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(D.chart i, X)) =
        FundamentalGroup.VanKampen.PathClass.basedLoop F (Path.Homotopic.Quotient.mk p) := by
      change
        Path.Homotopic.Quotient.mk (l'.map continuous_subtype_val) =
          FundamentalGroup.VanKampen.PathClass.basedLoop F (Path.Homotopic.Quotient.mk p)
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
      f (FundamentalGroup.VanKampen.PathClass.basedLoop F q) =
        g (FundamentalGroup.VanKampen.PathClass.basedLoop F q) := by
    apply
      FundamentalGroup.VanKampen.PathClass.pathClass_induction_of_open_cover
        (fun i => (D.chart i : Set X)) D.chart_open D.chart_cover
        (fun q =>
          f (FundamentalGroup.VanKampen.PathClass.basedLoop F q) =
            g (FundamentalGroup.VanKampen.PathClass.basedLoop F q))
    · intro x
      simp only [FundamentalGroup.VanKampen.PathClass.basedLoop_refl, map_one]
    · intro x y z p q hp hq
      rw [FundamentalGroup.VanKampen.PathClass.basedLoop_trans, map_mul, map_mul, hp, hq]
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
  simpa only [FundamentalGroup.VanKampen.PathClass.basedLoop, hbase,
    Path.Homotopic.Quotient.refl_trans, hsymm, Path.Homotopic.Quotient.trans_refl] using hall q
