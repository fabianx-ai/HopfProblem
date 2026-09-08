/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.FundamentalGroup.TwoSimplyConnectedCover
import Lib.AlgebraicTopology.FundamentalGroup.SimplyConnectedCover


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

theorem FundamentalGroupVanKampen.subpath_mem_of_mem_Icc {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t ∈ Set.Icc a b, p t ∈ s) : ∀ t, p.subpath a b t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [p.range_subpath_of_le a b hab]
  exact Set.image_subset_iff.mpr hp

structure FundamentalGroupVanKampen.LocalPathValue {X : Type*} [TopologicalSpace X] {ι : Type*}
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

theorem FundamentalGroupVanKampen.LocalPathValue.value_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (i : ι) {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hp : ∀ t, p t ∈ U i) (hp' : ∀ t, p.cast hx hy t ∈ U i) :
    L.value i (p.cast hx hy) hp' = L.value i p hp := by
  cases hx
  cases hy
  rfl

def FundamentalGroupVanKampen.LocalPathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
    (H : Path.Homotopy p q), (∀ s, H s ∈ U i) → L.value i p hp = L.value i q hq

structure FundamentalGroupVanKampen.PathValue (X : Type*) [TopologicalSpace X] (G : Type*)
    [Group G] where
  value : ∀ {x y : X}, Path x y → G
  refl : ∀ x, value (Path.refl x) = 1
  trans : ∀ {x y z : X} (p : Path x y) (q : Path y z), value (p.trans q) = value p * value q
  subpath_mul :
    ∀ {x y : X} (p : Path x y) (a b c : (unitInterval)),
      a ≤ b → b ≤ c → value (p.subpath a c) = value (p.subpath a b) * value (p.subpath b c)

theorem FundamentalGroupVanKampen.PathValue.value_cast {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) {x y x' y' : X}
    (p : Path x y) (hx : x' = x) (hy : y' = y) : V.value (p.cast hx hy) = V.value p := by
  cases hx
  cases hy
  rfl

@[simp]
theorem FundamentalGroupVanKampen.PathValue.value_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} (p : Path x y) : V.value (p.subpath 0 1) = V.value p := by
  rw [Path.subpath_zero_one, V.value_cast]

def FundamentalGroupVanKampen.PathValue.Extends {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i), V.value p = L.value i p hp

def FundamentalGroupVanKampen.PathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) : Prop :=
  ∀ {x y : X} (p q : Path x y), Path.Homotopic p q → V.value p = V.value q

structure FundamentalGroupVanKampen.TwoOpenCover (X : Type*) [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = Set.univ
  pathConnectedU : IsPathConnected (U : Set X)
  pathConnectedV : IsPathConnected (V : Set X)
  pathConnectedIntersection : IsPathConnected ((U : Set X) ∩ V)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

abbrev FundamentalGroupVanKampen.TwoOpenCover.chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : Bool → TopologicalSpace.Opens X
  | false => D.U
  | true => D.V

theorem FundamentalGroupVanKampen.TwoOpenCover.base_mem_chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : D.base ∈ D.chart i := by
  cases i
  · exact D.baseU
  · exact D.baseV

theorem FundamentalGroupVanKampen.TwoOpenCover.chart_open {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : IsOpen (D.chart i : Set X) :=
  (D.chart i).isOpen

theorem FundamentalGroupVanKampen.TwoOpenCover.chart_cover {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : ⋃ i, (D.chart i : Set X) = Set.univ := by
  apply subset_antisymm (Set.subset_univ _)
  intro x _
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩

theorem FundamentalGroupVanKampen.TwoOpenCover.mem_U_or_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : x ∈ D.U ∨ x ∈ D.V := by
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact hx

def FundamentalGroupVanKampen.TwoOpenCover.rawPathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical
    exact
    if h : x ∈ (D.U : Set X) ∩ D.V then
      (D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath
    else
      if hU : x ∈ D.U then (D.pathConnectedU.joinedIn D.base D.baseU x hU).somePath
      else
        (D.pathConnectedV.joinedIn D.base D.baseV x ((D.mem_U_or_V x).resolve_left hU)).somePath

theorem FundamentalGroupVanKampen.TwoOpenCover.rawPathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
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

def FundamentalGroupVanKampen.TwoOpenCover.pathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical exact if h : x = D.base then (Path.refl D.base).cast rfl h else D.rawPathTo x

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.pathTo_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.pathTo D.base = Path.refl D.base := by
  classical simp [pathTo]

theorem FundamentalGroupVanKampen.TwoOpenCover.pathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.pathTo x t ∈ D.chart i := by
  classical
  unfold pathTo
  split_ifs
  · exact D.base_mem_chart i
  · exact D.rawPathTo_mem i x hx t

abbrev FundamentalGroupVanKampen.TwoOpenCover.overlap {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : TopologicalSpace.Opens X :=
  D.U ⊓ D.V

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseUPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.U :=
  ⟨D.base, D.baseU⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseVPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.V :=
  ⟨D.base, D.baseV⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseOverlapPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.overlap :=
  ⟨D.base, D.baseU, D.baseV⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseChart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : D.chart i :=
  ⟨D.base, D.base_mem_chart i⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.UGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.U D.baseUPoint

abbrev FundamentalGroupVanKampen.TwoOpenCover.VGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.V D.baseVPoint

abbrev FundamentalGroupVanKampen.TwoOpenCover.OverlapGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.overlap D.baseOverlapPoint

def FundamentalGroupVanKampen.TwoOpenCover.overlapToU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.overlap, D.U) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def FundamentalGroupVanKampen.TwoOpenCover.overlapToV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.overlap, D.V) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def FundamentalGroupVanKampen.TwoOpenCover.inclusionU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def FundamentalGroupVanKampen.TwoOpenCover.inclusionV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.V, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def FundamentalGroupVanKampen.TwoOpenCover.overlapHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.OverlapGroup →* D.UGroup :=
  FundamentalGroup.map D.overlapToU D.baseOverlapPoint

def FundamentalGroupVanKampen.TwoOpenCover.overlapHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.OverlapGroup →* D.VGroup :=
  FundamentalGroup.map D.overlapToV D.baseOverlapPoint

def FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.UGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionU D.baseUPoint

def FundamentalGroupVanKampen.TwoOpenCover.inclusionHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.VGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionV D.baseVPoint

theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHom_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.inclusionHomU.comp D.overlapHomU = D.inclusionHomV.comp D.overlapHomV := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

def FundamentalGroupVanKampen.TwoOpenCover.Compatible {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {G : Type*} [Group G] (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) : Prop :=
  fU.comp D.overlapHomU = fV.comp D.overlapHomV

def FundamentalGroupVanKampen.pathIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩
    where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp]
theorem FundamentalGroupVanKampen.pathIn_apply {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (t : (unitInterval)) :
    (pathIn p hx hy hp t : X) = p t :=
  rfl

@[simp]
theorem FundamentalGroupVanKampen.pathIn_map {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) :
    (pathIn p hx hy hp).map continuous_subtype_val = p := by
  ext t
  rfl

@[simp]
theorem FundamentalGroupVanKampen.pathIn_refl {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (hx : x ∈ S) (hp : ∀ t, Path.refl x t ∈ S) :
    pathIn (Path.refl x) hx hx hp = Path.refl (⟨x, hx⟩ : S) := by
  ext t
  rfl

@[simp]
theorem FundamentalGroupVanKampen.pathIn_trans {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y z : X} (p : Path x y) (q : Path y z) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (hpq : ∀ t, p.trans q t ∈ S) :
    pathIn (p.trans q) hx hz hpq = (pathIn p hx hy hp).trans (pathIn q hy hz hq) := by
  ext t
  simp only [pathIn_apply, Path.trans_apply]
  split_ifs <;> rfl

def FundamentalGroupVanKampen.homotopyIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p q : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (H : Path.Homotopy p q) (hH : ∀ s, H s ∈ S) :
    Path.Homotopy (pathIn p hx hy hp) (pathIn q hx hy hq)
    where
  toFun s := ⟨H s, hH s⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.apply_zero t)
  map_one_left t := Subtype.ext (H.apply_one t)
  prop' s _t ht := Subtype.ext (H.eq_fst s ht)

theorem FundamentalGroupVanKampen.homotopy_trans_mem {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} {p q r : Path x y} (H : Path.Homotopy p q) (K : Path.Homotopy q r)
    (hH : ∀ s, H s ∈ S) (hK : ∀ s, K s ∈ S) : ∀ s, H.trans K s ∈ S := by
  intro s
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

theorem FundamentalGroupVanKampen.homotopy_transRefl_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ S) :
    ∀ s, Path.Homotopy.transRefl p s ∈ S := by
  intro s
  exact hp _

theorem FundamentalGroupVanKampen.homotopy_subpathTransSubpathRefl_mem {X : Type*}
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

theorem FundamentalGroupVanKampen.homotopy_subpathTransSubpath_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpath p a b c s ∈ S :=
  homotopy_trans_mem _ _ (homotopy_subpathTransSubpathRefl_mem p a b c hab hbc hp)
    (homotopy_transRefl_mem _ (subpath_mem_of_mem_Icc p (hab.trans hbc) hp))

theorem FundamentalGroupVanKampen.mem_Icc_of_subpath_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b)
    (hp : ∀ t, p.subpath a b t ∈ S) : ∀ t ∈ Set.Icc a b, p t ∈ S := by
  have hr := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hr
  intro t ht
  exact hr ⟨t, ht, rfl⟩

def FundamentalGroupVanKampen.subpathTransSubpathIn {X : Type*} [TopologicalSpace X] {S : Set X}
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

theorem FundamentalGroupVanKampen.TwoOpenCover.hom_ext {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
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
      FundamentalGroupVanKampen.pathIn l (D.base_mem_chart i) (D.base_mem_chart i) hl
    have hmap :
      (Path.Homotopic.Quotient.mk l').map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(D.chart i, X)) =
        TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p) := by
      change
        Path.Homotopic.Quotient.mk (l'.map continuous_subtype_val) =
          TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)
      rw [show l'.map continuous_subtype_val = l from
          FundamentalGroupVanKampen.pathIn_map _ _ _ _]
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

def FundamentalGroupVanKampen.TwoOpenCover.chartPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path (D.baseChart i) x :=
  FundamentalGroupVanKampen.pathIn (D.pathTo x.val) (D.base_mem_chart i) x.property
    (D.pathTo_mem i x.val x.property)

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.chartPath_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    D.chartPath i (D.baseChart i) = Path.refl (D.baseChart i) := by
  simp only [chartPath, baseChart, D.pathTo_base, FundamentalGroupVanKampen.pathIn_refl]

def FundamentalGroupVanKampen.TwoOpenCover.chartPathClass {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path.Homotopic.Quotient (D.baseChart i) x :=
  Path.Homotopic.Quotient.mk (D.chartPath i x)

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.chartPathClass_base {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    D.chartPathClass i (D.baseChart i) = Path.Homotopic.Quotient.refl (D.baseChart i) := by
  simp only [chartPathClass, D.chartPath_base, Path.Homotopic.Quotient.mk_refl]

def FundamentalGroupVanKampen.TwoOpenCover.closePath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) {x y : D.chart i} (p : Path x y) :
    FundamentalGroup (D.chart i) (D.baseChart i) :=
  TriangleRegularBaseFundamentalGroup.basedLoop (D.chartPathClass i)
    (Path.Homotopic.Quotient.mk p)

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.closePath_refl {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    D.closePath i (Path.refl x) = 1 :=
  TriangleRegularBaseFundamentalGroup.basedLoop_refl _ _

theorem FundamentalGroupVanKampen.TwoOpenCover.closePath_trans {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) {x y z : D.chart i} (p : Path x y)
    (q : Path y z) : D.closePath i (p.trans q) = D.closePath i q * D.closePath i p := by
  exact
    TriangleRegularBaseFundamentalGroup.basedLoop_trans (D.chartPathClass i)
      (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q)

theorem FundamentalGroupVanKampen.TwoOpenCover.closePath_homotopic {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool)
    {x y : D.chart i} {p q : Path x y} (hpq : Path.Homotopic p q) :
    D.closePath i p = D.closePath i q := by
  unfold closePath
  rw [Path.Homotopic.Quotient.eq.mpr hpq]

theorem FundamentalGroupVanKampen.TwoOpenCover.closePath_loop {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool)
    (p : Path (D.baseChart i) (D.baseChart i)) : D.closePath i p = Path.Homotopic.Quotient.mk p :=
  by
  simp only [closePath, TriangleRegularBaseFundamentalGroup.basedLoop, D.chartPathClass_base,
    Path.Homotopic.Quotient.refl_trans]
  exact Path.Homotopic.Quotient.trans_refl _

def FundamentalGroupVanKampen.TwoOpenCover.chartHom {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) : FundamentalGroup (D.chart i) (D.baseChart i) →* G := by
  cases i
  · exact fU
  · exact fV

def FundamentalGroupVanKampen.TwoOpenCover.localValue {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.chart i) : G :=
  (D.chartHom fU fV i
      (D.closePath i
        (FundamentalGroupVanKampen.pathIn (S := (D.chart i : Set X)) p (by simpa using hp 0)
          (by simpa using hp 1) hp)))⁻¹

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_refl {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) (x : X) (hx : ∀ t, Path.refl x t ∈ D.chart i) :
    D.localValue fU fV i (Path.refl x) hx = 1 := by
  simp only [localValue, FundamentalGroupVanKampen.pathIn_refl, D.closePath_refl, map_one,
    inv_one]

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_trans {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (hpq : ∀ t, p.trans q t ∈ D.chart i) :
    D.localValue fU fV i (p.trans q) hpq =
      D.localValue fU fV i p hp * D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  have hz : z ∈ D.chart i := by simpa using hq 1
  unfold localValue
  rw [FundamentalGroupVanKampen.pathIn_trans p q hx hy hz hp hq hpq, D.closePath_trans, map_mul,
    mul_inv_rev]

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y)
    (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (hpab : ∀ t, p.subpath a b t ∈ D.chart i)
    (hpbc : ∀ t, p.subpath b c t ∈ D.chart i) (hpac : ∀ t, p.subpath a c t ∈ D.chart i) :
    D.localValue fU fV i (p.subpath a c) hpac =
      D.localValue fU fV i (p.subpath a b) hpab * D.localValue fU fV i (p.subpath b c) hpbc := by
  have ha : p a ∈ D.chart i := by simpa using hpab 0
  have hb : p b ∈ D.chart i := by simpa using hpab 1
  have hc : p c ∈ D.chart i := by simpa using hpbc 1
  have H :=
    FundamentalGroupVanKampen.subpathTransSubpathIn p a b c hab hbc ha hb hc hpab hpbc hpac
  unfold localValue
  rw [← D.closePath_homotopic i ⟨H⟩, D.closePath_trans, map_mul, mul_inv_rev]

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (H : Path.Homotopy p q)
    (hH : ∀ s, H s ∈ D.chart i) : D.localValue fU fV i p hp = D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  unfold localValue
  rw [D.closePath_homotopic i ⟨FundamentalGroupVanKampen.homotopyIn p q hx hy hp hq H hH⟩]

def FundamentalGroupVanKampen.TwoOpenCover.overlapPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : D.overlap) : Path D.baseOverlapPoint x :=
  FundamentalGroupVanKampen.pathIn (S := (D.overlap : Set X)) (D.pathTo x.val) ⟨D.baseU, D.baseV⟩
    x.property
    (fun t =>
      ⟨D.pathTo_mem Bool.false x.val x.property.1 t, D.pathTo_mem Bool.true x.val x.property.2 t⟩)

theorem FundamentalGroupVanKampen.TwoOpenCover.overlapPath_map_U {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToU.continuous = D.chartPath Bool.false (D.overlapToU x) := by
  ext t
  rfl

theorem FundamentalGroupVanKampen.TwoOpenCover.overlapPath_map_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToV.continuous = D.chartPath Bool.true (D.overlapToV x) := by
  ext t
  rfl

def FundamentalGroupVanKampen.TwoOpenCover.overlapClose {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.OverlapGroup :=
  TriangleRegularBaseFundamentalGroup.basedLoop
    (fun x => Path.Homotopic.Quotient.mk (D.overlapPath x)) (Path.Homotopic.Quotient.mk p)

theorem FundamentalGroupVanKampen.TwoOpenCover.overlapHomU_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomU (D.overlapClose p) = D.closePath Bool.false (p.map D.overlapToU.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToU.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.false (D.overlapToU x)).trans (p.map D.overlapToU.continuous)).trans
          (D.chartPath Bool.false (D.overlapToU y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_U, D.overlapPath_map_U]
  rfl

theorem FundamentalGroupVanKampen.TwoOpenCover.overlapHomV_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomV (D.overlapClose p) = D.closePath Bool.true (p.map D.overlapToV.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToV.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.true (D.overlapToV x)).trans (p.map D.overlapToV.continuous)).trans
          (D.chartPath Bool.true (D.overlapToV y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_V, D.overlapPath_map_V]
  rfl

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_compatible_UV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ D.U) (hV : ∀ t, p t ∈ D.V) :
    D.localValue fU fV Bool.false p hU = D.localValue fU fV Bool.true p hV := by
  have hxU : x ∈ D.U := by simpa using hU 0
  have hxV : x ∈ D.V := by simpa using hV 0
  have hyU : y ∈ D.U := by simpa using hU 1
  have hyV : y ∈ D.V := by simpa using hV 1
  let pI :=
    FundamentalGroupVanKampen.pathIn (S := (D.overlap : Set X)) p ⟨hxU, hxV⟩ ⟨hyU, hyV⟩
      (fun t => ⟨hU t, hV t⟩)
  have hpU : pI.map D.overlapToU.continuous = FundamentalGroupVanKampen.pathIn p hxU hyU hU := by
    ext t
    rfl
  have hpV : pI.map D.overlapToV.continuous = FundamentalGroupVanKampen.pathIn p hxV hyV hV := by
    ext t
    rfl
  have h := DFunLike.congr_fun hf (D.overlapClose pI)
  change fU (D.overlapHomU (D.overlapClose pI)) = fV (D.overlapHomV (D.overlapClose pI)) at h
  have hU' := congrArg fU ((D.overlapHomU_close pI).trans (congrArg (D.closePath Bool.false) hpU))
  have hV' := congrArg fV ((D.overlapHomV_close pI).trans (congrArg (D.closePath Bool.true) hpV))
  exact congrArg (fun a : G => a⁻¹) (hU'.symm.trans (h.trans hV'))

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_compatible {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i j : Bool) {x y : X}
    (p : Path x y) (hi : ∀ t, p t ∈ D.chart i) (hj : ∀ t, p t ∈ D.chart j) :
    D.localValue fU fV i p hi = D.localValue fU fV j p hj := by
  cases i <;> cases j
  · rfl
  · exact D.localValue_compatible_UV fU fV hf p hi hj
  · exact (D.localValue_compatible_UV fU fV hf p hj hi).symm
  · rfl

def FundamentalGroupVanKampen.TwoOpenCover.localPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    FundamentalGroupVanKampen.LocalPathValue (fun i => (D.chart i : Set X)) G
    where
  value := D.localValue fU fV
  refl := D.localValue_refl fU fV
  trans := D.localValue_trans fU fV
  subpath_mul := D.localValue_subpath_mul fU fV
  compatible := D.localValue_compatible fU fV hf

theorem FundamentalGroupVanKampen.TwoOpenCover.localPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.localPathValue fU fV hf).HomotopyInvariant :=
  D.localValue_homotopy fU fV

theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_map_loop {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
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

def FundamentalGroupVanKampen.PathValue.fundamentalGroupHom {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) (hV : V.HomotopyInvariant)
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

theorem FundamentalGroupVanKampen.mem_of_subpath_mem {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t, p.subpath a b t ∈ s) {t : (unitInterval)} (ht : t ∈ Set.Icc a b) : p t ∈ s := by
  have hsub : Set.range (p.subpath a b) ⊆ s := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hsub
  exact hsub ⟨t, ht, rfl⟩

theorem FundamentalGroupVanKampen.subpath_mem_mono {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b c d : (unitInterval)} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c)
    (hdb : d ≤ b) {s : Set X} (hp : ∀ t, p.subpath a b t ∈ s) : ∀ t, p.subpath c d t ∈ s := by
  apply subpath_mem_of_mem_Icc p hcd
  intro t ht
  exact mem_of_subpath_mem p hab hp ⟨hac.trans ht.1, ht.2.trans hdb⟩

theorem FundamentalGroupVanKampen.exists_path_subdivision {X : Type*} [TopologicalSpace X]
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

def FundamentalGroupVanKampen.LocalPathValue.IsPrimitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

def FundamentalGroupVanKampen.LocalPathValue.IsPrimitiveUpTo {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) (r : (unitInterval)) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → b ≤ r → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

theorem FundamentalGroupVanKampen.LocalPathValue.isPrimitiveUpTo_zero {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y) :
    L.IsPrimitiveUpTo p (fun _ ↦ 1) 0 := by
  intro a b hab hb i hi
  have ha0 : a = 0 := le_antisymm (hab.trans hb) bot_le
  have hb0 : b = 0 := le_antisymm hb bot_le
  subst a
  subst b
  simp only [Path.subpath_self, L.refl, mul_one]

theorem FundamentalGroupVanKampen.LocalPathValue.exists_primitiveUpTo_step {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} {a b : (unitInterval)} (_hab : a ≤ b) (i : ι)
    (hi : ∀ t ∈ Set.Icc a b, p t ∈ U i) (hF : L.IsPrimitiveUpTo p F a) :
    ∃ H : (unitInterval) → G, H 0 = F 0 ∧ L.IsPrimitiveUpTo p H b := by
  classical
  let memi (s t : (unitInterval)) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ∀ u, p.subpath s t u ∈ U i :=
    FundamentalGroupVanKampen.subpath_mem_of_mem_Icc p hst
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
      FundamentalGroupVanKampen.subpath_mem_mono p hst hsa le_rfl hat hj
    have hjat : ∀ u, p.subpath a t u ∈ U j :=
      FundamentalGroupVanKampen.subpath_mem_mono p hst hat hsa le_rfl hj
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

theorem FundamentalGroupVanKampen.LocalPathValue.exists_primitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    ∃ F : (unitInterval) → G, F 0 = 1 ∧ L.IsPrimitive p F := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroupVanKampen.exists_path_subdivision hopen hcover p
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

theorem FundamentalGroupVanKampen.LocalPathValue.primitive_unique {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) {F H : (unitInterval) → G}
    (hF : L.IsPrimitive p F) (hH : L.IsPrimitive p H) (h0 : F 0 = H 0) : F = H := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroupVanKampen.exists_path_subdivision hopen hcover p
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
        FundamentalGroupVanKampen.subpath_mem_of_mem_Icc p hts
          (fun u hu ↦ hi u ⟨hu.1, hu.2.trans hs⟩)
      rw [hF (t m) s hts i hlocal, hH (t m) s hts i hlocal, ih (t m) le_rfl]
  funext s
  exact hprefix n s (by rw [hn]; exact le_top)

theorem FundamentalGroupVanKampen.convexComb_monotone {a b : (unitInterval)} (hab : a ≤ b) :
    Monotone (Set.Icc.convexComb a b) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + s * b ≤ (1 - (t : ℝ)) * a + t * b
  have hab' : (a : ℝ) ≤ b := hab
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hst')]

theorem FundamentalGroupVanKampen.convexComb_comp (a b s t u : (unitInterval)) :
    Set.Icc.convexComb a b (Set.Icc.convexComb s t u) =
      Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u := by
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  ring

theorem FundamentalGroupVanKampen.subpath_subpath {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (a b s t : (unitInterval)) :
    (p.subpath a b).subpath s t =
      p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) := by
  ext u
  change
    p (Set.Icc.convexComb a b (Set.Icc.convexComb s t u)) =
      p (Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u)
  rw [convexComb_comp]

def FundamentalGroupVanKampen.intervalHalf : (unitInterval) :=
  ⟨1 / 2, by norm_num⟩

theorem FundamentalGroupVanKampen.trans_convexComb_first_half {X : Type*} [TopologicalSpace X]
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

theorem FundamentalGroupVanKampen.trans_convexComb_second_half {X : Type*} [TopologicalSpace X]
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

@[simp]
theorem FundamentalGroupVanKampen.trans_apply_intervalHalf {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) : (p.trans q) intervalHalf = y := by
  simpa using trans_convexComb_first_half p q 1

theorem FundamentalGroupVanKampen.trans_subpath_first_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath 0 intervalHalf =
      p.cast (p.trans q).source (trans_apply_intervalHalf p q) := by
  ext t
  exact trans_convexComb_first_half p q t

theorem FundamentalGroupVanKampen.trans_subpath_second_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath intervalHalf 1 =
      q.cast (trans_apply_intervalHalf p q) (p.trans q).target := by
  ext t
  exact trans_convexComb_second_half p q t

theorem FundamentalGroupVanKampen.LocalPathValue.value_eq_of_path_eq {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (i : ι) {x y : X} {p q : Path x y}
    (h : p = q) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i) : L.value i p hp = L.value i q hq := by
  cases h
  rfl

theorem FundamentalGroupVanKampen.LocalPathValue.isPrimitive_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} (hF : L.IsPrimitive p F) (a b : (unitInterval)) (hab : a ≤ b) :
    L.IsPrimitive (p.subpath a b) (fun t => (F a)⁻¹ * F (Set.Icc.convexComb a b t)) := by
  intro s t hst i hi
  have heq := FundamentalGroupVanKampen.subpath_subpath p a b s t
  have hlocal : ∀ v, p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) v ∈ U i := by
    intro v
    rw [← heq]
    exact hi v
  have hv := L.value_eq_of_path_eq i heq hi hlocal
  have hstep :=
    hF (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t)
      (FundamentalGroupVanKampen.convexComb_monotone hab hst) i hlocal
  change
    (F a)⁻¹ * F (Set.Icc.convexComb a b t) =
      ((F a)⁻¹ * F (Set.Icc.convexComb a b s)) * L.value i ((p.subpath a b).subpath s t) hi
  rw [hv, hstep, mul_assoc]
  rfl

def FundamentalGroupVanKampen.LocalPathValue.transport {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : (unitInterval) → G :=
  (L.exists_primitive hopen hcover p).choose

@[simp]
theorem FundamentalGroupVanKampen.LocalPathValue.transport_zero {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.transport hopen hcover p 0 = 1 :=
  (L.exists_primitive hopen hcover p).choose_spec.1

theorem FundamentalGroupVanKampen.LocalPathValue.transport_isPrimitive {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.IsPrimitive p (L.transport hopen hcover p) :=
  (L.exists_primitive hopen hcover p).choose_spec.2

theorem FundamentalGroupVanKampen.LocalPathValue.transport_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
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

def FundamentalGroupVanKampen.LocalPathValue.rawValue {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] {U : ι → Set X} (L : FundamentalGroupVanKampen.LocalPathValue U G)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : G :=
  L.transport hopen hcover p 1

theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y) :
    L.rawValue hopen hcover (p.cast hx hy) = L.rawValue hopen hcover p := by
  cases hx
  cases hy
  rfl

@[simp]
theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.rawValue hopen hcover (p.subpath 0 1) = L.rawValue hopen hcover p := by
  rw [Path.subpath_zero_one, L.rawValue_cast]

theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_subpath {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b : (unitInterval))
    (hab : a ≤ b) :
    L.rawValue hopen hcover (p.subpath a b) =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p b := by
  simpa only [rawValue, Set.Icc.convexComb_one] using L.transport_subpath hopen hcover p a b hab 1

theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_local {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
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

theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_refl {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (x : X) : L.rawValue hopen hcover (Path.refl x) = 1 := by
  have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hp : ∀ t, Path.refl x t ∈ U i := fun _ => hi
  rw [L.rawValue_local hopen hcover i (Path.refl x) hp, L.refl]

theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) :
    L.rawValue hopen hcover (p.subpath a c) =
      L.rawValue hopen hcover (p.subpath a b) * L.rawValue hopen hcover (p.subpath b c) := by
  rw [L.rawValue_subpath hopen hcover p a c (hab.trans hbc),
    L.rawValue_subpath hopen hcover p a b hab, L.rawValue_subpath hopen hcover p b c hbc,
    mul_assoc, mul_inv_cancel_left]

theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_trans {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y z : X} (p : Path x y) (q : Path y z) :
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover p * L.rawValue hopen hcover q :=
  by
  calc
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover ((p.trans q).subpath 0 1) :=
      (L.rawValue_subpath_zero_one hopen hcover (p.trans q)).symm
    _ =
        L.rawValue hopen hcover ((p.trans q).subpath 0 FundamentalGroupVanKampen.intervalHalf) *
          L.rawValue hopen hcover
            ((p.trans q).subpath FundamentalGroupVanKampen.intervalHalf 1) :=
      (L.rawValue_subpath_mul hopen hcover (p.trans q) 0 FundamentalGroupVanKampen.intervalHalf 1
        unitInterval.nonneg' unitInterval.le_one')
    _ = L.rawValue hopen hcover p * L.rawValue hopen hcover q := by
      rw [FundamentalGroupVanKampen.trans_subpath_first_half,
        FundamentalGroupVanKampen.trans_subpath_second_half, L.rawValue_cast, L.rawValue_cast]

def FundamentalGroupVanKampen.LocalPathValue.extension {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : FundamentalGroupVanKampen.PathValue X G
    where
  value := L.rawValue hopen hcover
  refl := L.rawValue_refl hopen hcover
  trans := L.rawValue_trans hopen hcover
  subpath_mul := L.rawValue_subpath_mul hopen hcover

theorem FundamentalGroupVanKampen.LocalPathValue.extension_extends {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : (L.extension hopen hcover).Extends L := by
  intro i x y p hp
  exact L.rawValue_local hopen hcover i p hp

def FundamentalGroupVanKampen.squareHorizontal {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s : (unitInterval)) : Path (F (s, 0)) (F (s, 1))
    where
  toFun t := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

def FundamentalGroupVanKampen.squareVertical {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (t : (unitInterval)) : Path (F (0, t)) (F (1, t))
    where
  toFun s := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

def FundamentalGroupVanKampen.squarePathHomotopy {x y : (unitInterval) × (unitInterval)}
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

theorem FundamentalGroupVanKampen.convexComb_mem_Icc {s t u v : (unitInterval)}
    (hu : u ∈ Set.Icc s t) (hv : v ∈ Set.Icc s t) (r : (unitInterval)) :
    Set.Icc.convexComb u v r ∈ Set.Icc s t := by
  change (Set.Icc.convexComb u v r : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ)
  exact
    convex_Icc (s : ℝ) (t : ℝ) (show (u : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hu)
      (show (v : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hv) (unitInterval.one_minus_nonneg r)
      (unitInterval.nonneg r) (sub_add_cancel _ _)

theorem FundamentalGroupVanKampen.squarePathHomotopy_mem_rectangle
    {x y : (unitInterval) × (unitInterval)} (p q : Path x y) (s t a b : (unitInterval))
    (hp : ∀ u, p u ∈ Set.Icc s t ×ˢ Set.Icc a b) (hq : ∀ u, q u ∈ Set.Icc s t ×ˢ Set.Icc a b)
    (u : (unitInterval) × (unitInterval)) :
    squarePathHomotopy p q u ∈ Set.Icc s t ×ˢ Set.Icc a b :=
  ⟨convexComb_mem_Icc (hp u.2).1 (hq u.2).1 u.1, convexComb_mem_Icc (hp u.2).2 (hq u.2).2 u.1⟩

def FundamentalGroupVanKampen.rectangleHorizontalVertical (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b).trans
    ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)

def FundamentalGroupVanKampen.rectangleVerticalHorizontal (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t).trans
    ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)

theorem FundamentalGroupVanKampen.rectangleHorizontalVertical_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleHorizontalVertical s t a b).map F.continuous =
      ((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t) := by
  exact
    Path.map_trans
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b)
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)
      F.continuous

theorem FundamentalGroupVanKampen.rectangleVerticalHorizontal_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleVerticalHorizontal s t a b).map F.continuous =
      ((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b) := by
  exact
    Path.map_trans
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t)
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)
      F.continuous

theorem FundamentalGroupVanKampen.rectangleHorizontalVertical_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleHorizontalVertical s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨le_rfl, hst⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, hab, le_rfl⟩

theorem FundamentalGroupVanKampen.rectangleVerticalHorizontal_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleVerticalHorizontal s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, le_rfl, hab⟩
  · intro u
    exact ⟨⟨hst, le_rfl⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩

def FundamentalGroupVanKampen.rectangleBoundaryHomotopy {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    Path.Homotopy (((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t))
      (((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b)) :=
  ((squarePathHomotopy (rectangleHorizontalVertical s t a b)
            (rectangleVerticalHorizontal s t a b)).map
        F).cast
    (rectangleHorizontalVertical_map F s t a b) (rectangleVerticalHorizontal_map F s t a b)

theorem FundamentalGroupVanKampen.rectangleBoundaryHomotopy_apply {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval))
    (u : (unitInterval) × (unitInterval)) :
    rectangleBoundaryHomotopy F s t a b u =
      F
        (squarePathHomotopy (rectangleHorizontalVertical s t a b)
          (rectangleVerticalHorizontal s t a b) u) :=
  rfl

theorem FundamentalGroupVanKampen.rectangleBoundaryHomotopy_mem {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) (hst : s ≤ t)
    (hab : a ≤ b) {A : Set X} (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ A)
    (u : (unitInterval) × (unitInterval)) : rectangleBoundaryHomotopy F s t a b u ∈ A := by
  rw [rectangleBoundaryHomotopy_apply]
  exact
    hcell _
      (squarePathHomotopy_mem_rectangle _ _ s t a b
        (rectangleHorizontalVertical_mem s t a b hst hab)
        (rectangleVerticalHorizontal_mem s t a b hst hab) u)

theorem FundamentalGroupVanKampen.PathValue.square_cell_of_local {X : Type*} [TopologicalSpace X]
    {ι G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hExt : V.Extends L)
    (hL : L.HomotopyInvariant) (i : ι) (F : C((unitInterval) × (unitInterval), X))
    (s t a b : (unitInterval)) (hst : s ≤ t) (hab : a ≤ b)
    (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ U i) :
    V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath a b) *
        V.value ((FundamentalGroupVanKampen.squareVertical F b).subpath s t) =
      V.value ((FundamentalGroupVanKampen.squareVertical F a).subpath s t) *
        V.value ((FundamentalGroupVanKampen.squareHorizontal F t).subpath a b) := by
  let H := FundamentalGroupVanKampen.rectangleBoundaryHomotopy F s t a b
  have hH : ∀ u, H u ∈ U i :=
    FundamentalGroupVanKampen.rectangleBoundaryHomotopy_mem F s t a b hst hab hcell
  have hp :
    ∀ u,
      ((FundamentalGroupVanKampen.squareHorizontal F s).subpath a b).trans
          ((FundamentalGroupVanKampen.squareVertical F b).subpath s t) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_zero_left u)).mp (hH (0, u))
  have hq :
    ∀ u,
      ((FundamentalGroupVanKampen.squareVertical F a).subpath s t).trans
          ((FundamentalGroupVanKampen.squareHorizontal F t).subpath a b) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_one_left u)).mp (hH (1, u))
  calc
    _ =
        V.value
          (((FundamentalGroupVanKampen.squareHorizontal F s).subpath a b).trans
            ((FundamentalGroupVanKampen.squareVertical F b).subpath s t)) :=
      (V.trans _ _).symm
    _ = L.value i _ hp := (hExt i _ hp)
    _ = L.value i _ hq := (hL i _ _ hp hq H hH)
    _ =
        V.value
          (((FundamentalGroupVanKampen.squareVertical F a).subpath s t).trans
            ((FundamentalGroupVanKampen.squareHorizontal F t).subpath a b)) :=
      (hExt i _ hq).symm
    _ = _ := V.trans _ _

theorem FundamentalGroupVanKampen.PathValue.value_eq_one_of_constant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} (p : Path x y) (hp : ∀ t, p t = x) : V.value p = 1 := by
  have hy : y = x := p.target.symm.trans (hp 1)
  subst y
  have heq : p = Path.refl x := by
    ext t
    exact hp t
  rw [heq, V.refl]

theorem FundamentalGroupVanKampen.PathValue.square_strip {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    (F : C((unitInterval) × (unitInterval), X)) (s t : (unitInterval)) (d : ℕ → (unitInterval))
    (hmono : Monotone d) (n : ℕ)
    (hcell :
      ∀ k < n,
        V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d k) (d (k + 1))) *
            V.value ((FundamentalGroupVanKampen.squareVertical F (d (k + 1))).subpath s t) =
          V.value ((FundamentalGroupVanKampen.squareVertical F (d k)).subpath s t) *
            V.value
              ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d k) (d (k + 1)))) :
    V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
        V.value ((FundamentalGroupVanKampen.squareVertical F (d n)).subpath s t) =
      V.value ((FundamentalGroupVanKampen.squareVertical F (d 0)).subpath s t) *
        V.value ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d 0) (d n)) := by
  induction n with
  | zero => simp only [Path.subpath_self, V.refl, one_mul, mul_one]
  | succ n ih =>
    have hprev := ih (fun k hk => hcell k (Nat.lt_succ_of_lt hk))
    rw [V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)),
      V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))]
    calc
      _ =
          V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value
                ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d n) (d (n + 1))) *
              V.value ((FundamentalGroupVanKampen.squareVertical F (d (n + 1))).subpath s t)) :=
        mul_assoc _ _ _
      _ =
          V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value ((FundamentalGroupVanKampen.squareVertical F (d n)).subpath s t) *
              V.value
                ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d n) (d (n + 1)))) := by
        rw [hcell n (Nat.lt_succ_self n)]
      _ =
          (V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
              V.value ((FundamentalGroupVanKampen.squareVertical F (d n)).subpath s t)) *
            V.value
              ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d n) (d (n + 1))) :=
        (mul_assoc _ _ _).symm
      _ =
          (V.value ((FundamentalGroupVanKampen.squareVertical F (d 0)).subpath s t) *
              V.value ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d 0) (d n))) *
            V.value
              ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d n) (d (n + 1))) := by
        rw [hprev]
      _ = _ := mul_assoc _ _ _

theorem FundamentalGroupVanKampen.PathValue.value_squareHorizontal_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s : (unitInterval)) :
    V.value (FundamentalGroupVanKampen.squareHorizontal H.toContinuousMap s) =
      V.value (H.eval s) := by
  have heq :
    FundamentalGroupVanKampen.squareHorizontal H.toContinuousMap s =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  rw [heq, V.value_cast]

theorem FundamentalGroupVanKampen.PathValue.value_squareVertical_homotopy_zero {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroupVanKampen.squareVertical H.toContinuousMap 0).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 0) = H (s, 0)
  simp only [Path.Homotopy.source]

theorem FundamentalGroupVanKampen.PathValue.value_squareVertical_homotopy_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroupVanKampen.squareVertical H.toContinuousMap 1).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 1) = H (s, 1)
  simp only [Path.Homotopy.target]

theorem FundamentalGroupVanKampen.PathValue.value_eq_of_homotopy_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroupVanKampen.PathValue X G)
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
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

theorem FundamentalGroupVanKampen.PathValue.homotopyInvariant_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroupVanKampen.PathValue X G)
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (hExt : V.Extends L) (hL : L.HomotopyInvariant) :
    V.HomotopyInvariant := by
  intro x y p q h
  obtain ⟨H⟩ := h
  exact V.value_eq_of_homotopy_of_open_cover L hopen hcover hExt hL p q H

def FundamentalGroupVanKampen.TwoOpenCover.globalPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroupVanKampen.PathValue X G :=
  (D.localPathValue fU fV hf).extension D.chart_open D.chart_cover

theorem FundamentalGroupVanKampen.TwoOpenCover.globalPathValue_extends {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).Extends (D.localPathValue fU fV hf) :=
  (D.localPathValue fU fV hf).extension_extends D.chart_open D.chart_cover

theorem FundamentalGroupVanKampen.TwoOpenCover.globalPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).HomotopyInvariant :=
  FundamentalGroupVanKampen.PathValue.homotopyInvariant_of_open_cover (D.globalPathValue fU fV hf)
    (D.localPathValue fU fV hf) D.chart_open D.chart_cover (D.globalPathValue_extends fU fV hf)
    (D.localPathValue_homotopyInvariant fU fV hf)

def FundamentalGroupVanKampen.TwoOpenCover.lift {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroup X D.base →* G :=
  (D.globalPathValue fU fV hf).fundamentalGroupHom (D.globalPathValue_homotopyInvariant fU fV hf)
    D.base

theorem FundamentalGroupVanKampen.TwoOpenCover.lift_mk_of_mem {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i : Bool) (p : Path D.base D.base)
    (hp : ∀ t, p t ∈ D.chart i) :
    D.lift fU fV hf (Path.Homotopic.Quotient.mk p) = (D.localValue fU fV i p hp)⁻¹ :=
  congrArg (fun a : G => a⁻¹) (D.globalPathValue_extends fU fV hf i p hp)

theorem FundamentalGroupVanKampen.TwoOpenCover.lift_comp_inclusionU {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomU = fU := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.false (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

theorem FundamentalGroupVanKampen.TwoOpenCover.lift_comp_inclusionV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomV = fV := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.true (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

abbrev FundamentalGroupVanKampen.TwoOpenCover.ChartGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :=
  FundamentalGroup (D.chart i) (D.baseChart i)

def FundamentalGroupVanKampen.TwoOpenCover.overlapHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : (i : Bool) → D.OverlapGroup →* D.ChartGroup i
  | false => D.overlapHomU
  | true => D.overlapHomV

def FundamentalGroupVanKampen.TwoOpenCover.inclusionHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    (i : Bool) → D.ChartGroup i →* FundamentalGroup X D.base
  | false => D.inclusionHomU
  | true => D.inclusionHomV

theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHom_comp_overlapHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    (D.inclusionHom i).comp (D.overlapHom i) = D.inclusionHomU.comp D.overlapHomU := by
  cases i
  · rfl
  · exact D.inclusionHom_compatible.symm

abbrev FundamentalGroupVanKampen.TwoOpenCover.Pushout {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  Monoid.PushoutI D.overlapHom

def FundamentalGroupVanKampen.TwoOpenCover.pushoutOfU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.UGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.false

def FundamentalGroupVanKampen.TwoOpenCover.pushoutOfV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.VGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.true

def FundamentalGroupVanKampen.TwoOpenCover.pushoutBase {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.OverlapGroup →* D.Pushout :=
  Monoid.PushoutI.base D.overlapHom

theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutOfU_comp_overlapHomU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutOfU.comp D.overlapHomU = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.false

theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutOfV_comp_overlapHomV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutOfV.comp D.overlapHomV = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.true

theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutOf_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.Compatible D.pushoutOfU D.pushoutOfV :=
  D.pushoutOfU_comp_overlapHomU.trans D.pushoutOfV_comp_overlapHomV.symm

def FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.Pushout →* FundamentalGroup X D.base :=
  Monoid.PushoutI.lift D.inclusionHom (D.inclusionHomU.comp D.overlapHomU)
    D.inclusionHom_comp_overlapHom

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool)
    (g : D.ChartGroup i) :
    D.pushoutToFundamentalGroup (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  Monoid.PushoutI.lift_of _ _ _ g

theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    D.pushoutToFundamentalGroup.comp (Monoid.PushoutI.of i) = D.inclusionHom i := by
  ext g
  exact D.pushoutToFundamentalGroup_of i g

theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_ofU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfU = D.inclusionHomU :=
  D.pushoutToFundamentalGroup_comp_of Bool.false

theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_ofV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfV = D.inclusionHomV :=
  D.pushoutToFundamentalGroup_comp_of Bool.true

def FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    FundamentalGroup X D.base →* D.Pushout :=
  D.lift D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

theorem FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionU
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomU = D.pushoutOfU :=
  D.lift_comp_inclusionU D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

theorem FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionV
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomV = D.pushoutOfV :=
  D.lift_comp_inclusionV D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

theorem
  FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
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

theorem
  FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.fundamentalGroupToPushout =
      MonoidHom.id (FundamentalGroup X D.base) := by
  apply D.hom_ext
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionU,
      D.pushoutToFundamentalGroup_comp_ofU, MonoidHom.id_comp]
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionV,
      D.pushoutToFundamentalGroup_comp_ofV, MonoidHom.id_comp]

def FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.Pushout ≃* FundamentalGroup X D.base
    where
  toFun := D.pushoutToFundamentalGroup
  invFun := D.fundamentalGroupToPushout
  left_inv g := DFunLike.congr_fun D.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup g
  right_inv g := DFunLike.congr_fun D.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout g
  map_mul' := D.pushoutToFundamentalGroup.map_mul

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv_of {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (g : D.ChartGroup i) :
    D.pushoutEquiv (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  D.pushoutToFundamentalGroup_of i g

theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X)
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
end Mathoverflow1973
