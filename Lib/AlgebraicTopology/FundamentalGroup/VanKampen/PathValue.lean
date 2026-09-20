/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar, Fabian Franz
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Basic

/-!
# Local-to-global path values for a two-open cover

This module proves the existence half of the van Kampen universal property: a pair of
homomorphisms out of `π₁(U)` and `π₁(V)` agreeing on `π₁(U ∩ V)` extends to a homomorphism out
of `π₁(X)` (`TwoOpenCover.lift`, with `lift_comp_inclusionU` and `lift_comp_inclusionV`).  The
extension is built by subdividing a loop into pieces lying in a single member of the cover and
multiplying their local values, and is well defined by a corresponding subdivision of a homotopy
into rectangles.

The path-factorization argument was adapted from Sebastian Kumar's Mathlib PR 28246, source commit
`037ad801e1e5a5b7aa1750957c07f7769812effc`.

## References

* [A. Hatcher, *Algebraic topology*][hatcher02], Theorem 1.20 (van Kampen).
* [T. tom Dieck, *Algebraic topology*][tomDieck08], §2.6.
-/

@[expose] public noncomputable section

open Set Function Topology
open scoped ContinuousMap Interval

/-- The chosen path from the basepoint to `x`, viewed inside the member `chart i` of the cover. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.chartPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path (D.baseChart i) x :=
  FundamentalGroup.VanKampen.Cocone.pathIn (D.pathTo x.val) (D.base_mem_chart i) x.property
    (D.pathTo_mem i x.val x.property)

/-- The chosen path inside a chart from the basepoint to itself is constant. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.chartPath_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) :
    D.chartPath i (D.baseChart i) = Path.refl (D.baseChart i) := by
  simp only [chartPath, baseChart, D.pathTo_base, FundamentalGroup.VanKampen.Cocone.pathIn_refl]

/-- The homotopy class of the chosen path inside a chart. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.chartPathClass {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path.Homotopic.Quotient (D.baseChart i) x :=
  Path.Homotopic.Quotient.mk (D.chartPath i x)

/-- The class of the chosen path from the basepoint to itself is the identity. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.chartPathClass_base {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) :
    D.chartPathClass i (D.baseChart i) = Path.Homotopic.Quotient.refl (D.baseChart i) := by
  simp only [chartPathClass, D.chartPath_base, Path.Homotopic.Quotient.mk_refl]

/-- Close a path in a chart into a loop at the basepoint of that chart by prefixing and
suffixing the chosen paths, and take its class in `π₁(chart i)`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.closePath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) {x y : D.chart i} (p : Path x y) :
    FundamentalGroup (D.chart i) (D.baseChart i) :=
  FundamentalGroup.VanKampen.Cocone.PathClass.basedLoop (D.chartPathClass i)
    (Path.Homotopic.Quotient.mk p)

/-- Closing a constant path gives the trivial loop. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.closePath_refl {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    D.closePath i (Path.refl x) = 1 :=
  FundamentalGroup.VanKampen.Cocone.PathClass.basedLoop_refl _ _

/-- Closing a concatenation gives the product of the closed loops, in the opposite order. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.closePath_trans {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool) {x y z : D.chart i} (p : Path x y)
    (q : Path y z) : D.closePath i (p.trans q) = D.closePath i q * D.closePath i p := by
  exact
    FundamentalGroup.VanKampen.Cocone.PathClass.basedLoop_trans (D.chartPathClass i)
      (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q)

/-- Homotopic paths close to the same loop. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.closePath_homotopic {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool)
    {x y : D.chart i} {p q : Path x y} (hpq : Path.Homotopic p q) :
    D.closePath i p = D.closePath i q := by
  unfold closePath
  rw [Path.Homotopic.Quotient.eq.mpr hpq]

/-- Closing a loop already based at the basepoint returns its own class. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.closePath_loop {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (i : Bool)
    (p : Path (D.baseChart i) (D.baseChart i)) : D.closePath i p = Path.Homotopic.Quotient.mk p :=
  by
  simp only [closePath, FundamentalGroup.VanKampen.Cocone.PathClass.basedLoop, D.chartPathClass_base,
    Path.Homotopic.Quotient.refl_trans]
  exact Path.Homotopic.Quotient.trans_refl _

/-- The homomorphism attached to the indexed chart: `fU` for `U` and `fV` for `V`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.chartHom {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) : FundamentalGroup (D.chart i) (D.baseChart i) →* G := by
  cases i
  · exact fU
  · exact fV

/-- The value in `G` of a path contained in `chart i`: the image under `fU` or `fV` of the
inverse of the loop obtained by closing the path. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.chart i) : G :=
  (D.chartHom fU fV i
      (D.closePath i
        (FundamentalGroup.VanKampen.Cocone.pathIn (S := (D.chart i : Set X)) p (by simpa using hp 0)
          (by simpa using hp 1) hp)))⁻¹

/-- The local value of a constant path is trivial. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_refl {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) (x : X) (hx : ∀ t, Path.refl x t ∈ D.chart i) :
    D.localValue fU fV i (Path.refl x) hx = 1 := by
  simp only [localValue, FundamentalGroup.VanKampen.Cocone.pathIn_refl, D.closePath_refl, map_one,
    inv_one]

/-- The local value of a concatenation is the product of the local values. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_trans {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (hpq : ∀ t, p.trans q t ∈ D.chart i) :
    D.localValue fU fV i (p.trans q) hpq =
      D.localValue fU fV i p hp * D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  have hz : z ∈ D.chart i := by simpa using hq 1
  unfold localValue
  rw [FundamentalGroup.VanKampen.Cocone.pathIn_trans p q hx hy hz hp hq hpq, D.closePath_trans, map_mul,
    mul_inv_rev]

/-- The local value of a restriction splits as the product of the local values of two
consecutive restrictions. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y)
    (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (hpab : ∀ t, p.subpath a b t ∈ D.chart i)
    (hpbc : ∀ t, p.subpath b c t ∈ D.chart i) (hpac : ∀ t, p.subpath a c t ∈ D.chart i) :
    D.localValue fU fV i (p.subpath a c) hpac =
      D.localValue fU fV i (p.subpath a b) hpab * D.localValue fU fV i (p.subpath b c) hpbc := by
  have ha : p a ∈ D.chart i := by simpa using hpab 0
  have hb : p b ∈ D.chart i := by simpa using hpab 1
  have hc : p c ∈ D.chart i := by simpa using hpbc 1
  have H :=
    FundamentalGroup.VanKampen.Cocone.subpathTransSubpathIn p a b c hab hbc ha hb hc hpab hpbc hpac
  unfold localValue
  rw [← D.closePath_homotopic i ⟨H⟩, D.closePath_trans, map_mul, mul_inv_rev]

/-- Homotopic paths with a homotopy inside the chart have the same local value. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (H : Path.Homotopy p q)
    (hH : ∀ s, H s ∈ D.chart i) : D.localValue fU fV i p hp = D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  unfold localValue
  rw [D.closePath_homotopic i ⟨FundamentalGroup.VanKampen.Cocone.homotopyIn p q hx hy hp hq H hH⟩]

/-- The chosen path from the basepoint to `x`, viewed inside `U ∩ V`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (x : D.overlap) : Path D.baseOverlapPoint x :=
  FundamentalGroup.VanKampen.Cocone.pathIn (S := (D.overlap : Set X)) (D.pathTo x.val) ⟨D.baseU, D.baseV⟩
    x.property
    (fun t =>
      ⟨D.pathTo_mem Bool.false x.val x.property.1 t, D.pathTo_mem Bool.true x.val x.property.2 t⟩)

/-- Pushing the chosen path in `U ∩ V` into `U` gives the chosen path in `U`. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapPath_map_U {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToU.continuous = D.chartPath Bool.false (D.overlapToU x) := by
  ext t
  rfl

/-- Pushing the chosen path in `U ∩ V` into `V` gives the chosen path in `V`. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapPath_map_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToV.continuous = D.chartPath Bool.true (D.overlapToV x) := by
  ext t
  rfl

/-- Close a path in `U ∩ V` into a loop at the basepoint and take its class in `π₁(U ∩ V)`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapClose {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.OverlapGroup :=
  FundamentalGroup.VanKampen.Cocone.PathClass.basedLoop
    (fun x => Path.Homotopic.Quotient.mk (D.overlapPath x)) (Path.Homotopic.Quotient.mk p)

/-- The map `π₁(U ∩ V) → π₁(U)` sends a closed loop of `U ∩ V` to the loop closed in `U`. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapHomU_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomU (D.overlapClose p) = D.closePath Bool.false (p.map D.overlapToU.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToU.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.false (D.overlapToU x)).trans (p.map D.overlapToU.continuous)).trans
          (D.chartPath Bool.false (D.overlapToU y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_U, D.overlapPath_map_U]
  rfl

/-- The map `π₁(U ∩ V) → π₁(V)` sends a closed loop of `U ∩ V` to the loop closed in `V`. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.overlapHomV_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomV (D.overlapClose p) = D.closePath Bool.true (p.map D.overlapToV.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToV.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.true (D.overlapToV x)).trans (p.map D.overlapToV.continuous)).trans
          (D.chartPath Bool.true (D.overlapToV y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_V, D.overlapPath_map_V]
  rfl

/-- For compatible `fU` and `fV`, a path lying in both `U` and `V` gets the same value from
either chart. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_compatible_UV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ D.U) (hV : ∀ t, p t ∈ D.V) :
    D.localValue fU fV Bool.false p hU = D.localValue fU fV Bool.true p hV := by
  have hxU : x ∈ D.U := by simpa using hU 0
  have hxV : x ∈ D.V := by simpa using hV 0
  have hyU : y ∈ D.U := by simpa using hU 1
  have hyV : y ∈ D.V := by simpa using hV 1
  let pI :=
    FundamentalGroup.VanKampen.Cocone.pathIn (S := (D.overlap : Set X)) p ⟨hxU, hxV⟩ ⟨hyU, hyV⟩
      (fun t => ⟨hU t, hV t⟩)
  have hpU : pI.map D.overlapToU.continuous = FundamentalGroup.VanKampen.Cocone.pathIn p hxU hyU hU := by
    ext t
    rfl
  have hpV : pI.map D.overlapToV.continuous = FundamentalGroup.VanKampen.Cocone.pathIn p hxV hyV hV := by
    ext t
    rfl
  have h := DFunLike.congr_fun hf (D.overlapClose pI)
  change fU (D.overlapHomU (D.overlapClose pI)) = fV (D.overlapHomV (D.overlapClose pI)) at h
  have hU' := congrArg fU ((D.overlapHomU_close pI).trans (congrArg (D.closePath Bool.false) hpU))
  have hV' := congrArg fV ((D.overlapHomV_close pI).trans (congrArg (D.closePath Bool.true) hpV))
  exact congrArg (fun a : G => a⁻¹) (hU'.symm.trans (h.trans hV'))

/-- For compatible `fU` and `fV`, the local value of a path is independent of the chart used. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_compatible {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i j : Bool) {x y : X}
    (p : Path x y) (hi : ∀ t, p t ∈ D.chart i) (hj : ∀ t, p t ∈ D.chart j) :
    D.localValue fU fV i p hi = D.localValue fU fV j p hj := by
  cases i <;> cases j
  · rfl
  · exact D.localValue_compatible_UV fU fV hf p hi hj
  · exact (D.localValue_compatible_UV fU fV hf p hj hi).symm
  · rfl

/-- The local path value attached to a compatible pair of homomorphisms out of `π₁(U)` and
`π₁(V)`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    FundamentalGroup.VanKampen.Cocone.LocalPathValue (fun i => (D.chart i : Set X)) G
    where
  value := D.localValue fU fV
  refl := D.localValue_refl fU fV
  trans := D.localValue_trans fU fV
  subpath_mul := D.localValue_subpath_mul fU fV
  compatible := D.localValue_compatible fU fV hf

/-- The local path value of a compatible pair is homotopy invariant. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.localPathValue fU fV hf).HomotopyInvariant :=
  D.localValue_homotopy fU fV

/-- The local value of a loop of `chart i` pushed into `X` is the inverse of its image under the
corresponding homomorphism. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.localValue_map_loop {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
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

/-- A homotopy-invariant path value induces a homomorphism `π₁(X, o) → G`, sending the class of
a loop to the inverse of its value. -/
def FundamentalGroup.VanKampen.Cocone.PathValue.fundamentalGroupHom {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G) (hV : V.HomotopyInvariant)
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

/-- The induced homomorphism sends the class of a loop to the inverse of its value. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.PathValue.fundamentalGroupHom_mk {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G]
    (V : FundamentalGroup.VanKampen.Cocone.PathValue X G) (hV : V.HomotopyInvariant) (o : X)
    (p : Path o o) :
    V.fundamentalGroupHom hV o (Path.Homotopic.Quotient.mk p) = (V.value p)⁻¹ :=
  rfl

/-- If the restriction of `p` to `[a, b]` stays in `s`, then `p t ∈ s` for every `t ∈ [a, b]`. -/
theorem FundamentalGroup.VanKampen.Cocone.mem_of_subpath_mem {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t, p.subpath a b t ∈ s) {t : (unitInterval)} (ht : t ∈ Set.Icc a b) : p t ∈ s := by
  have hsub : Set.range (p.subpath a b) ⊆ s := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hsub
  exact hsub ⟨t, ht, rfl⟩

/-- A restriction of `p` to a subinterval of `[a, b]` stays in any set containing the
restriction to `[a, b]`. -/
theorem FundamentalGroup.VanKampen.Cocone.subpath_mem_mono {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b c d : (unitInterval)} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c)
    (hdb : d ≤ b) {s : Set X} (hp : ∀ t, p.subpath a b t ∈ s) : ∀ t, p.subpath c d t ∈ s := by
  apply subpath_mem_of_mem_Icc p hcd
  intro t ht
  exact mem_of_subpath_mem p hab hp ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- Lebesgue-number subdivision of a path relative to an open cover: the parameter interval can
be cut into finitely many closed pieces each of which `p` maps into a single member of the
cover. -/
theorem FundamentalGroup.VanKampen.Cocone.exists_path_subdivision {X : Type*} [TopologicalSpace X]
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

/-- `F` is a primitive of `L` along `p` if, for every subinterval `[a, b]` on which `p` stays in
one member of the cover, `F b = F a * L.value (p|[a,b])`. -/
def FundamentalGroup.VanKampen.Cocone.LocalPathValue.IsPrimitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

/-- `F` is a primitive of `L` along `p` up to the parameter `r` if the primitive equation holds
for all subintervals of `[0, r]`. -/
def FundamentalGroup.VanKampen.Cocone.LocalPathValue.IsPrimitiveUpTo {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) (r : (unitInterval)) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → b ≤ r → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

/-- The constant function `1` is a primitive up to the parameter `0`. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.isPrimitiveUpTo_zero {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) {x y : X} (p : Path x y) :
    L.IsPrimitiveUpTo p (fun _ ↦ 1) 0 := by
  intro a b hab hb i hi
  have ha0 : a = 0 := le_antisymm (hab.trans hb) bot_le
  have hb0 : b = 0 := le_antisymm hb bot_le
  subst a
  subst b
  simp only [Path.subpath_self, L.refl, mul_one]

/-- A primitive up to `a` extends to a primitive up to `b`, provided `p` maps `[a, b]` into a
single member of the cover. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.exists_primitiveUpTo_step {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} {a b : (unitInterval)} (_hab : a ≤ b) (i : ι)
    (hi : ∀ t ∈ Set.Icc a b, p t ∈ U i) (hF : L.IsPrimitiveUpTo p F a) :
    ∃ H : (unitInterval) → G, H 0 = F 0 ∧ L.IsPrimitiveUpTo p H b := by
  classical
  let memi (s t : (unitInterval)) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ∀ u, p.subpath s t u ∈ U i :=
    FundamentalGroup.VanKampen.Cocone.subpath_mem_of_mem_Icc p hst
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
      FundamentalGroup.VanKampen.Cocone.subpath_mem_mono p hst hsa le_rfl hat hj
    have hjat : ∀ u, p.subpath a t u ∈ U j :=
      FundamentalGroup.VanKampen.Cocone.subpath_mem_mono p hst hat hsa le_rfl hj
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

/-- Along any path, a local path value for an open cover has a primitive normalized by `F 0 = 1`. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.exists_primitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    ∃ F : (unitInterval) → G, F 0 = 1 ∧ L.IsPrimitive p F := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroup.VanKampen.Cocone.exists_path_subdivision hopen hcover p
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

/-- Two primitives of the same local path value along the same path that agree at `0` are equal. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.primitive_unique {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) {F H : (unitInterval) → G}
    (hF : L.IsPrimitive p F) (hH : L.IsPrimitive p H) (h0 : F 0 = H 0) : F = H := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroup.VanKampen.Cocone.exists_path_subdivision hopen hcover p
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
        FundamentalGroup.VanKampen.Cocone.subpath_mem_of_mem_Icc p hts
          (fun u hu ↦ hi u ⟨hu.1, hu.2.trans hs⟩)
      rw [hF (t m) s hts i hlocal, hH (t m) s hts i hlocal, ih (t m) le_rfl]
  funext s
  exact hprefix n s (by rw [hn]; exact le_top)

/-- The affine parametrization of `[a, b]` by the unit interval is monotone. -/
theorem FundamentalGroup.VanKampen.Cocone.convexComb_monotone {a b : (unitInterval)} (hab : a ≤ b) :
    Monotone (Set.Icc.convexComb a b) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + s * b ≤ (1 - (t : ℝ)) * a + t * b
  have hab' : (a : ℝ) ≤ b := hab
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hst')]

/-- Composing two affine reparametrizations of the unit interval is again affine. -/
theorem FundamentalGroup.VanKampen.Cocone.convexComb_comp (a b s t u : (unitInterval)) :
    Set.Icc.convexComb a b (Set.Icc.convexComb s t u) =
      Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u := by
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  ring

/-- Restricting a restriction of a path is the restriction over the correspondingly rescaled
subinterval. -/
theorem FundamentalGroup.VanKampen.Cocone.subpath_subpath {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (a b s t : (unitInterval)) :
    (p.subpath a b).subpath s t =
      p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) := by
  ext u
  change
    p (Set.Icc.convexComb a b (Set.Icc.convexComb s t u)) =
      p (Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u)
  rw [convexComb_comp]

/-- The midpoint `1/2` of the unit interval. -/
def FundamentalGroup.VanKampen.Cocone.intervalHalf : (unitInterval) :=
  ⟨1 / 2, by norm_num⟩

/-- On the first half of the parameter interval, a concatenation is the first path. -/
theorem FundamentalGroup.VanKampen.Cocone.trans_convexComb_first_half {X : Type*} [TopologicalSpace X]
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

/-- On the second half of the parameter interval, a concatenation is the second path. -/
theorem FundamentalGroup.VanKampen.Cocone.trans_convexComb_second_half {X : Type*} [TopologicalSpace X]
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

/-- A concatenation passes through the joining point at the parameter `1/2`. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.trans_apply_intervalHalf {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) : (p.trans q) intervalHalf = y := by
  simpa using trans_convexComb_first_half p q 1

/-- The restriction of `p.trans q` to `[0, 1/2]` is `p`. -/
theorem FundamentalGroup.VanKampen.Cocone.trans_subpath_first_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath 0 intervalHalf =
      p.cast (p.trans q).source (trans_apply_intervalHalf p q) := by
  ext t
  exact trans_convexComb_first_half p q t

/-- The restriction of `p.trans q` to `[1/2, 1]` is `q`. -/
theorem FundamentalGroup.VanKampen.Cocone.trans_subpath_second_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath intervalHalf 1 =
      q.cast (trans_apply_intervalHalf p q) (p.trans q).target := by
  ext t
  exact trans_convexComb_second_half p q t

/-- Equal paths have equal local values. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.value_eq_of_path_eq {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (i : ι) {x y : X} {p q : Path x y}
    (h : p = q) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i) : L.value i p hp = L.value i q hq := by
  cases h
  rfl

/-- A primitive along `p` restricts, after normalization at the left endpoint, to a primitive
along any restriction of `p`. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.isPrimitive_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} (hF : L.IsPrimitive p F) (a b : (unitInterval)) (hab : a ≤ b) :
    L.IsPrimitive (p.subpath a b) (fun t => (F a)⁻¹ * F (Set.Icc.convexComb a b t)) := by
  intro s t hst i hi
  have heq := FundamentalGroup.VanKampen.Cocone.subpath_subpath p a b s t
  have hlocal : ∀ v, p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) v ∈ U i := by
    intro v
    rw [← heq]
    exact hi v
  have hv := L.value_eq_of_path_eq i heq hi hlocal
  have hstep :=
    hF (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t)
      (FundamentalGroup.VanKampen.Cocone.convexComb_monotone hab hst) i hlocal
  change
    (F a)⁻¹ * F (Set.Icc.convexComb a b t) =
      ((F a)⁻¹ * F (Set.Icc.convexComb a b s)) * L.value i ((p.subpath a b).subpath s t) hi
  rw [hv, hstep, mul_assoc]
  rfl

/-- The chosen primitive of `L` along `p`, normalized by `F 0 = 1`. -/
def FundamentalGroup.VanKampen.Cocone.LocalPathValue.transport {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : (unitInterval) → G :=
  (L.exists_primitive hopen hcover p).choose

/-- The chosen primitive takes the value `1` at the parameter `0`. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.transport_zero {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.transport hopen hcover p 0 = 1 :=
  (L.exists_primitive hopen hcover p).choose_spec.1

/-- The chosen primitive is indeed a primitive. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.transport_isPrimitive {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.IsPrimitive p (L.transport hopen hcover p) :=
  (L.exists_primitive hopen hcover p).choose_spec.2

/-- The primitive along a restriction of `p` is the primitive along `p`, normalized at the left
endpoint of the subinterval. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.transport_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
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

/-- The global value of a path: the value at the parameter `1` of the chosen primitive. -/
def FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] {U : ι → Set X} (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : G :=
  L.transport hopen hcover p 1

/-- The global value of a path is unchanged by casting its endpoints. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y) :
    L.rawValue hopen hcover (p.cast hx hy) = L.rawValue hopen hcover p := by
  cases hx
  cases hy
  rfl

/-- The restriction of a path to the whole interval has the same global value. -/
@[simp]
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.rawValue hopen hcover (p.subpath 0 1) = L.rawValue hopen hcover p := by
  rw [Path.subpath_zero_one, L.rawValue_cast]

/-- The global value of a restriction is the corresponding increment of the primitive. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_subpath {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b : (unitInterval))
    (hab : a ≤ b) :
    L.rawValue hopen hcover (p.subpath a b) =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p b := by
  simpa only [rawValue, Set.Icc.convexComb_one] using L.transport_subpath hopen hcover p a b hab 1

/-- For a path contained in a single member of the cover, the global value is the local value. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_local {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
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

/-- The global value of a constant path is trivial. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_refl {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (x : X) : L.rawValue hopen hcover (Path.refl x) = 1 := by
  have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hp : ∀ t, Path.refl x t ∈ U i := fun _ => hi
  rw [L.rawValue_local hopen hcover i (Path.refl x) hp, L.refl]

/-- The global value of a restriction splits as the product of the global values of two
consecutive restrictions. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) :
    L.rawValue hopen hcover (p.subpath a c) =
      L.rawValue hopen hcover (p.subpath a b) * L.rawValue hopen hcover (p.subpath b c) := by
  rw [L.rawValue_subpath hopen hcover p a c (hab.trans hbc),
    L.rawValue_subpath hopen hcover p a b hab, L.rawValue_subpath hopen hcover p b c hbc,
    mul_assoc, mul_inv_cancel_left]

/-- The global value of a concatenation is the product of the global values. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_trans {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y z : X} (p : Path x y) (q : Path y z) :
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover p * L.rawValue hopen hcover q :=
  by
  calc
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover ((p.trans q).subpath 0 1) :=
      (L.rawValue_subpath_zero_one hopen hcover (p.trans q)).symm
    _ =
        L.rawValue hopen hcover ((p.trans q).subpath 0 FundamentalGroup.VanKampen.Cocone.intervalHalf) *
          L.rawValue hopen hcover
            ((p.trans q).subpath FundamentalGroup.VanKampen.Cocone.intervalHalf 1) :=
      (L.rawValue_subpath_mul hopen hcover (p.trans q) 0 FundamentalGroup.VanKampen.Cocone.intervalHalf 1
        unitInterval.nonneg' unitInterval.le_one')
    _ = L.rawValue hopen hcover p * L.rawValue hopen hcover q := by
      rw [FundamentalGroup.VanKampen.Cocone.trans_subpath_first_half,
        FundamentalGroup.VanKampen.Cocone.trans_subpath_second_half, L.rawValue_cast, L.rawValue_cast]

/-- The global path value extending a local path value over an open cover. -/
def FundamentalGroup.VanKampen.Cocone.LocalPathValue.extension {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : FundamentalGroup.VanKampen.Cocone.PathValue X G
    where
  value := FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue L hopen hcover
  refl := FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_refl L hopen hcover
  trans := FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_trans L hopen hcover
  subpath_mul := FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_subpath_mul L hopen hcover

/-- The global path value agrees with the local one on paths contained in a member of the cover. -/
theorem FundamentalGroup.VanKampen.Cocone.LocalPathValue.extension_extends {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : (L.extension hopen hcover).Extends L := by
  intro i x y p hp
  exact FundamentalGroup.VanKampen.Cocone.LocalPathValue.rawValue_local L hopen hcover i p hp

/-- The horizontal path `t ↦ F (s, t)` of a square `F`. -/
def FundamentalGroup.VanKampen.Cocone.squareHorizontal {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s : (unitInterval)) : Path (F (s, 0)) (F (s, 1))
    where
  toFun t := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- The vertical path `s ↦ F (s, t)` of a square `F`. -/
def FundamentalGroup.VanKampen.Cocone.squareVertical {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (t : (unitInterval)) : Path (F (0, t)) (F (1, t))
    where
  toFun s := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

/-- Any two paths in the square `[0,1] × [0,1]` with the same endpoints are homotopic, by the
straight-line homotopy taken coordinatewise. -/
def FundamentalGroup.VanKampen.Cocone.squarePathHomotopy {x y : (unitInterval) × (unitInterval)}
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

/-- A convex combination of two points of `[s, t]` lies in `[s, t]`. -/
theorem FundamentalGroup.VanKampen.Cocone.convexComb_mem_Icc {s t u v : (unitInterval)}
    (hu : u ∈ Set.Icc s t) (hv : v ∈ Set.Icc s t) (r : (unitInterval)) :
    Set.Icc.convexComb u v r ∈ Set.Icc s t := by
  change (Set.Icc.convexComb u v r : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ)
  exact
    convex_Icc (s : ℝ) (t : ℝ) (show (u : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hu)
      (show (v : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hv) (unitInterval.one_minus_nonneg r)
      (unitInterval.nonneg r) (sub_add_cancel _ _)

/-- The straight-line homotopy between two paths inside a rectangle stays inside that rectangle. -/
theorem FundamentalGroup.VanKampen.Cocone.squarePathHomotopy_mem_rectangle
    {x y : (unitInterval) × (unitInterval)} (p q : Path x y) (s t a b : (unitInterval))
    (hp : ∀ u, p u ∈ Set.Icc s t ×ˢ Set.Icc a b) (hq : ∀ u, q u ∈ Set.Icc s t ×ˢ Set.Icc a b)
    (u : (unitInterval) × (unitInterval)) :
    squarePathHomotopy p q u ∈ Set.Icc s t ×ˢ Set.Icc a b :=
  ⟨convexComb_mem_Icc (hp u.2).1 (hq u.2).1 u.1, convexComb_mem_Icc (hp u.2).2 (hq u.2).2 u.1⟩

/-- The path from `(s, a)` to `(t, b)` in the square that goes vertically first and then
horizontally. -/
def FundamentalGroup.VanKampen.Cocone.rectangleHorizontalVertical (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b).trans
    ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)

/-- The path from `(s, a)` to `(t, b)` in the square that goes horizontally first and then
vertically. -/
def FundamentalGroup.VanKampen.Cocone.rectangleVerticalHorizontal (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t).trans
    ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)

/-- Pushing the first boundary path of a rectangle through `F` gives the corresponding
concatenation of restrictions of the edges of `F`. -/
theorem FundamentalGroup.VanKampen.Cocone.rectangleHorizontalVertical_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleHorizontalVertical s t a b).map F.continuous =
      ((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t) := by
  exact
    Path.map_trans
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b)
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)
      F.continuous

/-- Pushing the second boundary path of a rectangle through `F` gives the corresponding
concatenation of restrictions of the edges of `F`. -/
theorem FundamentalGroup.VanKampen.Cocone.rectangleVerticalHorizontal_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleVerticalHorizontal s t a b).map F.continuous =
      ((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b) := by
  exact
    Path.map_trans
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t)
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)
      F.continuous

/-- The first boundary path of a rectangle stays inside that rectangle. -/
theorem FundamentalGroup.VanKampen.Cocone.rectangleHorizontalVertical_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleHorizontalVertical s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply Path.trans_mem
  · intro u
    exact ⟨⟨le_rfl, hst⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, hab, le_rfl⟩

/-- The second boundary path of a rectangle stays inside that rectangle. -/
theorem FundamentalGroup.VanKampen.Cocone.rectangleVerticalHorizontal_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleVerticalHorizontal s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply Path.trans_mem
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, le_rfl, hab⟩
  · intro u
    exact ⟨⟨hst, le_rfl⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩

/-- The homotopy, inside the image of a rectangle under `F`, between the two ways of traversing
its boundary. -/
def FundamentalGroup.VanKampen.Cocone.rectangleBoundaryHomotopy {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    Path.Homotopy (((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t))
      (((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b)) :=
  ((squarePathHomotopy (rectangleHorizontalVertical s t a b)
            (rectangleVerticalHorizontal s t a b)).map
        F).cast
    (rectangleHorizontalVertical_map F s t a b) (rectangleVerticalHorizontal_map F s t a b)

/-- The boundary homotopy of a rectangle is `F` applied to the straight-line homotopy in the
square. -/
theorem FundamentalGroup.VanKampen.Cocone.rectangleBoundaryHomotopy_apply {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval))
    (u : (unitInterval) × (unitInterval)) :
    rectangleBoundaryHomotopy F s t a b u =
      F
        (squarePathHomotopy (rectangleHorizontalVertical s t a b)
          (rectangleVerticalHorizontal s t a b) u) :=
  rfl

/-- The boundary homotopy of a rectangle stays inside any set containing the image of the
rectangle under `F`. -/
theorem FundamentalGroup.VanKampen.Cocone.rectangleBoundaryHomotopy_mem {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) (hst : s ≤ t)
    (hab : a ≤ b) {A : Set X} (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ A)
    (u : (unitInterval) × (unitInterval)) : rectangleBoundaryHomotopy F s t a b u ∈ A := by
  rw [rectangleBoundaryHomotopy_apply]
  exact
    hcell _
      (squarePathHomotopy_mem_rectangle _ _ s t a b
        (rectangleHorizontalVertical_mem s t a b hst hab)
        (rectangleVerticalHorizontal_mem s t a b hst hab) u)

/-- For a rectangle whose image under `F` lies in one member of the cover, the two ways of
traversing its boundary have the same value: the commutation relation of a single cell. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.square_cell_of_local {X : Type*} [TopologicalSpace X]
    {ι G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hExt : V.Extends L)
    (hL : L.HomotopyInvariant) (i : ι) (F : C((unitInterval) × (unitInterval), X))
    (s t a b : (unitInterval)) (hst : s ≤ t) (hab : a ≤ b)
    (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ U i) :
    V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath a b) *
        V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F b).subpath s t) =
      V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F a).subpath s t) *
        V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath a b) := by
  let H := FundamentalGroup.VanKampen.Cocone.rectangleBoundaryHomotopy F s t a b
  have hH : ∀ u, H u ∈ U i :=
    FundamentalGroup.VanKampen.Cocone.rectangleBoundaryHomotopy_mem F s t a b hst hab hcell
  have hp :
    ∀ u,
      ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath a b).trans
          ((FundamentalGroup.VanKampen.Cocone.squareVertical F b).subpath s t) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_zero_left u)).mp (hH (0, u))
  have hq :
    ∀ u,
      ((FundamentalGroup.VanKampen.Cocone.squareVertical F a).subpath s t).trans
          ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath a b) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_one_left u)).mp (hH (1, u))
  calc
    _ =
        V.value
          (((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath a b).trans
            ((FundamentalGroup.VanKampen.Cocone.squareVertical F b).subpath s t)) :=
      (V.trans _ _).symm
    _ = L.value i _ hp := (hExt i _ hp)
    _ = L.value i _ hq := (hL i _ _ hp hq H hH)
    _ =
        V.value
          (((FundamentalGroup.VanKampen.Cocone.squareVertical F a).subpath s t).trans
            ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath a b)) :=
      (hExt i _ hq).symm
    _ = _ := V.trans _ _

/-- A constant path has trivial value. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.value_eq_one_of_constant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    {x y : X} (p : Path x y) (hp : ∀ t, p t = x) : V.value p = 1 := by
  have hy : y = x := p.target.symm.trans (hp 1)
  subst y
  have heq : p = Path.refl x := by
    ext t
    exact hp t
  rw [heq, V.refl]

/-- Chaining the cell relations along a subdivision of one side of the square gives the
commutation relation for the whole strip. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.square_strip {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    (F : C((unitInterval) × (unitInterval), X)) (s t : (unitInterval)) (d : ℕ → (unitInterval))
    (hmono : Monotone d) (n : ℕ)
    (hcell :
      ∀ k < n,
        V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath (d k) (d (k + 1))) *
            V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d (k + 1))).subpath s t) =
          V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d k)).subpath s t) *
            V.value
              ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath (d k) (d (k + 1)))) :
    V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath (d 0) (d n)) *
        V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d n)).subpath s t) =
      V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d 0)).subpath s t) *
        V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath (d 0) (d n)) := by
  induction n with
  | zero => simp only [Path.subpath_self, V.refl, one_mul, mul_one]
  | succ n ih =>
    have hprev := ih (fun k hk => hcell k (Nat.lt_succ_of_lt hk))
    rw [V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)),
      V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))]
    calc
      _ =
          V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value
                ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath (d n) (d (n + 1))) *
              V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d (n + 1))).subpath s t)) :=
        mul_assoc _ _ _
      _ =
          V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d n)).subpath s t) *
              V.value
                ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath (d n) (d (n + 1)))) := by
        rw [hcell n (Nat.lt_succ_self n)]
      _ =
          (V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F s).subpath (d 0) (d n)) *
              V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d n)).subpath s t)) *
            V.value
              ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath (d n) (d (n + 1))) :=
        (mul_assoc _ _ _).symm
      _ =
          (V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical F (d 0)).subpath s t) *
              V.value ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath (d 0) (d n))) *
            V.value
              ((FundamentalGroup.VanKampen.Cocone.squareHorizontal F t).subpath (d n) (d (n + 1))) := by
        rw [hprev]
      _ = _ := mul_assoc _ _ _

/-- The horizontal path of a homotopy at the parameter `s` has the value of the intermediate
path `H.eval s`. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.value_squareHorizontal_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s : (unitInterval)) :
    V.value (FundamentalGroup.VanKampen.Cocone.squareHorizontal H.toContinuousMap s) =
      V.value (H.eval s) := by
  have heq :
    FundamentalGroup.VanKampen.Cocone.squareHorizontal H.toContinuousMap s =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  rw [heq, V.value_cast]

/-- The vertical edge of a homotopy at `t = 0` is constant, hence has trivial value. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.value_squareVertical_homotopy_zero {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical H.toContinuousMap 0).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 0) = H (s, 0)
  simp only [Path.Homotopy.source]

/-- The vertical edge of a homotopy at `t = 1` is constant, hence has trivial value. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.value_squareVertical_homotopy_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroup.VanKampen.Cocone.squareVertical H.toContinuousMap 1).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 1) = H (s, 1)
  simp only [Path.Homotopy.target]

/-- A path value that extends a homotopy-invariant local path value over an open cover is itself
homotopy invariant: this is the subdivision-of-a-homotopy step of van Kampen's theorem. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.value_eq_of_homotopy_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
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

/-- A path value extending a homotopy-invariant local path value over an open cover is homotopy
invariant. -/
theorem FundamentalGroup.VanKampen.Cocone.PathValue.homotopyInvariant_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroup.VanKampen.Cocone.PathValue X G)
    (L : FundamentalGroup.VanKampen.Cocone.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (hExt : V.Extends L) (hL : L.HomotopyInvariant) :
    V.HomotopyInvariant := by
  intro x y p q h
  obtain ⟨H⟩ := h
  exact V.value_eq_of_homotopy_of_open_cover L hopen hcover hExt hL p q H

/-- The global path value attached to a compatible pair of homomorphisms out of `π₁(U)` and
`π₁(V)`. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.globalPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroup.VanKampen.Cocone.PathValue X G :=
  (D.localPathValue fU fV hf).extension D.chart_open D.chart_cover

/-- The global path value extends the local one. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.globalPathValue_extends {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).Extends (D.localPathValue fU fV hf) :=
  (D.localPathValue fU fV hf).extension_extends D.chart_open D.chart_cover

/-- The global path value attached to a compatible pair is homotopy invariant. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.globalPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).HomotopyInvariant :=
  FundamentalGroup.VanKampen.Cocone.PathValue.homotopyInvariant_of_open_cover (D.globalPathValue fU fV hf)
    (D.localPathValue fU fV hf) D.chart_open D.chart_cover (D.globalPathValue_extends fU fV hf)
    (D.localPathValue_homotopyInvariant fU fV hf)

/-- The homomorphism `π₁(X) → G` induced by a compatible pair of homomorphisms out of `π₁(U)`
and `π₁(V)`: the existence half of the van Kampen universal property. -/
def FundamentalGroup.VanKampen.Cocone.TwoOpenCover.lift {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroup X D.base →* G :=
  (globalPathValue D fU fV hf).fundamentalGroupHom
    (globalPathValue_homotopyInvariant D fU fV hf) D.base

/-- On the class of a loop contained in one chart, the lift is the inverse of the local value. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.lift_mk_of_mem {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i : Bool) (p : Path D.base D.base)
    (hp : ∀ t, p t ∈ D.chart i) :
    D.lift fU fV hf (Path.Homotopic.Quotient.mk p) = (D.localValue fU fV i p hp)⁻¹ :=
  congrArg (fun a : G => a⁻¹) (D.globalPathValue_extends fU fV hf i p hp)

/-- The lift restricts to `fU` along `π₁(U) → π₁(X)`. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.lift_comp_inclusionU {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomU = fU := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.false (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

/-- The lift restricts to `fV` along `π₁(V) → π₁(X)`. -/
theorem FundamentalGroup.VanKampen.Cocone.TwoOpenCover.lift_comp_inclusionV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroup.VanKampen.Cocone.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomV = fV := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.true (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h
