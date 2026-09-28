/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Subdivision.CubeClass

/-!
# Slicing a based cube along coordinate cuts

Given a based cube `p : GenLoop N X x` and two *cut functions* `a b : C(N → I, I)` in the
coordinate `i` (both *based*, `CutBased p i a`: setting `u i := a u` lands `p` at `x`),
the *slice* `Hurewicz.NativeSubdivision.sliceLoop p i a b` is `p` restricted to the region
between the graphs of `a` and `b`, reparametrised to the full cube by the convex
combination `u i ↦ (1 - u i) • a u + u i • b u`.

Slicing is compatible with concatenation: for cuts independent of the coordinate `i`
(`CutIndependent`), the slice from `a` to `c` is homotopic to the concatenation
`GenLoop.transAt i` of the slices from `a` to `b` and from `b` to `c`
(`slice_homotopic_trans`), through the binary warp `cutBinaryWarp`. Iterating,
`finiteCuts_class` writes the class of `p` as the sum of the classes of the slices
between consecutive members of a finite family of cuts running from `0` to `1`.

This is the "cutting a cube into slabs" step of the subdivision argument in the proof of
the Hurewicz theorem (Hatcher, *Algebraic Topology*, Theorem 4.32).

## Main definitions

* `Hurewicz.NativeSubdivision.CutIndependent`, `Hurewicz.NativeSubdivision.CutBased`
* `Hurewicz.NativeSubdivision.sliceMap`, `Hurewicz.NativeSubdivision.sliceLoop`
* `Hurewicz.NativeSubdivision.cutBinaryWarp`, `Hurewicz.NativeSubdivision.sliceConcat`

## Main results

* `Hurewicz.NativeSubdivision.slice_homotopic_trans`
* `Hurewicz.NativeSubdivision.sliceConcat_class`, `Hurewicz.NativeSubdivision.finiteCuts_class`
-/

open Set Function Topology

noncomputable section

/-! ### Coordinate cuts and slicing -/

/-- A cut function `a` is independent of coordinate `i`: updating `u i` does not
change `a u`. -/
def Hurewicz.NativeSubdivision.CutIndependent {N : Type*} [DecidableEq N] (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u v, a (Function.update u i v) = a u

/-- A cut `a` at coordinate `i` is based for `p`: setting `u i := a u` lands `p`
at `x`. -/
def Hurewicz.NativeSubdivision.CutBased {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

/-- The slice map at coordinate `i` between cuts `a` and `b`: updates `u i` to the
convex combination of `a u` and `b u` at position `u i`. -/
def Hurewicz.NativeSubdivision.sliceMap {N : Type*} [DecidableEq N] (i : N)
    (a b : C(NativeCube N, (unitInterval))) : C(NativeCube N, NativeCube N)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

/-- For cuts based for `p`, the slice map composed with `p` is based at `x`. -/
theorem Hurewicz.NativeSubdivision.sliceMap_based {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) (hu : u ∈ Cube.boundary N) : p (sliceMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [sliceMap, hj] using ha u
    · simpa [sliceMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [sliceMap, hji] using hj⟩

/-- The based cube obtained by slicing `p` at coordinate `i` between the cuts
`a` and `b`. -/
def Hurewicz.NativeSubdivision.sliceLoop {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b) :
    GenLoop N X x :=
  ⟨p.val.comp (sliceMap i a b), sliceMap_based p i a b ha hb⟩

/-- `sliceLoop p i a b` applied at `u` is `p` of the sliced point. -/
@[simp]
theorem Hurewicz.NativeSubdivision.sliceLoop_apply {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) :
    sliceLoop p i a b ha hb u = p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) :=
  rfl

/-- Slicing `p` between the same cut `a` twice yields the constant loop
`GenLoop.const`. -/
theorem Hurewicz.NativeSubdivision.sliceLoop_self {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (a : C(NativeCube N, (unitInterval)))
    (ha : CutBased p i a) : sliceLoop p i a a ha ha = GenLoop.const := by
  apply GenLoop.ext
  intro u
  simpa only [sliceLoop_apply, Set.Icc.convexComb_eq, GenLoop.const_apply] using ha u

/-- Slicing between the constant cuts `0` and `1` recovers `p`. -/
theorem Hurewicz.NativeSubdivision.sliceLoop_full {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (ha0 : ∀ u, a u = 0) (hb1 : ∀ u, b u = 1) : sliceLoop p i a b ha hb = p := by
  apply GenLoop.ext
  intro u
  simp [ha0 u, hb1 u]

/-- If `q` is `p` with coordinate `i` set by `w`, and `w` agrees with `a`/`b` on the
`u i = 0`/`1` faces, then `sliceLoop p i a b` is homotopic rel boundary to `q`. -/
def Hurewicz.NativeSubdivision.sliceHomotopyOfCoordinate {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (q : GenLoop N X x) (w : C(NativeCube N, (unitInterval)))
    (hq : ∀ u, q u = p (Function.update u i (w u))) (hw0 : ∀ u, u i = 0 → w u = a u)
    (hw1 : ∀ u, u i = 1 → w u = b u) :
    (sliceLoop p i a b ha hb).val.HomotopyRel q.val (Cube.boundary N)
    where
  toFun
    v :=
    p
      (Function.update v.2 i
        (Set.Icc.convexComb (Set.Icc.convexComb (a v.2) (b v.2) (v.2 i)) (w v.2) v.1))
  continuous_toFun :=
    p.val.continuous.comp
      (continuous_snd.update i
        (Set.Icc.continuous_convexComb_prod.comp
          ((Set.Icc.continuous_convexComb_prod.comp
                ((a.continuous.comp continuous_snd).prodMk
                  ((b.continuous.comp continuous_snd).prodMk
                    ((continuous_apply i).comp continuous_snd)))).prodMk
            ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 0)) =
        _
    rw [Set.Icc.convexComb_zero]
    rfl
  map_one_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 1)) =
        q u
    rw [Set.Icc.convexComb_one]
    exact (hq u).symm
  prop' t u
    hu := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) t)) =
        sliceLoop p i a b ha hb u
    have hs : sliceLoop p i a b ha hb u = x := (sliceLoop p i a b ha hb).property u hu
    rw [hs]
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · simpa [hj, hw0 u hj] using ha u
      · simpa [hj, hw1 u hj] using hb u
    · exact p.property _ ⟨j, by simpa [hji] using hj⟩

/-- The ternary warp `((a,b,c), t) ↦` convex combination: for `t ≤ 1/2` blends `a`
to `b`, for `t ≥ 1/2` blends the result toward `c`. -/
def Hurewicz.NativeSubdivision.cutBinaryWarp :
    C(((unitInterval) × (unitInterval) × (unitInterval)) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb
      (Set.Icc.convexComb p.1.1 p.1.2.1 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))) p.1.2.2
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

/-- `cutBinaryWarp ((a,b,c), t)` is the nested convex combination. -/
theorem Hurewicz.NativeSubdivision.cutBinaryWarp_apply (a b c t : (unitInterval)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb (Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)))) c
        (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  rfl

/-- At `t = 0` the binary warp returns `a`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.cutBinaryWarp_zero (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 0) = a := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

/-- At `t = 1` the binary warp returns `c`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.cutBinaryWarp_one (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 1) = c := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

/-- For `t ≤ 1/2`, the binary warp is the convex combination of `a` and `b`. -/
theorem Hurewicz.NativeSubdivision.cutBinaryWarp_of_le_half (a b c t : (unitInterval))
    (ht : (t : ℝ) ≤ 1 / 2) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) := by
  have hz : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, hz, Set.Icc.convexComb_zero]

/-- For `1/2 ≤ t`, the binary warp is the convex combination toward `c`. -/
theorem Hurewicz.NativeSubdivision.cutBinaryWarp_of_half_le (a b c t : (unitInterval))
    (ht : 1 / 2 ≤ (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) := by
  have ho : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, ho, Set.Icc.convexComb_one]

/-- For `t > 1/2`, the binary warp is the convex combination toward `c`. -/
theorem Hurewicz.NativeSubdivision.cutBinaryWarp_of_half_lt (a b c t : (unitInterval))
    (ht : 1 / 2 < (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  cutBinaryWarp_of_half_le a b c t ht.le

/-- The sliced coordinate at `i` through three cuts `a`, `b`, `c`:
`u ↦ cutBinaryWarp ((a u, b u, c u), u i)`. -/
def Hurewicz.NativeSubdivision.sliceBinaryCoordinate {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) : C(NativeCube N, (unitInterval))
    where
  toFun u := cutBinaryWarp ((a u, b u, c u), u i)
  continuous_toFun :=
    cutBinaryWarp.continuous.comp
      ((a.continuous.prodMk (b.continuous.prodMk c.continuous)).prodMk (continuous_apply i))

/-- On the face `u i = 0`, the binary sliced coordinate is `a u`. -/
theorem Hurewicz.NativeSubdivision.sliceBinaryCoordinate_zero {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 0) :
    sliceBinaryCoordinate i a b c u = a u := by simp [sliceBinaryCoordinate, hu]

/-- On the face `u i = 1`, the binary sliced coordinate is `c u`. -/
theorem Hurewicz.NativeSubdivision.sliceBinaryCoordinate_one {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 1) :
    sliceBinaryCoordinate i a b c u = c u := by simp [sliceBinaryCoordinate, hu]

/-- The transitivity slice of `p` through coordinate `i` evaluated at `u`. -/
theorem Hurewicz.NativeSubdivision.sliceTrans_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) (u : NativeCube N) :
    GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc) u =
      p (Function.update u i (sliceBinaryCoordinate i a b c u)) := by
  change
    (if (u i : ℝ) ≤ 1 / 2 then
        sliceLoop p i a b ha hb
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        sliceLoop p i b c hb hc
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))) =
      p (Function.update u i (cutBinaryWarp ((a u, b u, c u), u i)))
  split_ifs with h
  · rw [sliceLoop_apply, haInd u _, hbInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_le_half (a u) (b u) (c u) (u i) h).symm
  · rw [sliceLoop_apply, hbInd u _, hcInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_half_lt (a u) (b u) (c u) (u i) (lt_of_not_ge h)).symm

/-- Slicing twice through the same coordinate is homotopic to the direct slice. -/
theorem Hurewicz.NativeSubdivision.slice_homotopic_trans {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) :
    GenLoop.Homotopic (sliceLoop p i a c ha hc)
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc)) :=
  ⟨sliceHomotopyOfCoordinate p i a c ha hc
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc))
      (sliceBinaryCoordinate i a b c) (sliceTrans_apply p i a b c ha hb hc haInd hbInd hcInd)
      (sliceBinaryCoordinate_zero i a b c) (sliceBinaryCoordinate_one i a b c)⟩

/-- The slice loop of a concatenation decomposes as the `transAt` of the slices. -/
theorem Hurewicz.NativeSubdivision.slice_toLoop_transAt {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) (a b : GenLoop N X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- Slicing a `transAt` concatenation is homotopic to the concatenation of the
slices. -/
theorem Hurewicz.NativeSubdivision.slice_transAt_homotopic {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) {a b c d : GenLoop N X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [slice_toLoop_transAt, slice_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

/-- The iterated slice of `p` at coordinate `i` through `k+1` successive cuts,
as a `transAt`-concatenation of slice loops. -/
def Hurewicz.NativeSubdivision.sliceConcat {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) :
    (k : ℕ) →
      (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) →
        (∀ j, CutBased p i (a j)) → GenLoop N X x
  | 0, _, _ => GenLoop.const
  | k + 1, a, ha =>
    GenLoop.transAt i
      (sliceLoop p i (a 0) (a (0 : Fin (k + 1)).succ) (ha 0) (ha (0 : Fin (k + 1)).succ))
      (sliceConcat p i k (fun j => a j.succ) (fun j => ha j.succ))

/-- The iterated slice is homotopic to the single slice from the first to the last
cut. -/
theorem Hurewicz.NativeSubdivision.slice_homotopic_concat {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) :
    GenLoop.Homotopic (sliceLoop p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)))
      (sliceConcat p i k a ha) := by
  induction k with
  | zero =>
    change GenLoop.Homotopic (sliceLoop p i (a 0) (a 0) (ha 0) (ha 0)) GenLoop.const
    rw [sliceLoop_self]
  | succ k
    ih =>
    have ht := ih (fun j => a j.succ) (fun j => ha j.succ) (fun j => hInd j.succ)
    have hs :=
      slice_homotopic_trans p i (a 0) (a (0 : Fin (k + 1)).succ) (a (Fin.last (k + 1))) (ha 0)
        (ha (0 : Fin (k + 1)).succ) (ha (Fin.last (k + 1))) (hInd 0) (hInd (0 : Fin (k + 1)).succ)
        (hInd (Fin.last (k + 1)))
    apply hs.trans
    apply slice_transAt_homotopic
    · exact GenLoop.Homotopic.refl _
    · exact ht

/-- The native class of the iterated slice equals the class of `p` sliced once. -/
theorem Hurewicz.NativeSubdivision.sliceConcat_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j)) :
    nativeClass (sliceConcat p i k a ha) =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) := by
  induction k with
  | zero => simp [sliceConcat]
  | succ k ih =>
    rw [sliceConcat, nativeClass_transAt, ih, Fin.sum_univ_succ]
    rfl

/-- A finite family of cuts is homotopic to slicing through them successively. -/
theorem Hurewicz.NativeSubdivision.finiteCuts_homotopic {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) : GenLoop.Homotopic p (sliceConcat p i k a ha) := by
  have h := slice_homotopic_concat p i k a ha hInd
  rwa [sliceLoop_full p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)) hzero hone] at h

/-- The native class of the finite-cut slicing equals the class of `p`. -/
theorem Hurewicz.NativeSubdivision.finiteCuts_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) :
    nativeClass p =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) :=
  (nativeClass_homotopic (finiteCuts_homotopic p i k a ha hInd hzero hone)).trans
    (sliceConcat_class p i k a ha)
