/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareRotation

/-!
# The homotopy class of a based cube and its reparametrisations

`Hurewicz.NativeSubdivision.nativeClass p` is the class `Additive.ofMul ⟦p⟧` of a based
cube `p : GenLoop N X x` in the additively written homotopy group `Additive (π_N X x)`.
It is additive under concatenation `GenLoop.transAt`, changes sign under reversal
`GenLoop.symmAt`, and is invariant under homotopy rel boundary.

Two reparametrisations are studied:

* the *quarter turn* in a coordinate pair `(i, j)`, which is homotopic to the identity
  (`nativeClass_quarterTurn`), and
* the *coordinate permutation* `permuteCubeLoop p e = p ∘ (u ↦ u ∘ e)`, whose class is
  `sign e • nativeClass p` (`permuteCubeLoop_additiveClass`): a transposition is a
  quarter turn followed by a reversal.

For an *internally based* cube (`NativeCubeInternalBased p`: `p u = x` whenever two
coordinates of `u` coincide), pullbacks along two cube self-maps that agree on a common
*flat* of the boundary (`NativeCubeSameFlat`) are homotopic rel boundary through the
coordinatewise convex blend (`nativeCubeLinearHomotopy`). This is the tool by which the
subdivision argument replaces one chart of a chamber by another.

The sign of a permuted cube is the classical statement that `π_n` is acted on by `S_n`
through the sign character (cf. Hatcher, *Algebraic Topology*, §4.1); it enters this
development's proof of the Hurewicz theorem (statement: Hatcher, Theorem 4.32; the argument is
recorded in `Lib/docs/C.md`).

## Main definitions

* `Hurewicz.NativeSubdivision.nativeClass`
* `Hurewicz.NativeSubdivision.NativeCubeInternalBased`, `Hurewicz.NativeSubdivision.NativeCubeSameFlat`
* `Hurewicz.NativeSubdivision.nativeCubePullbackLoop`, `Hurewicz.NativeSubdivision.nativeCubeLinearHomotopy`
* `Hurewicz.NativeSubdivision.permuteCubeLoop`

## Main results

* `Hurewicz.NativeSubdivision.nativeClass_transAt`, `Hurewicz.NativeSubdivision.nativeClass_symmAt`
* `Hurewicz.NativeSubdivision.permuteCubeLoop_additiveClass`
-/

open Set Function Topology

noncomputable section

/-! ### The native class and cube reparametrization -/

/-- The coordinate pair `(u i, u j)` extracted from a cube point. -/
def Hurewicz.NativeSubdivision.nativeCubePair {N : Type*} (i j : N) :
    C(N → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

/-- The homotopy map rotating the `(i, j)` coordinate pair through a quarter turn
while preserving boundary values. -/
def Hurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap {N : Type*} [DecidableEq N]
    (i j : N) : C((unitInterval) × (N → (unitInterval)), N → (unitInterval))
    where
  toFun z
    k :=
    if k = i then
      Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 0
    else
      if k = j then
        Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 1
      else z.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases hi : k = i
    · simp only [if_pos hi]
      exact
        (continuous_apply (0 : Fin 2)).comp
          (Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
            (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
    · by_cases hj : k = j
      · simp only [if_neg hi, if_pos hj]
        exact
          (continuous_apply (1 : Fin 2)).comp
            (Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
              (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
      · simp only [if_neg hi, if_neg hj]
        exact (continuous_apply k).comp continuous_snd

/-- At time `0` the quarter-turn map is the identity. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_zero {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change
    (if k = i then
        Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
      else
        if k = j then
          Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 1
        else u k) =
      u k
  simp only [Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

/-- At time `1` the quarter-turn map is the quarter rotation of the `(i,j)` pair. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_one {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) = fun k =>
      if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

/-- The quarter-turn map preserves the cube boundary at all times. -/
theorem Hurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_boundary {N : Type*}
    [DecidableEq N] (i j : N) (hij : i ≠ j) (t : (unitInterval)) (u : N → (unitInterval))
    (hu : u ∈ Cube.boundary N) : nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ :=
      Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_boundary t (nativeCubePair i j u) h
    fin_cases k
    · exact ⟨i, by simpa [nativeCubeQuarterTurnHomotopyMap] using hk⟩
    · exact ⟨j, by simpa [nativeCubeQuarterTurnHomotopyMap, hij.symm] using hk⟩
  obtain ⟨k, hk⟩ := hu
  by_cases hi : k = i
  · subst k
    exact hp ⟨0, by simpa [nativeCubePair] using hk⟩
  · by_cases hj : k = j
    · subst k
      exact hp ⟨1, by simpa [nativeCubePair] using hk⟩
    · exact ⟨k, by simpa [nativeCubeQuarterTurnHomotopyMap, hi, hj] using hk⟩

/-- The based cube obtained by applying the quarter-turn endpoint to `p`:
`u ↦ p (quarterTurn (1, u))`. -/
def Hurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    GenLoop N X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp
        ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
          (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

/-- `nativeCubeQuarterTurnLoop` applied at `u` is `p` of the quarter-turned point. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_apply {N : Type*}
    [DecidableEq N] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

/-- The homotopy from `p` to its quarter-turned form. -/
def Hurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopy {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary N)
    where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u
    hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

/-- A native `N`-indexed cube: the function space `N → unitInterval`. -/
abbrev Hurewicz.NativeSubdivision.NativeCube (N : Type*) :=
  N → (unitInterval)

/-- The additive π-class `Additive.ofMul ⟦p⟧` of a based `N`-cube. -/
def Hurewicz.NativeSubdivision.nativeClass {N X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop N X x) : Additive (HomotopyGroup N X x) :=
  Additive.ofMul (⟦p⟧ : HomotopyGroup N X x)

/-- `nativeClass` is homotopy invariant: homotopic based cubes have the same class. -/
theorem Hurewicz.NativeSubdivision.nativeClass_homotopic {N X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) : nativeClass p = nativeClass q :=
  congrArg (fun a : HomotopyGroup N X x => Additive.ofMul a) (Quotient.sound h)

/-- `nativeClass` is additive under `transAt` concatenation at coordinate `i`. -/
theorem Hurewicz.NativeSubdivision.nativeClass_transAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nontrivial N] (i : N) (p q : GenLoop N X x) :
    nativeClass (GenLoop.transAt i p q) = nativeClass p + nativeClass q :=
  congrArg Additive.ofMul
    ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans (mul_comm _ _))

/-- `nativeClass` is antisymmetric under `symmAt` reversal at coordinate `i`. -/
theorem Hurewicz.NativeSubdivision.nativeClass_symmAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] (i : N) (p : GenLoop N X x) :
    nativeClass (GenLoop.symmAt i p) = -nativeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

/-- The native class of the constant cube is `0`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeClass_const {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] : nativeClass (GenLoop.const : GenLoop N X x) = 0 :=
  rfl

/-- A based `N`-cube is internally based: `p u = x` whenever two distinct
coordinates of `u` coincide. -/
def Hurewicz.NativeSubdivision.NativeCubeInternalBased {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) : Prop :=
  ∀ u : NativeCube N, ∀ i j : N, i ≠ j → u i = u j → p u = x

/-- Two cube points lie on the same flat (boundary or diagonal stratum): they share
a zero coordinate, a one coordinate, or an equal pair of coordinates. -/
inductive Hurewicz.NativeSubdivision.NativeCubeSameFlat {N : Type*} (a b : NativeCube N) :
    Prop
  | zero (i : N) (ha : a i = 0) (hb : b i = 0)
  | one (i : N) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : N) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

/-- The convex blend `t ↦ (1-t)·a + t·b` of two cube points, coordinatewise. -/
def Hurewicz.NativeSubdivision.nativeCubeBlend {N : Type*} (t : (unitInterval))
    (a b : NativeCube N) : NativeCube N := fun i => Set.Icc.convexComb (a i) (b i) t

/-- At `t = 0` the blend is `a`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeCubeBlend_zero {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

/-- At `t = 1` the blend is `b`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeCubeBlend_one {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

/-- The blend of two cube self-maps `f, g` along a parameter cube. -/
def Hurewicz.NativeSubdivision.nativeCubeBlendMap {N : Type*}
    (f g : C(NativeCube N, NativeCube N)) : C((unitInterval) × NativeCube N, NativeCube N)
    where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

/-- If `f u` and `g u` lie on the same flat and `p` is internally based, the blend
`p (blend t (f u) (g u))` is based at `x`. -/
theorem Hurewicz.NativeSubdivision.nativeCubeBlend_based {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p) {a b : NativeCube N}
    (h : NativeCubeSameFlat a b) (t : (unitInterval)) : p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb => exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb => exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb => exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

/-- The pullback of a based cube `p` along a boundary-preserving cube self-map `f`. -/
def Hurewicz.NativeSubdivision.nativeCubePullbackLoop {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (f : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x) : GenLoop N X x :=
  ⟨p.val.comp f, hf⟩

/-- The linear homotopy between two pullbacks of `p` along `f` and `g`, valid when
the images lie on a common flat. -/
def Hurewicz.NativeSubdivision.nativeCubeLinearHomotopy {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube N, NativeCube N)) (hf : ∀ u ∈ Cube.boundary N, p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary N, p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary N, NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel (nativeCubePullbackLoop p g hg).val
      (Cube.boundary N)
    where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left
    u := by
    change p (nativeCubeBlend 0 (f u) (g u)) = p (f u)
    rw [nativeCubeBlend_zero]
  map_one_left
    u := by
    change p (nativeCubeBlend 1 (f u) (g u)) = p (g u)
    rw [nativeCubeBlend_one]
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

/-- The coordinate permutation of a cube by `e`: `u ↦ u ∘ e`. -/
def Hurewicz.NativeSubdivision.permuteCubeCoordinates {N : Type*} (e : Equiv.Perm N) :
    C(N → (unitInterval), N → (unitInterval))
    where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

/-- The coordinate permutation preserves the cube boundary. -/
theorem Hurewicz.NativeSubdivision.permuteCubeCoordinates_boundary {N : Type*}
    (e : Equiv.Perm N) (u : N → (unitInterval)) (hu : u ∈ Cube.boundary N) :
    permuteCubeCoordinates e u ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

/-- The pullback of a based cube along a coordinate permutation. -/
def Hurewicz.NativeSubdivision.permuteCubeLoop {N : Type*} {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) : GenLoop N X x :=
  ⟨p.val.comp (permuteCubeCoordinates e), fun u hu =>
    p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

/-- `permuteCubeLoop p e u = p (u ∘ e)`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.permuteCubeLoop_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) (u : N → (unitInterval)) :
    permuteCubeLoop p e u = p (fun i => u (e i)) :=
  rfl

/-- Permuting by the identity leaves the loop unchanged. -/
@[simp]
theorem Hurewicz.NativeSubdivision.permuteCubeLoop_one {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

/-- Permuting by a composite `e * f` permutes by `f` then `e`. -/
theorem Hurewicz.NativeSubdivision.permuteCubeLoop_mul {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e f : Equiv.Perm N) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

/-- The quarter-turn loop equals the `symmAt`-reversed, permuted loop. -/
theorem Hurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_eq_symmAt_permute {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) :
    nativeCubeQuarterTurnLoop p i j hij = GenLoop.symmAt i (permuteCubeLoop p (Equiv.swap i j)) :=
  by
  apply GenLoop.ext
  intro u
  rw [nativeCubeQuarterTurnLoop_apply]
  change
    p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) =
      p
        (fun k =>
          if Equiv.swap i j k = i then (unitInterval.symm) (u i) else u (Equiv.swap i j k))
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

/-- The native class of the quarter-turned cube equals the class of `p`. -/
theorem Hurewicz.NativeSubdivision.nativeClass_quarterTurn {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    nativeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeClass p :=
  (nativeClass_homotopic ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩).symm

/-- Permuting by a transposition negates the native class. -/
theorem Hurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) : nativeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeClass p :=
  by
  have h := nativeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

/-- The native class of a permuted cube is the permutation sign times the original
class. -/
theorem Hurewicz.NativeSubdivision.permuteCubeLoop_additiveClass {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] [Fintype N] (p : GenLoop N X x)
    (e : Equiv.Perm N) :
    nativeClass (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
