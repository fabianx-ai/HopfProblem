/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Subdivision.SimplexQuotient
import Lib.AlgebraicTopology.Hurewicz.Subdivision.ExtendedChamber
import Lib.AlgebraicTopology.Hurewicz.Subdivision.DuffyMap

/-!
# The subdivision identity for based cubes

The class of an internally based `n`-cube `p : GenLoop (Fin n) X x` (`n ≥ 2`) in the
additively written homotopy group is the signed sum, over the permutations `e`, of the
classes of the based simplices cut out by the Kuhn cells:

`Additive.ofMul ⟦p⟧ = ∑ e : Perm (Fin n), cubeOrientation e • basedSimplexClass (nativeBasedCubeSimplex p hp e)`

(`Hurewicz.NativeSubdivision.nativeCubeSubdivision_class`). Here
`nativeBasedCubeSimplex p hp e` is the restriction of `p` to the `e`-th Kuhn cell
`Hurewicz.CubeTriangulation.cubeSimplex e`, which is a based simplex because `p` is
internally based, and `basedSimplexClass` is its class via the simplex quotient of the
cube.

The proof assembles the pieces of the subdivision: by induction on `m ≤ n` the class of `p`
is the sum over the chambers of the `m`-cube of the extended Duffy chamber loops
(`nativeClass_eq_sum_partialChambers`, using the insertion sum), and for `m = n` each
chamber loop is homotopic to the based simplex loop of its cell
(`nativeDuffyCube_homotopic_basedSimplexLoop`: the Duffy cube and the cell quotient
`nativeCubeSimplexQuotient e` share a flat on the boundary), with the sign of the
permutation as orientation (`nativeClass_chamber_eq_orientedSimplex`).

This is the step "a spheroid is the signed sum of the simplices of a triangulation of the
cube" in the proof of the Hurewicz theorem (Hatcher, *Algebraic Topology*, Theorem 4.32).

## Main definitions

* `Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient`, `Hurewicz.NativeSubdivision.nativeBasedCubeSimplex`

## Main results

* `Hurewicz.NativeSubdivision.nativeClass_eq_sum_partialChambers`
* `Hurewicz.NativeSubdivision.nativeDuffyCubeClass_eq_basedSimplexClass`
* `Hurewicz.NativeSubdivision.nativeClass_eq_sum_simplices`,
  `Hurewicz.NativeSubdivision.nativeCubeSubdivision_class`
-/

open Set Function Topology

noncomputable section

/-! ### Kuhn cells as based simplices -/

/-- The composite `cubeSimplex e ∘ simplexQuotient n` as a cube self-map: the `e`-th
Kuhn cell read in quotient coordinates. -/
def Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (Hurewicz.CubeTriangulation.cubeSimplex e).comp
    (Hurewicz.SimplexGeometry.simplexQuotient n)

/-- For an internally based `p`, the `e`-th cell restriction `p ∘ cubeSimplex e` is
a based simplex. -/
theorem Hurewicz.NativeSubdivision.nativeCubeSimplex_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n)
    (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) :
    p (Hurewicz.CubeTriangulation.cubeSimplex e s) = x := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := hs
    have hi0 : i = 0 := Fin.ext (by omega)
    subst i
    have hsum : s 0 = 1 := by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using stdSimplex.sum_eq_one s
    exact False.elim (by linarith)
  | succ
    n =>
    rcases Hurewicz.CubeTriangulation.cubeSimplex_simplexBoundary e s hs with h |
      ⟨i, j, hij, h⟩
    · exact p.property _ h
    · exact hp _ i j hij h

/-- The `e`-th Kuhn cell of an internally based cube `p` as a based simplex. -/
def Hurewicz.NativeSubdivision.nativeBasedCubeSimplex {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) : Hurewicz.SimplexGeometry.BasedSimplex n x :=
  ⟨p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e), nativeCubeSimplex_based p hp e⟩

/-- For internally based `p`, `p (nativeCubeSimplexQuotient e u) = x` for `u` on the cube boundary. -/
theorem Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeCubeSimplexQuotient e u) = x :=
  nativeCubeSimplex_based p hp e _ (Hurewicz.SimplexGeometry.simplexQuotient_boundary u hu)

/-! ### The chamber sum and the subdivision identity -/

/-- The native class of `p` equals the sum over chamber charts of the extended
chamber classes. -/
theorem Hurewicz.NativeSubdivision.nativeClass_eq_sum_partialChambers {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (m : ℕ) (h : m ≤ n) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin m), nativeClass (extendedChamberLoop p hp h (orderedDuffyChart e)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_insertPermutation]
    calc
      nativeClass p =
          ∑ e : Equiv.Perm (Fin m),
            nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) (orderedDuffyChart e)) :=
        ih (Nat.le_of_succ_le h)
      _ =
          ∑ e : Equiv.Perm (Fin m),
            ∑ r : Fin (m + 1),
              nativeClass
                (extendedChamberLoop p hp h (orderedDuffyChart (insertPermutation e r))) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [nativeClass_extendedChamber_eq_sum_insertions p hp h (orderedDuffyChart e)]
        apply Finset.sum_congr rfl
        intro r _
        exact
          nativeClass_extendedChamber_eq p hp h (insertChamberChart e r (orderedDuffyChart e))
            (orderedDuffyChart (insertPermutation e r))

/-- The coordinates of the cell quotient map `nativeCubeSimplexQuotient e`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeCubeSimplexQuotient e u (e i) =
      Hurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) :=
  Subtype.ext (Hurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate e u i)

/-- A cell-quotient coordinate vanishes when the corresponding ordered coordinate
is `0`. -/
theorem Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeCubeSimplexQuotient e u (e j) = 0 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  exact
    le_antisymm (hi ▸ Hurewicz.SimplexGeometry.prefixMinimum_le_coordinate u _ i (by omega))
      bot_le

/-- The `(e 0)`-th cell-quotient coordinate equals `1` when the first ordered
coordinate `u 0` is `1`. -/
theorem Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeCubeSimplexQuotient e u (e 0) = 1 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  change Hurewicz.SimplexGeometry.prefixMinimum u (0 + 1) = 1
  rw [Hurewicz.SimplexGeometry.prefixMinimum_succ u 0 (Nat.zero_lt_succ n),
    Hurewicz.SimplexGeometry.prefixMinimum_zero]
  simp [hu]

/-- Adjacent cell-quotient coordinates coincide when the intervening coordinate is
`1`. -/
theorem Hurewicz.NativeSubdivision.nativeCubeSimplexQuotient_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) :
    nativeCubeSimplexQuotient e u (e i.castSucc) = nativeCubeSimplexQuotient e u (e i.succ) := by
  rw [nativeCubeSimplexQuotient_coordinate, nativeCubeSimplexQuotient_coordinate,
    Hurewicz.SimplexGeometry.prefixMinimum_succ u i.succ.val i.succ.isLt]
  change
    Hurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) =
      Min.min (Hurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)) (u i.succ)
  rw [hi,
    min_eq_left
      (show Hurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) ≤ 1 from
        (Hurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)).property.2)]

/-- The Duffy cube and the cell quotient map land on the same flat. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_simplex_sameFlat {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeSimplexQuotient e u) := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact
      .zero (e i) (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)
        (nativeCubeSimplexQuotient_coordinate_eq_zero e u i i le_rfl hi)
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero =>
        exact
          .one (e 0) (nativeDuffyCube_coordinate_zero_of_one e u hi)
            (nativeCubeSimplexQuotient_coordinate_zero_of_one e u hi)
      | succ i =>
        exact
          .equal (e i.castSucc) (e i.succ)
            (e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this))
            (nativeDuffyCube_adjacent_of_one e u i hi)
            (nativeCubeSimplexQuotient_adjacent_of_one e u i hi)

/-- The homotopy between the Duffy-cube pullback of `p` and the cell simplex
pullback. -/
def Hurewicz.NativeSubdivision.nativeDuffyCubeSimplexHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (Hurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeSimplexQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeSimplexQuotient_based p hp e)
    (nativeDuffyCube_simplex_sameFlat e)

/-- The Duffy-cube loop of `p` is homotopic to the cell's based simplex loop. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_homotopic_basedSimplexLoop {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (Hurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)) :=
  ⟨nativeDuffyCubeSimplexHomotopy p hp e⟩

/-- The native class of the Duffy-cube loop equals the cell's based simplex class. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCubeClass_eq_basedSimplexClass {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    nativeClass (nativeDuffyCubeLoop p hp e) =
      Hurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_homotopic (nativeDuffyCube_homotopic_basedSimplexLoop p hp e)

/-- The native class of a boundary-flat-common pullback equals the oriented cell
class. -/
theorem Hurewicz.NativeSubdivision.nativeClass_commonOrderedSimplex {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      Hurewicz.CubeTriangulation.cubeOrientation e •
        Hurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  rw [nativeClass_commonOrderedDuffy p hp e f hf hfg, nativeDuffyCubeClass_eq_basedSimplexClass]
  rfl

/-- The native class of a chamber loop equals `cubeOrientation e • basedSimplexClass`
of the `e`-th cell. -/
theorem Hurewicz.NativeSubdivision.nativeClass_chamber_eq_orientedSimplex {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (le_refl n) chart) =
      Hurewicz.CubeTriangulation.cubeOrientation e •
        Hurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  apply
    nativeClass_commonOrderedSimplex p hp e (extendCubeMap (le_refl n) chart.toContinuousMap)
      (extendedChamberMap_based p hp (le_refl n) chart)
  intro u hu
  rw [extendCubeMap_refl]
  exact chart.commonOrderedDuffy u hu

/-- The native class of an internally based cube equals the signed sum over the Kuhn
cells of their based simplex classes. -/
theorem Hurewicz.NativeSubdivision.nativeClass_eq_sum_simplices {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin n),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          Hurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  calc
    nativeClass p =
        ∑ e : Equiv.Perm (Fin n),
          nativeClass (extendedChamberLoop p hp (le_refl n) (orderedDuffyChart e)) :=
      nativeClass_eq_sum_partialChambers p hp n (le_refl n)
    _ = _ :=
      Finset.sum_congr rfl fun e _ =>
        nativeClass_chamber_eq_orientedSimplex p hp e (orderedDuffyChart e)

/-- The subdivision identity: `Additive.ofMul ⟦p⟧` equals the signed sum
`∑ e, cubeOrientation e • basedSimplexClass (nativeBasedCubeSimplex p hp e)`. -/
theorem Hurewicz.NativeSubdivision.nativeCubeSubdivision_class {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ n X x) =
      ∑ e : Equiv.Perm (Fin n),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          Hurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_eq_sum_simplices p hp
