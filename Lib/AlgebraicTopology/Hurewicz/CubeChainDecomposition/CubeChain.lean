/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization

/-!
# The fundamental cube chain

`Hurewicz.fundamentalCubeChain n` is the fundamental singular chain of the cube
`Fin n → I`, defined by recursion: the point chain for `n = 0`, the interval chain for
`n = 1`, and for `n + 2` the edge cross product (Hatcher §3.B) of the interval chain with
the fundamental chain of the `(n + 1)`-cube, pushed forward along the uncurrying map
`cubeCoordinates (n + 1) : I × Iⁿ⁺¹ → Iⁿ⁺²`. The *cube chain* of a based cube
`p : GenLoop (Fin n) X x` is its pushforward `cubeChain p = p_* (fundamentalCubeChain n)`.

The recursion is expressed on `X` by currying: `cubeChain p` is the evaluation of the
cross product of the interval chain with the cube chain of the curried cube
`curryLoop p : GenLoop (Fin n) C(I, X) _` (`cubeChain_succ`), and the cross product of the
interval chain with the `e`-th Kuhn simplex of the curried cube is the prism realization
at `e` (`evalLeft_crossProductEdge_intervalChain_simplex`) — the term that the Kuhn
decomposition step feeds into the prism argument.

The low degrees are computed explicitly: in degree `1` the cube chain is the single
permutation simplex (`cubeChain_one`), and in degree `2` the fundamental chain is the
fundamental square chain of `Lib.AlgebraicTopology.Hurewicz.PrismOperator`
(`fundamentalCubeChain_two`, `cubeChain_eq_squareChain`).

## Main definitions

* `Hurewicz.cubeCoordinates`, `Hurewicz.cubeMap`, `Hurewicz.curryLoop`
* `Hurewicz.fundamentalCubeChain`, `Hurewicz.cubeChain`

## Main results

* `Hurewicz.cubeChain_succ`, `Hurewicz.evalLeft_crossProductEdge_intervalChain_simplex`
* `Hurewicz.cubeChain_one`, `Hurewicz.fundamentalCubeChain_two`, `Hurewicz.cubeChain_eq_squareChain`
-/

open Set Function Topology

noncomputable section

/-! ### The cube chain in every degree -/

/-- Dropping the zeroth coordinate of an `n + 1`-cube: the remaining coordinates as a
continuous map. -/
def Hurewicz.cubeRemainingCoordinates (n : ℕ) :
    C(Fin n → (unitInterval), { j : Fin (n + 1) // j ≠ 0 } → (unitInterval)) where
  toFun u j := u (j.1.pred j.2)
  continuous_toFun := by fun_prop

/-- Uncurrying a cube: the continuous map `I × (Fin n → I) → Fin (n + 1) → I` inserting the
first coordinate at position `0`. General-`n` form of `Hurewicz.DegreeTwo.squareCoordinates`. -/
def Hurewicz.cubeCoordinates (n : ℕ) :
    C((unitInterval) × (Fin n → (unitInterval)), Fin (n + 1) → (unitInterval)) where
  toFun z := Cube.insertAt (0 : Fin (n + 1)) (z.1, Hurewicz.cubeRemainingCoordinates n z.2)
  continuous_toFun := by
    apply (Cube.insertAt (0 : Fin (n + 1))).continuous.comp
    fun_prop

/-! ### Cube coordinates -/

/-- The zeroth coordinate of `cubeCoordinates n z` is the interval component `z.1`. -/
@[simp]
theorem Hurewicz.cubeCoordinates_zero (n : ℕ)
    (z : (unitInterval) × (Fin n → (unitInterval))) :
    Hurewicz.cubeCoordinates n z 0 = z.1 := by
  simp [Hurewicz.cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

/-- The `j.succ` coordinate of `cubeCoordinates n z` is the cube component `z.2 j`. -/
@[simp]
theorem Hurewicz.cubeCoordinates_succ (n : ℕ)
    (z : (unitInterval) × (Fin n → (unitInterval))) (j : Fin n) :
    Hurewicz.cubeCoordinates n z j.succ = z.2 j := by
  simp [Hurewicz.cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply,
    Hurewicz.cubeRemainingCoordinates]

/-- The uncurrying preserves the boundary in the second argument. -/
theorem Hurewicz.cubeCoordinates_boundary_right (n : ℕ) (s : (unitInterval))
    {u : Fin n → (unitInterval)} (hu : u ∈ Cube.boundary (Fin n)) :
    Hurewicz.cubeCoordinates n (s, u) ∈ Cube.boundary (Fin (n + 1)) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa using hi⟩

/-- Inserting an endpoint of `I` as the zeroth cube coordinate lands on the cube boundary. -/
theorem Hurewicz.cubeCoordinates_boundary_left (n : ℕ) (t : (unitInterval))
    (u : Fin n → (unitInterval)) (ht : t = 0 ∨ t = 1) :
    Hurewicz.cubeCoordinates n (t, u) ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨0, by simpa [Hurewicz.cubeCoordinates_zero] using ht⟩

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- A constant map pushes every `n`-chain to the corresponding multiple of the constant
simplex. -/
theorem SingularChains.inducedChain_const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) (n : ℕ) (a : SingularChains.Chains X n) :
    SingularChains.inducedChain (ContinuousMap.const X y) n a =
      Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X n a •
        SingularChains.simplexChain Y n (ContinuousMap.const (SingularChains.Simplex n) y) := by
  let m : SingularChains.Chains Y n :=
    SingularChains.simplexChain Y n (ContinuousMap.const (SingularChains.Simplex n) y)
  have hf :
      SingularChains.inducedChain (ContinuousMap.const X y) n =
        SingularChains.chainLift X n (fun _ => m) := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp [SingularChains.inducedChain_simplex, ContinuousMap.const_comp,
      SingularChains.chainLift_simplex]
    rfl
  have hz : SingularChains.chainLift X n (fun _ : SingularChains.SingularSimplex X n =>
      (0 : SingularChains.Chains Y n)) = 0 := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp [SingularChains.chainLift_simplex]
  have hsub := Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant X n
    (fun _ => m) m a
  rw [hf]
  simpa [hz, sub_self] using (eq_sub_iff_add_eq.mp hsub).symm
/-- A based `n + 1`-cube as a map from the product `I × (Fin n → I)`. -/
def Hurewicz.cubeMap {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 1)) X x) : C((unitInterval) × (Fin n → (unitInterval)), X) :=
  p.val.comp (Hurewicz.cubeCoordinates n)

/-- Currying a based `n + 1`-cube to a based `n`-cube of paths. -/
def Hurewicz.curryLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 1)) X x) :
    GenLoop (Fin n) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((Hurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry, by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (Hurewicz.cubeCoordinates_boundary_right n s hu)⟩

/-- Evaluation of the curried cube recovers the cube map. -/
theorem Hurewicz.evalLeft_comp_curryLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 1)) X x) :
    (Hurewicz.CubeSubdivision.evalLeft X).comp
        ((ContinuousMap.id (unitInterval)).prodMap (Hurewicz.curryLoop p).val) =
      Hurewicz.cubeMap p := by
  ext z
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The fundamental singular chain of the topological `n`-cube `Fin n → I`, defined
recursively: the `0`-cube is the point chain, the `1`-cube is the interval chain transported
along `(Fin 1 → I) ≃ₜ I`, and the `n + 2`-cube is the cross product of the interval chain with
the `n + 1`-cube chain, transported along the uncurrying map. -/
def Hurewicz.fundamentalCubeChain :
    (n : ℕ) → SingularChains.Chains (Fin n → (unitInterval)) n
  | 0 => SingularChains.pointChain 0
  | 1 => SingularChains.inducedChain
      ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval), Fin 1 →
        (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain
  | n + 2 =>
    SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
      (SingularHomology.crossProductEdge (unitInterval) (Fin (n + 1) → (unitInterval))
        (n + 1) Hurewicz.DegreeTwo.intervalChain (Hurewicz.fundamentalCubeChain (n + 1)))

/-- The cube chain of a based `n`-cube: the image of the fundamental chain. -/
def Hurewicz.cubeChain {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin n) X x) : SingularChains.Chains X n :=
  SingularChains.inducedChain p.val n (Hurewicz.fundamentalCubeChain n)

/-- The recursive step: the fundamental `(n+2)`-cube chain is the `cubeCoordinates`
pushforward of the edge cross product of the interval chain with the
`n+1`-fundamental chain. -/
theorem Hurewicz.fundamentalCubeChain_succ (n : ℕ) :
    Hurewicz.fundamentalCubeChain (n + 2) =
      SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
        (SingularHomology.crossProductEdge (unitInterval)
          (Fin (n + 1) → (unitInterval)) (n + 1) Hurewicz.DegreeTwo.intervalChain
          (Hurewicz.fundamentalCubeChain (n + 1))) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The recursion for the cube chain: the `n + 2`-cube chain is the evaluation of the cross
product of the interval chain with the curried `n + 1`-cube chain. -/
theorem Hurewicz.cubeChain_succ {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 2)) X x) :
    Hurewicz.cubeChain p =
      (SingularChains.inducedChain (Hurewicz.CubeSubdivision.evalLeft X) ((n + 1) + 1))
        ((SingularHomology.crossProductEdge (unitInterval) C((unitInterval), X)
            (n + 1)) Hurewicz.DegreeTwo.intervalChain
          (Hurewicz.cubeChain (Hurewicz.curryLoop p))) := by
  unfold Hurewicz.cubeChain
  show (SingularChains.inducedChain p.val (n + 2) (Hurewicz.fundamentalCubeChain (n + 2))) =
    _
  rw [Hurewicz.fundamentalCubeChain_succ, ← LinearMap.comp_apply,
    ← SingularChains.inducedChain_comp,
    show p.val.comp (Hurewicz.cubeCoordinates (n + 1)) = Hurewicz.cubeMap p from rfl,
    ← Hurewicz.evalLeft_comp_curryLoop p, SingularChains.inducedChain_comp,
    LinearMap.comp_apply, SingularHomology.crossProductEdge_natural,
    SingularChains.inducedChain_id, LinearMap.id_apply]

/-- The prism cube map factors through the uncurrying map: inserting the path simplex and the
`e`-th permutation simplex along coordinate `0` gives the prism cube map. General-`n` form of
`Hurewicz.CubeSubdivision.prismCubeMap_three`. -/
theorem Hurewicz.cubeCoordinates_comp_prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Hurewicz.cubeCoordinates n).comp
        ((SingularChains.pathSimplex Path.id).prodMap
          (Hurewicz.CubeTriangulation.cubeSimplex e)) =
      Hurewicz.CubeSubdivision.prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Hurewicz.cubeCoordinates_zero n _
  · show Hurewicz.cubeCoordinates n _ j.succ = _
    rw [Hurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The key term identification of the induction step: the cross product of the interval chain
with the `e`-th simplex chain of the curried cube evaluates to the `e`-th prism realization.
General-`n` form of
`Hurewicz.CubeSubdivision.intervalTetrahedronChain_eq_prismCubeRealization`. -/
theorem Hurewicz.evalLeft_crossProductEdge_intervalChain_simplex {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin n)) :
    (SingularChains.inducedChain (Hurewicz.CubeSubdivision.evalLeft X) (n + 1))
        ((SingularHomology.crossProductEdge (unitInterval) C((unitInterval), X) n)
          Hurewicz.DegreeTwo.intervalChain
          (SingularChains.simplexChain C((unitInterval), X) n
            ((Hurewicz.curryLoop p).val.comp
              (Hurewicz.CubeTriangulation.cubeSimplex e)))) =
      Hurewicz.CubeSubdivision.prismCubeRealization p.val e (n + 1)
        ((SingularHomology.formalEdgeCrossProduct n)
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 1) => j))) := by
  rw [Hurewicz.DegreeTwo.intervalChain, SingularChains.pathChain,
    SingularHomology.crossProductEdge_simplex,
    Hurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct]
  rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
  have h : (Hurewicz.CubeSubdivision.evalLeft X).comp
        ((SingularChains.pathSimplex Path.id).prodMap
          ((Hurewicz.curryLoop p).val.comp
            (Hurewicz.CubeTriangulation.cubeSimplex e))) =
      p.val.comp (Hurewicz.CubeSubdivision.prismCubeMap e) := by
    rw [show (SingularChains.pathSimplex Path.id).prodMap
            ((Hurewicz.curryLoop p).val.comp
              (Hurewicz.CubeTriangulation.cubeSimplex e)) =
          ((ContinuousMap.id (unitInterval)).prodMap (Hurewicz.curryLoop p).val).comp
            ((SingularChains.pathSimplex Path.id).prodMap
              (Hurewicz.CubeTriangulation.cubeSimplex e)) from
        by apply ContinuousMap.ext; intro z; rfl]
    rw [← ContinuousMap.comp_assoc, Hurewicz.evalLeft_comp_curryLoop p]
    rw [Hurewicz.cubeMap, ContinuousMap.comp_assoc,
      Hurewicz.cubeCoordinates_comp_prismCubeMap]
  rw [h]

/-- The canonical identification of the interval with the `1`-cube, pulled back along the
identity path simplex, is the permutation simplex of the identity: the `n = 1` corner of the
cube-simplex dictionary. -/
theorem Hurewicz.funUniqueSymm_pathSimplex_eq_cubeSimplex_one :
    ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
        Fin 1 → (unitInterval))).comp (SingularChains.pathSimplex Path.id) =
      Hurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 1)) := by
  apply ContinuousMap.ext
  intro s
  funext j
  apply Subtype.ext
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show (s 1 : ℝ) = _
  rw [Hurewicz.CubeTriangulation.cubeSimplex,
    Hurewicz.CubeTriangulation.cubeAffineSimplex_coordinate]
  simp [Hurewicz.CubeTriangulation.cubeVertex, Fin.sum_univ_two]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cube chain in degree `1` is the single permutation simplex: the base case of the Kuhn
decomposition. -/
theorem Hurewicz.cubeChain_one {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 1) X x) :
    Hurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin 1),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X 1
          (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) := by
  have h1 : ∀ e : Equiv.Perm (Fin 1), e = 1 := fun e => by
    apply Equiv.ext
    intro j
    exact Subsingleton.elim _ _
  rw [Finset.sum_eq_single 1 (fun e _ he => absurd (h1 e) he) (by simp)]
  have hsign : Hurewicz.CubeTriangulation.cubeOrientation (1 : Equiv.Perm (Fin 1)) = 1 := by
    simp [Hurewicz.CubeTriangulation.cubeOrientation]
  rw [hsign, one_zsmul]
  unfold Hurewicz.cubeChain
  rw [show Hurewicz.fundamentalCubeChain 1 =
      SingularChains.inducedChain
        ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
          Fin 1 → (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain from rfl]
  rw [Hurewicz.DegreeTwo.intervalChain, SingularChains.pathChain, SingularChains.inducedChain_simplex,
    SingularChains.inducedChain_simplex]
  congr 1
  rw [Hurewicz.funUniqueSymm_pathSimplex_eq_cubeSimplex_one]

/-- The uncurrying map in degree `2`, pulled back along the `(Fin 1 → I) ≃ₜ I` identification,
is the square coordinates map. -/
theorem Hurewicz.cubeCoordinates_one_comp_eq_squareCoordinates :
    (Hurewicz.cubeCoordinates 1).comp
        ((ContinuousMap.id (unitInterval)).prodMap
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval)))) =
      Hurewicz.DegreeTwo.squareCoordinates := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show Hurewicz.cubeCoordinates 1 _ 0 = Hurewicz.DegreeTwo.squareCoordinates z 0
    rw [Hurewicz.cubeCoordinates_zero, Hurewicz.DegreeTwo.squareCoordinates_zero]
    rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show Hurewicz.cubeCoordinates 1 _ (0 : Fin 1).succ = Hurewicz.DegreeTwo.squareCoordinates z 1
    rw [Hurewicz.cubeCoordinates_succ, Hurewicz.DegreeTwo.squareCoordinates_one]
    rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The fundamental chain of the `2`-cube is the fundamental square chain. -/
theorem Hurewicz.fundamentalCubeChain_two :
    Hurewicz.fundamentalCubeChain 2 = Hurewicz.DegreeTwo.fundamentalSquareChain := by
  have key : (SingularHomology.crossProductEdge (unitInterval)
        (Fin 1 → (unitInterval)) 1) Hurewicz.DegreeTwo.intervalChain
        ((SingularChains.inducedChain
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval))) 1) Hurewicz.DegreeTwo.intervalChain) =
      (SingularChains.inducedChain
        ((ContinuousMap.id (unitInterval)).prodMap
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval)))) 2) Hurewicz.DegreeTwo.productSquareChain := by
    rw [Hurewicz.DegreeTwo.productSquareChain,
      SingularHomology.crossProductEdge_natural, SingularChains.inducedChain_id,
      LinearMap.id_apply]
  rw [Hurewicz.fundamentalCubeChain_succ 0,
    show Hurewicz.fundamentalCubeChain (0 + 1) =
        SingularChains.inducedChain
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain from rfl,
    key, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
    Hurewicz.cubeCoordinates_one_comp_eq_squareCoordinates]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cube chain in degree `2` is the square chain. -/
theorem Hurewicz.cubeChain_eq_squareChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    Hurewicz.cubeChain p = Hurewicz.DegreeTwo.squareChain p := by
  unfold Hurewicz.cubeChain
  rw [Hurewicz.fundamentalCubeChain_two, Hurewicz.DegreeTwo.squareChain,
    Hurewicz.DegreeTwo.suspensionOne_toLoop, Hurewicz.DegreeTwo.fundamentalSquareChain,
    ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
  rfl
