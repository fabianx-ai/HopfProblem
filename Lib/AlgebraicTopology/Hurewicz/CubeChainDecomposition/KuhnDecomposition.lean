/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PermutationInsertion
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.CubeChain

/-!
# The Kuhn decomposition of the cube chain

The cube chain of a based `n`-cube is the signed sum of its `n!` Kuhn simplices:

`cubeChain p = ∑ e : Perm (Fin n), cubeOrientation e • simplexChain X n (p ∘ cubeSimplex e)`

(`Hurewicz.cubeChain_eq_sum_simplices`). The proof is by induction on `n` through the
prism: the base cases are the interval (`cubeChain_one`) and the square, whose two
triangles are the Kuhn cells of the identity and of the transposition
(`lowerSquareTriangle_eq_cubeSimplex_one`, `upperSquareTriangle_eq_cubeSimplex_swap`,
`cubeChain_two`); the step (`cubeChain_eq_sum_simplices_step`) writes the cross product of
the interval chain with each Kuhn simplex of the curried cube as a prism realization,
replaces the edge cross product by the standard prism, and reindexes the shuffle
simplices by permutation insertion.

Together with the boundary of the constant simplex (`boundary_const_simplex`) this is the
chain identity behind the Hurewicz theorem: the singular chain of a spheroid is the
alternating sum of the simplices of the Kuhn (Freudenthal) triangulation of the cube
(statement of the Hurewicz theorem: Hatcher, *Algebraic Topology*, Theorem 4.32; the argument
is this development's own, recorded in `Lib/docs/C.md`, §§3 and 10–11; cross-product convention
of Hatcher, §3.B).

## Main results

* `Hurewicz.boundary_const_simplex`
* `Hurewicz.cubeChain_two`
* `Hurewicz.cubeChain_eq_sum_simplices_step`, `Hurewicz.cubeChain_eq_sum_simplices`
-/

open Set Function Topology

noncomputable section

/-! ### The square and the induction step -/

/-- The boundary of the constant `(n+1)`-simplex chain at `x` is the alternating sum
of constant `n`-simplex chains. -/
theorem Hurewicz.boundary_const_simplex {X : Type} [TopologicalSpace X] (x : X)
    (n : ℕ) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom
        (SingularChains.simplexChain X (n + 1)
          (ContinuousMap.const (SingularChains.Simplex (n + 1)) x)) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SingularChains.simplexChain X n
          (ContinuousMap.const (SingularChains.Simplex n) x) := by
  rw [SingularChains.boundary_simplex]
  simp only [ContinuousMap.const_comp]
  exact
    (map_sum (zmultiplesHom (SingularChains.Chains X n)
        (SingularChains.simplexChain X n
          (ContinuousMap.const (SingularChains.Simplex n) x)))
      (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val) Finset.univ).symm

/-- The lower triangle of the square is the identity permutation simplex. -/
theorem Hurewicz.lowerSquareTriangle_eq_cubeSimplex_one :
    Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle =
      Hurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 2)) := by
  apply ContinuousMap.ext
  intro s
  funext i
  apply Subtype.ext
  refine Fin.cases ?_ (fun j => ?_) i
  · show (↑(Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle s 0) : ℝ) =
      ↑((Hurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 2))) s
        ((1 : Equiv.Perm (Fin 2)) 0))
    rw [Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_zero,
      Hurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show (↑(Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle s 1) : ℝ) =
      ↑((Hurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 2))) s
        ((1 : Equiv.Perm (Fin 2)) 1))
    rw [Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_one,
      Hurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]

/-- The upper triangle of the square is the transposition permutation simplex. -/
theorem Hurewicz.upperSquareTriangle_eq_cubeSimplex_swap :
    Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle =
      Hurewicz.CubeTriangulation.cubeSimplex (Equiv.swap 0 1) := by
  apply ContinuousMap.ext
  intro s
  funext i
  apply Subtype.ext
  refine Fin.cases ?_ (fun j => ?_) i
  · show (↑(Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle s 0) : ℝ) =
      ↑((Hurewicz.CubeTriangulation.cubeSimplex (Equiv.swap 0 1)) s
        ((Equiv.swap (0 : Fin 2) 1) 1))
    rw [Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_zero,
      Hurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show (↑(Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle s 1) : ℝ) =
      ↑((Hurewicz.CubeTriangulation.cubeSimplex (Equiv.swap 0 1)) s
        ((Equiv.swap (0 : Fin 2) 1) 0))
    rw [Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_one,
      Hurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cube chain in degree `2` is the alternating sum of the two permutation simplices: the
second base case of the Kuhn decomposition. -/
theorem Hurewicz.cubeChain_two {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    Hurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin 2),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X 2
          (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) := by
  have hub : Hurewicz.cubeChain p = Hurewicz.DegreeTwo.squareChain p := by
    unfold Hurewicz.cubeChain
    rw [Hurewicz.fundamentalCubeChain_two, Hurewicz.DegreeTwo.squareChain,
      Hurewicz.DegreeTwo.suspensionOne_toLoop, Hurewicz.DegreeTwo.fundamentalSquareChain,
      ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
    rfl
  rw [hub, Hurewicz.DegreeTwo.SimplyConnected.squareChain_two_triangles,
    Hurewicz.lowerSquareTriangle_eq_cubeSimplex_one,
    Hurewicz.upperSquareTriangle_eq_cubeSimplex_swap]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hsign1 : Hurewicz.CubeTriangulation.cubeOrientation (1 : Equiv.Perm (Fin 2)) = 1 := by
    simp [Hurewicz.CubeTriangulation.cubeOrientation]
  have hsign2 : Hurewicz.CubeTriangulation.cubeOrientation (Equiv.swap (0 : Fin 2) 1) = -1 := by
    simp [Hurewicz.CubeTriangulation.cubeOrientation]
  rw [hsign1, hsign2]
  simp only [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The induction step of the Kuhn decomposition: from the decomposition in degree `k + 2` to
degree `k + 3`, through the prism realization (the prism decomposition of Hatcher, proof of
Theorem 2.10). -/
theorem Hurewicz.cubeChain_eq_sum_simplices_step {k : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (ih : ∀ {Y : Type} [TopologicalSpace Y] {y : Y} (q : GenLoop (Fin ((k + 1) + 1)) Y y),
      Hurewicz.cubeChain q = ∑ e : Equiv.Perm (Fin ((k + 1) + 1)),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain Y ((k + 1) + 1)
            (q.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)))
    (p : GenLoop (Fin (k + 3)) X x) :
    Hurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin (k + 3)),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X (k + 3)
          (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [Hurewicz.cubeChain_succ (n := k + 1) p, ih (Hurewicz.curryLoop p)]
  simp only [map_sum, map_zsmul,
    Hurewicz.evalLeft_crossProductEdge_intervalChain_simplex]
  rw [← Hurewicz.CubeSubdivision.orientedPrismRealization_eq_sum]
  show Hurewicz.CubeSubdivision.orientedPrismRealization p.val (k + 3)
      (SingularHomology.formalEdgeCrossProduct (k + 2)
        (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
        (SingularMayerVietoris.formalSimplex (fun j : Fin (k + 3) => j))) = _
  rw [Hurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard]
  show Hurewicz.CubeSubdivision.orientedPrismRealization p.val ((k + 2) + 1)
      (Hurewicz.CubeSubdivision.standardPrism (k + 2) (fun i : Fin 2 => i)
        (fun j : Fin ((k + 2) + 1) => j)) =
    ∑ e : Equiv.Perm (Fin ((k + 2) + 1)),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X ((k + 2) + 1)
          (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))
  rw [Hurewicz.CubeSubdivision.orientedPrismRealization_standardPrism]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Kuhn decomposition of the cube chain in every degree: the chain of a based `n`-cube is
the alternating sum of its `n!` permutation simplices. This is the chain identity
`[Π n] = Σ_σ sign(σ)·σ_e` behind this development's proof of the Hurewicz theorem (statement:
Hatcher, Theorem 4.32; the argument is recorded in `Lib/docs/C.md`; cross product as in Hatcher,
§3.B), proved by induction through the prism realization. -/
theorem Hurewicz.cubeChain_eq_sum_simplices (n : ℕ) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) :
    Hurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin n),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X n
          (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) := by
  have aux : ∀ (m : ℕ) {Y : Type} [TopologicalSpace Y] {y : Y} (q : GenLoop (Fin m) Y y),
      Hurewicz.cubeChain q = ∑ e : Equiv.Perm (Fin m),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain Y m
            (q.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro Y inst y q
      cases m with
      | zero =>
        have h1 : ∀ e : Equiv.Perm (Fin 0), e = 1 := fun e => by
          apply Equiv.ext
          intro j
          exact j.elim0
        rw [Finset.sum_eq_single 1 (fun e _ he => absurd (h1 e) he) (by simp)]
        have hsign : Hurewicz.CubeTriangulation.cubeOrientation (1 : Equiv.Perm (Fin 0)) =
            1 := by
          simp [Hurewicz.CubeTriangulation.cubeOrientation]
        rw [hsign, one_zsmul]
        unfold Hurewicz.cubeChain
        rw [show Hurewicz.fundamentalCubeChain 0 = SingularChains.pointChain 0 from rfl,
          SingularChains.pointChain, SingularChains.inducedChain_simplex]
        congr 1
        apply ContinuousMap.ext
        intro s
        apply congrArg q.val
        funext i
        exact i.elim0
      | succ m =>
        cases m with
        | zero => exact Hurewicz.cubeChain_one q
        | succ m =>
          cases m with
          | zero => exact Hurewicz.cubeChain_two q
          | succ k =>
            exact Hurewicz.cubeChain_eq_sum_simplices_step (k := k)
              (fun q' => ihm ((k + 1) + 1) (by omega) q') q
  exact aux n p
