/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator
/-!
# The fundamental cube chain and its Kuhn decomposition

`Hurewicz.cubeChain_eq_sum_simplices` decomposes the cube chain of a based `n`-cube,
for every `n`, into the signed sum
`∑ e, cubeOrientation e • simplexChain X n (p.val.comp (cubeSimplex e))` over the
Freudenthal–Kuhn simplices, and `Hurewicz.cubeChain_boundary` shows that for `n ≥ 2`
the cube chain of a based cube is a cycle (`Hurewicz.cubeCycle`).

## Outline of the construction

1. Prism insertion signs: `CubeSubdivision.PermutationInsertion.insert` splices an
   omitted index back into a permutation, and `sign_insert` tracks the sign.
2. The recursive fundamental chain `Hurewicz.fundamentalCubeChain` is built by the
   edge cross product of the interval chain with the previous fundamental chain.
3. `cubeChain_eq_sum_simplices` identifies the cube chain with the signed Kuhn sum.
4. `fundamentalCubeChain_boundary_supported` bounds the support of the boundary, and
   `cubeChain_transAt_zero_*` supplies the concatenation correction term.
5. `Hurewicz.cubeChain_boundary` cancels the boundary using the face trichotomy and
   the permutation-insertion sign sum.

## Main definitions and results

* `Hurewicz.fundamentalCubeChain`, `Hurewicz.cubeChain`, `Hurewicz.cubeCycle`:
  the fundamental chain, the chain of a based cube, and its cycle.
* `Hurewicz.cubeChain_eq_sum_simplices`, `Hurewicz.cubeChain_boundary`: the Kuhn
  decomposition and the cycle property.

## References

* The construction is recorded in `Lib/docs/C.md`, §§3 and 10–11; the cross-product
  convention follows [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.B.

## Tags

cube chain, Kuhn triangulation, boundary cancellation
-/


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

/-! ### Permutation sign sums -/

/-- A signed sum over permutations vanishes if the summand is invariant under the
swap `i j` (with `i ≠ j`), since orbits pair terms of opposite orientation. -/
theorem Hurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant {n : ℕ} {A : Type*}
    [AddCommGroup A] (i j : Fin n) (hij : i ≠ j) (f : Equiv.Perm (Fin n) → A)
    (hf : ∀ e, f ((Equiv.swap i j).trans e) = f e) :
    ∑ e, Hurewicz.CubeTriangulation.cubeOrientation e • f e = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [Hurewicz.CubeTriangulation.cubeOrientation_swap e hij, hf, neg_smul, add_neg_cancel]
  · intro e _ he
    have h := congrArg (fun k : Equiv.Perm (Fin n) => k i) he
    have h' : e j = e i := by simpa using h
    exact hij (e.injective h').symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    simp

/-- The signed sum `∑ e, cubeOrientation e • a` of a constant function over
permutations vanishes for `n ≥ 2` (nontrivial `Fin n`). -/
theorem Hurewicz.CubeSubdivision.signed_sum_constant_eq_zero {n : ℕ} [Nontrivial (Fin n)]
    {A : Type*} [AddCommGroup A] (a : A) :
    ∑ e : Equiv.Perm (Fin n), Hurewicz.CubeTriangulation.cubeOrientation e • a = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  exact signed_sum_eq_zero_of_swap_invariant i j hij (fun _ => a) (fun _ => rfl)

/-! ### The prism realization -/

/-- The prism cube vertex of the pair `z = (t, k)`: coordinate `0` is the time `t`,
and coordinate `i.succ` is the `k`-th Kuhn vertex coordinate of `e` at `i`. -/
def Hurewicz.CubeSubdivision.prismCubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) : Hurewicz.CubeTriangulation.CubeN (n + 1) :=
  Fin.cases (SingularChains.pathSimplex Path.id (SingularMayerVietoris.stdVertices 1 z.1))
    (Hurewicz.CubeTriangulation.cubeVertex e z.2)

/-- The `i.succ`-coordinate of `prismCubeVertex e z` is the `e`-Kuhn vertex of `z.2`
at coordinate `i`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.prismCubeVertex_succ {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) (i : Fin n) :
    prismCubeVertex e z i.succ = Hurewicz.CubeTriangulation.cubeVertex e z.2 i :=
  rfl

/-- The affine simplex in the `(n+1)`-cube on the prism vertices `v`, viewing each
vertex as a pair `(time, Kuhn index)`. -/
def Hurewicz.CubeSubdivision.prismCubeSimplex {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    C(SingularChains.Simplex m, Hurewicz.CubeTriangulation.CubeN (n + 1)) :=
  Hurewicz.CubeTriangulation.cubeAffineSimplex (fun j => prismCubeVertex e (v j))

/-- If `z.2` differs from the swapped index `i.succ.castSucc`, the prism cube vertex
is unchanged by the adjacent transposition. -/
theorem Hurewicz.CubeSubdivision.prismCubeVertex_swap_of_ne {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (z : Fin 2 × Fin (n + 2))
    (hz : z.2 ≠ i.succ.castSucc) :
    prismCubeVertex e z = prismCubeVertex ((Equiv.swap i.castSucc i.succ).trans e) z := by
  funext coord
  refine Fin.cases ?_ (fun k => ?_) coord
  · rfl
  · exact congrFun (Hurewicz.CubeTriangulation.cubeVertex_swap_of_ne e i z.2 hz) k

/-- If no vertex of `v` uses index `i.succ.castSucc`, the prism cube simplex is
unchanged by the adjacent transposition of `e`. -/
theorem Hurewicz.CubeSubdivision.prismCubeSimplex_swap_of_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    prismCubeSimplex e v = prismCubeSimplex ((Equiv.swap i.castSucc i.succ).trans e) v := by
  apply congrArg Hurewicz.CubeTriangulation.cubeAffineSimplex
  funext j
  exact prismCubeVertex_swap_of_ne e i (v j) (hv j)

/-- If all left coordinates of the prism vertices are `0`, the prism cube simplex has
zeroth coordinate `0`. -/
theorem Hurewicz.CubeSubdivision.prismCubeSimplex_zero_of_left_zero {m n : ℕ}
    (e : Equiv.Perm (Fin n)) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) (hv : ∀ j, (v j).1 = 0)
    (s : SingularChains.Simplex m) : prismCubeSimplex e v s 0 = 0 := by
  apply Hurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp [prismCubeVertex, hv j, SingularMayerVietoris.stdVertices]

/-- If no vertex of `v` uses the last index, the prism cube simplex maps into the
face where the last ordered coordinate vanishes. -/
theorem Hurewicz.CubeSubdivision.prismCubeSimplex_zero_of_last_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ Fin.last (n + 1)) (s : SingularChains.Simplex m) :
    prismCubeSimplex e v s (e (Fin.last n)).succ = 0 := by
  apply Hurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp only [prismCubeVertex_succ, Hurewicz.CubeTriangulation.cubeVertex,
    Equiv.symm_apply_apply, Fin.val_last]
  apply if_neg
  have hne : (v j).2.val ≠ n + 1 := by
    intro h
    exact hv j (Fin.ext h)
  have hlt := (v j).2.isLt
  omega

/-- The realization of a formal prism chain by the cube map `p`: the induced chain of
`p ∘ prismCubeSimplex e` applied to the formal chain. -/
def Hurewicz.CubeSubdivision.prismCubeRealization {X : Type} [TopologicalSpace X] {n : ℕ}
    (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X)) (e : Equiv.Perm (Fin n)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      SingularChains.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v))

/-- On a simplex generator `v`, `prismCubeRealization` is the `p`-pushforward of the
affine prism simplex on `v`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.prismCubeRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    prismCubeRealization p e m (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

/-- The signed sum over permutations `e` of `cubeOrientation e • prismCubeRealization
p e m`, realizing the oriented prism of the cube map `p`. -/
def Hurewicz.CubeSubdivision.orientedPrismRealization {X : Type} [TopologicalSpace X]
    {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      SingularChains.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    ∑ e : Equiv.Perm (Fin n),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v))

/-- On a vertex family `v`, `orientedPrismRealization` is the signed sum of the
`p`-pushforwards of the prism simplices on `v`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    orientedPrismRealization p m (SingularMayerVietoris.formalSimplex v) =
      ∑ e : Equiv.Perm (Fin n),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

/-- Evaluation at the left coordinate: `(t, γ) ↦ γ t` as a continuous map
`unitInterval × C(unitInterval, X) → X`. -/
def Hurewicz.CubeSubdivision.evalLeft (X : Type) [TopologicalSpace X] :
    C((unitInterval) × C((unitInterval), X), X)
    where
  toFun z := z.2 z.1
  continuous_toFun := by fun_prop

/-- An affine cube simplex composed with an affine simplex is the affine simplex of
the composed vertices. -/
theorem Hurewicz.CubeSubdivision.cubeAffineSimplex_comp {k m n : ℕ}
    (v : Fin (n + 1) → Hurewicz.CubeTriangulation.CubeN k)
    (w : Fin (m + 1) → SingularChains.Simplex n) :
    (Hurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex w) =
      Hurewicz.CubeTriangulation.cubeAffineSimplex
        (fun j => Hurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) := by
  ext t i
  change
    (Hurewicz.CubeTriangulation.cubeAffineSimplex v
          (SingularMayerVietoris.affineSimplex w t) i :
        ℝ) =
      (Hurewicz.CubeTriangulation.cubeAffineSimplex
          (fun j => Hurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) t i :
        ℝ)
  simp only [Hurewicz.CubeTriangulation.cubeAffineSimplex_coordinate,
    SingularMayerVietoris.affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- An affine cube simplex composed with the affine simplex of standard vertices
selected by `a` is the affine simplex on the selected vertices `v ∘ a`. -/
theorem Hurewicz.CubeSubdivision.cubeAffineSimplex_comp_selectedVertices {k m n : ℕ}
    (v : Fin (n + 1) → Hurewicz.CubeTriangulation.CubeN k) (a : Fin (m + 1) → Fin (n + 1)) :
    (Hurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex
          (fun j => SingularMayerVietoris.stdVertices n (a j))) =
      Hurewicz.CubeTriangulation.cubeAffineSimplex (fun j => v (a j)) := by
  rw [cubeAffineSimplex_comp]
  simp only [Hurewicz.CubeTriangulation.cubeAffineSimplex_vertex]

/-- The prism map `Simplex 1 × Simplex n → CubeN (n+1)` sending `(t, s)` to the cube
point whose `0`-coordinate is `t` and whose `i.succ`-coordinate is the `e`-Kuhn
coordinate of `s`. -/
def Hurewicz.CubeSubdivision.prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(SingularChains.Simplex 1 × SingularChains.Simplex n,
      Hurewicz.CubeTriangulation.CubeN (n + 1))
    where
  toFun
    z :=
    Fin.cases (SingularChains.pathSimplex Path.id z.1)
      (Hurewicz.CubeTriangulation.cubeSimplex e z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (SingularChains.pathSimplex Path.id).continuous.comp continuous_fst
    · exact
        (continuous_apply j).comp
          ((Hurewicz.CubeTriangulation.cubeSimplex e).continuous.comp continuous_snd)

/-- `prismCubeMap e` composed with a product affine simplex on pair-vertices `v` is
the prism cube simplex on `v`. -/
theorem Hurewicz.CubeSubdivision.prismCubeMap_affine {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    (prismCubeMap e).comp
        (SingularHomology.productAffineSimplex
          (fun j =>
            (SingularMayerVietoris.stdVertices 1 (v j).1,
              SingularMayerVietoris.stdVertices n (v j).2))) =
      prismCubeSimplex e v := by
  apply ContinuousMap.ext
  intro t
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply Subtype.ext
    change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).1) t
          1 =
        ∑ j, t j * SingularMayerVietoris.stdVertices 1 (v j).1 1
    exact SingularMayerVietoris.affineSimplex_coordinate _ _ _
  · change
      ((Hurewicz.CubeTriangulation.cubeAffineSimplex
                (Hurewicz.CubeTriangulation.cubeVertex e)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices n (v j).2)))
          t k =
        _
    rw [cubeAffineSimplex_comp_selectedVertices]
    rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `prismCubeRealization p e m` equals the `p`-pushforward of the prism realization
chain. -/
theorem Hurewicz.CubeSubdivision.prismCubeRealization_eq_induced {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) :
    prismCubeRealization p e m =
      (SingularChains.inducedChain (p.comp (prismCubeMap e)) m).comp
        ((SingularHomology.productAffineChainMap 1 n m).comp
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.stdVertices 1) (SingularMayerVietoris.stdVertices n))
            (m + 1))) := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  simp only [prismCubeRealization_simplex, LinearMap.comp_apply,
    SingularMayerVietoris.formalMap_simplex,
    SingularHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex]
  apply congrArg (SingularChains.simplexChain X m)
  change
    p.comp (prismCubeSimplex e v) =
      p.comp
        ((prismCubeMap e).comp
          (SingularHomology.productAffineSimplex
            (fun j =>
              (SingularMayerVietoris.stdVertices 1 (v j).1,
                SingularMayerVietoris.stdVertices n (v j).2))))
  rw [prismCubeMap_affine]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism realization of `p` at permutation `e` equals the `p`-pushforward of the
edge cross product of the interval chain with the `e`-th Kuhn simplex chain. -/
theorem Hurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) :
    prismCubeRealization p e (n + 1)
        (SingularHomology.formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 1) => j))) =
      SingularChains.inducedChain (p.comp (prismCubeMap e)) (n + 1)
        (SingularHomology.productAffineChainMap 1 n (n + 1)
          (SingularHomology.formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) := by
  rw [prismCubeRealization_eq_induced]
  simp only [LinearMap.comp_apply]
  rw [SingularHomology.formalMap_edgeCrossProduct]
  simp only [SingularMayerVietoris.formalMap_simplex, Function.comp_def]

/-! ### The bad-prism submodule -/

/-- The submodule of `FormalChains (Fin 2 × Fin (q+1)) m` generated by chains
supported on the left-zero locus or on the locus omitting a nonzero index: the
formal prism terms that degenerate under realization. -/
def Hurewicz.CubeSubdivision.badPrism (q m : ℕ) :
    Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m) :=
  SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ⊔
    ⨆ i : { i : Fin (q + 1) // i ≠ 0 },
      SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i.val} m

/-- A formal chain supported on `{z | z.1 = 0}` belongs to `badPrism`. -/
theorem Hurewicz.CubeSubdivision.mem_badPrism_of_left_zero {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_left hc

/-- A formal chain supported on `{z | ∀ j, (z j).2 ≠ i}` for `i ≠ 0` belongs to
`badPrism`. -/
theorem Hurewicz.CubeSubdivision.mem_badPrism_of_omit {q m : ℕ} (i : Fin (q + 1))
    (hi : i ≠ 0) {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨i, hi⟩ hc)

/-- `badPrism` is contained in any submodule containing the left-zero and
index-omitting supported chains. -/
theorem Hurewicz.CubeSubdivision.badPrism_le {q m : ℕ}
    {P : Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m)}
    (hzero : SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ≤ P)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m ≤ P) :
    badPrism q m ≤ P :=
  sup_le hzero (iSup_le fun i => homit i.val i.property)

/-- If a linear map kills all left-zero and index-omitting supported generators, it
kills `badPrism`. -/
theorem Hurewicz.CubeSubdivision.badPrism_le_ker {q m : ℕ} {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m →ₗ[ℤ] M)
    (hzero : ∀ v, (∀ j, (v j).1 = 0) → f (SingularMayerVietoris.formalSimplex v) = 0)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → ∀ v, (∀ j, (v j).2 ≠ i) → f (SingularMayerVietoris.formalSimplex v) = 0) :
    badPrism q m ≤ LinearMap.ker f := by
  apply badPrism_le
  · exact SingularMayerVietoris.formalChainsSupported_le hzero
  · intro i hi
    exact SingularMayerVietoris.formalChainsSupported_le (homit i hi)

/-- The formal cone at `(0, 0)` of a bad-prism chain is again a bad-prism chain. -/
theorem Hurewicz.CubeSubdivision.formalCone_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalCone (0, 0) m c ∈ badPrism q (m + 1) := by
  have hle :
    badPrism q m ≤ (badPrism q (m + 1)).comap (SingularMayerVietoris.formalCone (0, 0) m) := by
    apply badPrism_le
    · intro d hd
      exact
        mem_badPrism_of_left_zero
          (SingularMayerVietoris.formalCone_mem_supported (S :=
            {z : Fin 2 × Fin (q + 1) | z.1 = 0}) (a := (0, 0)) rfl hd)
    · intro i hi d hd
      exact
        mem_badPrism_of_omit i hi (SingularMayerVietoris.formalCone_mem_supported (Ne.symm hi) hd)
  exact hle hc

/-- The formal map of `Prod.map id Fin.succ` sends bad-prism chains to bad-prism
chains. -/
theorem Hurewicz.CubeSubdivision.formalMap_succ_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2))) m c ∈
      badPrism (q + 1) m := by
  have hle :
    badPrism q m ≤
      (badPrism (q + 1) m).comap
        (SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2)))
          m) := by
    apply badPrism_le
    · intro d hd
      apply mem_badPrism_of_left_zero
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.1 = 0})
          (T := {z : Fin 2 × Fin (q + 2) | z.1 = 0}) (Prod.map id Fin.succ) (fun _ hz => hz) hd
    · intro i hi d hd
      apply mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i)
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.2 ≠ i})
          (T := {z : Fin 2 × Fin (q + 2) | z.2 ≠ i.succ}) (Prod.map id Fin.succ)
          (fun _ hz h => hz (Fin.succ_injective _ h)) hd
  exact hle hc

/-- The formal edge cross product of an edge chain with a chain omitting index `i ≠ 0`
is a bad-prism chain. -/
theorem Hurewicz.CubeSubdivision.formalEdgeCrossProduct_mem_badPrism_of_omit {q r : ℕ}
    (i : Fin (q + 1)) (hi : i ≠ 0) (c : SingularMayerVietoris.FormalChains (Fin 2) 2)
    {d : SingularMayerVietoris.FormalChains (Fin (q + 1)) (r + 1)}
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported {j | j ≠ i} (r + 1)) :
    SingularHomology.formalEdgeCrossProduct r c d ∈ badPrism q (r + 2) := by
  apply mem_badPrism_of_omit i hi
  apply
    SingularMayerVietoris.formalChainsSupported_mono (S :=
      (Set.univ : Set (Fin 2)) ×ˢ {j : Fin (q + 1) | j ≠ i}) (fun _ hz => hz.2)
  exact
    SingularHomology.formalEdgeCrossProduct_mem_supported r (S := Set.univ) (by simp) hd

/-! ### The retained first boundary -/

/-- The signed boundary sum over all faces except face `0`, retaining the first vertex. -/
def Hurewicz.CubeSubdivision.retainedFirstBoundary {W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains W (q + 2) →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) :=
  SingularMayerVietoris.formalLift fun w =>
    ∑ i : Fin (q + 1),
      (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove)

/-- On a simplex generator, the retained boundary is the signed sum of the faces with
nonzero indices. -/
@[simp]
theorem Hurewicz.CubeSubdivision.retainedFirstBoundary_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) =
      ∑ i : Fin (q + 1),
        (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove) :=
  SingularMayerVietoris.formalLift_simplex _ _

/-- The formal boundary of a simplex splits as the first-face term plus the retained
remaining boundary. -/
theorem Hurewicz.CubeSubdivision.formalBoundary_firstFace_split_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    SingularMayerVietoris.formalBoundary (q + 1) (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (Fin.tail w) +
        retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) := by
  rw [SingularMayerVietoris.formalBoundary_simplex, Fin.sum_univ_succ,
    retainedFirstBoundary_simplex]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.succAbove_zero]
  rfl

/-! ### Prism shuffles and the standard prism -/

/-- The prism vertex list of the shuffle of `v : Fin 2 → V` and `w : Fin (q+1) → W`:
`Fin (q+3)` vertices pairing initial segments of `v` with terminal segments of `w`. -/
def Hurewicz.CubeSubdivision.shufflePrismVertices {V W : Type*} {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 1) → W) (i : Fin (q + 1)) : Fin (q + 2) → V × W := fun k =>
  (if k ≤ i.castSucc then v 0 else v 1, w (i.predAbove k))

/-- The first shuffle prism vertex pairs `v 0` with `w 0`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.shufflePrismVertices_first {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i 0 = (v 0, w 0) := by simp [shufflePrismVertices]

/-- At index `0` the shuffle prism vertices use `(v 0, w 0)`. -/
theorem Hurewicz.CubeSubdivision.shufflePrismVertices_zero_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    shufflePrismVertices v w 0 = Fin.cons (v 0, w 0) (fun j => (v 1, w j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices]

/-- At successor index `j.succ` the shuffle prism vertices use `(v _, w j)`. -/
theorem Hurewicz.CubeSubdivision.shufflePrismVertices_succ_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 2) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i.succ =
      Fin.cons (v 0, w 0) (shufflePrismVertices v (Fin.tail w) i) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices, Fin.tail, Fin.le_castSucc_iff]

/-- The shuffle prism vertices are natural under maps `f : V → V'`, `g : W → W'`. -/
theorem Hurewicz.CubeSubdivision.shufflePrismVertices_map {V W V' W' : Type*} {q : ℕ}
    (f : V → V') (g : W → W') (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    Prod.map f g ∘ shufflePrismVertices v w i = shufflePrismVertices (f ∘ v) (g ∘ w) i := by
  funext k
  simp only [shufflePrismVertices, Function.comp_apply, Prod.map_apply]
  split_ifs <;> rfl

/-- The standard prism of `v` and `w`: the signed sum
`∑ i, (-1)^i • formalSimplex (shufflePrismVertices v w i)` over `Fin (q+1)`. -/
def Hurewicz.CubeSubdivision.standardPrism {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  ∑ i : Fin (q + 1),
    (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (shufflePrismVertices v w i)

/-- At right degree `0`, the standard prism is the point cross product of `v` and `w`. -/
theorem Hurewicz.CubeSubdivision.standardPrism_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) :
    standardPrism 0 v w = SingularMayerVietoris.formalSimplex (fun i => (v i, w 0)) := by
  rw [standardPrism, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.eq_zero j]
    rfl

/-- At right degree `q+1`, the standard prism is the formal edge cross product
summand built from the shuffle prism vertices. -/
theorem Hurewicz.CubeSubdivision.standardPrism_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    standardPrism (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (SingularMayerVietoris.formalMap (fun z => (v 1, z)) (q + 2)
            (SingularMayerVietoris.formalSimplex w) -
          standardPrism q v (Fin.tail w)) := by
  rw [standardPrism, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index, map_sub,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    standardPrism, map_sum, map_smul, SingularMayerVietoris.formalCone_simplex]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, shufflePrismVertices_succ_index]

/-- The standard prism is natural under `f : V → V'`, `g : W → W'`. -/
theorem Hurewicz.CubeSubdivision.formalMap_standardPrism {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (standardPrism q v w) =
      standardPrism q (f ∘ v) (g ∘ w) := by
  simp only [standardPrism, map_sum, map_smul, SingularMayerVietoris.formalMap_simplex,
    shufflePrismVertices_map]

/-- The discrepancy between the formal edge cross product and the standard prism:
the difference of the two prism decompositions. -/
def Hurewicz.CubeSubdivision.prismDiscrepancy {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  SingularHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
      (SingularMayerVietoris.formalSimplex w) -
    standardPrism q v w

/-- The prism discrepancy at right degree `0` vanishes. -/
@[simp]
theorem Hurewicz.CubeSubdivision.prismDiscrepancy_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) : prismDiscrepancy 0 v w = 0 := by
  simp only [prismDiscrepancy,
    SingularHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, standardPrism_zero, Function.comp_def, sub_self]

/-- The prism discrepancy is natural under maps `f : V → V'`, `g : W → W'`. -/
theorem Hurewicz.CubeSubdivision.formalMap_prismDiscrepancy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (prismDiscrepancy q v w) =
      prismDiscrepancy q (f ∘ v) (g ∘ w) := by
  simp only [prismDiscrepancy, map_sub, SingularHomology.formalMap_edgeCrossProduct,
    formalMap_standardPrism, SingularMayerVietoris.formalMap_simplex]

/-- The prism discrepancy of the universal edge and simplex: `prismDiscrepancy`
specialized to the standard vertex lists. -/
def Hurewicz.CubeSubdivision.canonicalPrismDiscrepancy (q : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) (q + 2) :=
  prismDiscrepancy q (fun i => i) (fun j => j)

/-- The canonical prism discrepancy at right degree `0` vanishes. -/
@[simp]
theorem Hurewicz.CubeSubdivision.canonicalPrismDiscrepancy_zero :
    canonicalPrismDiscrepancy 0 = 0 :=
  prismDiscrepancy_zero _ _

/-- Every prism discrepancy is the formal map of the canonical one. -/
theorem Hurewicz.CubeSubdivision.prismDiscrepancy_eq_map_canonical {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    prismDiscrepancy q v w =
      SingularMayerVietoris.formalMap (Prod.map v w) (q + 2) (canonicalPrismDiscrepancy q) := by
  simpa only [canonicalPrismDiscrepancy, Function.comp_def] using
    (formalMap_prismDiscrepancy v w q (fun i => i) (fun j => j)).symm

/-- The successor step: `prismDiscrepancy (q+1) v w` is the formal cone at `(v 0, w 0)`
of `-(z ↦ (v 0, z))`-image of `w`, minus the edge cross product of `v` with `∂w`,
plus `standardPrism q v (Fin.tail w)`. -/
theorem Hurewicz.CubeSubdivision.prismDiscrepancy_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            SingularHomology.formalEdgeCrossProduct q
              (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalBoundary (q + 1)
                (SingularMayerVietoris.formalSimplex w)) +
          standardPrism q v (Fin.tail w)) := by
  rw [prismDiscrepancy, SingularHomology.formalEdgeCrossProduct_simplex_succ,
    SingularHomology.formalPointCrossProduct_edge_boundary, standardPrism_succ]
  simp only [map_sub, map_add, map_neg]
  abel

/-- The retained-first-boundary part of the successor-step prism discrepancy. -/
theorem Hurewicz.CubeSubdivision.prismDiscrepancy_succ_retained {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            prismDiscrepancy q v (Fin.tail w) -
          SingularHomology.formalEdgeCrossProduct q
            (SingularMayerVietoris.formalSimplex v)
            (retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w))) := by
  rw [prismDiscrepancy_succ, formalBoundary_firstFace_split_simplex, map_add, prismDiscrepancy]
  simp only [map_sub, map_add, map_neg]
  abel

/-- The successor-step formula for the canonical prism discrepancy. -/
theorem Hurewicz.CubeSubdivision.canonicalPrismDiscrepancy_succ (q : ℕ) :
    canonicalPrismDiscrepancy (q + 1) =
      SingularMayerVietoris.formalCone ((0 : Fin 2), (0 : Fin (q + 2))) (q + 2)
        (-SingularMayerVietoris.formalSimplex (fun j : Fin (q + 2) => ((0 : Fin 2), j)) -
            SingularMayerVietoris.formalMap (Prod.map (fun i : Fin 2 => i) Fin.succ) (q + 2)
              (canonicalPrismDiscrepancy q) -
          ∑ i : Fin (q + 1),
            (-1 : ℤ) ^ (i.val + 1) •
              SingularHomology.formalEdgeCrossProduct q
                (SingularMayerVietoris.formalSimplex (fun j : Fin 2 => j))
                (SingularMayerVietoris.formalSimplex i.succ.succAbove)) := by
  change prismDiscrepancy (q + 1) (fun i : Fin 2 => i) (fun j : Fin (q + 2) => j) = _
  rw [prismDiscrepancy_succ_retained, prismDiscrepancy_eq_map_canonical]
  simp only [retainedFirstBoundary_simplex, map_sum, map_smul,
    SingularMayerVietoris.formalMap_simplex, Function.comp_def]
  rfl

/-- The canonical prism discrepancy is a bad-prism chain. -/
theorem Hurewicz.CubeSubdivision.canonicalPrismDiscrepancy_mem_badPrism (q : ℕ) :
    canonicalPrismDiscrepancy q ∈ badPrism q (q + 2) := by
  induction q with
  | zero =>
    rw [canonicalPrismDiscrepancy_zero]
    exact Submodule.zero_mem _
  | succ q ih =>
    rw [canonicalPrismDiscrepancy_succ]
    apply formalCone_mem_badPrism
    apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact
          mem_badPrism_of_left_zero
            (SingularMayerVietoris.formalSimplex_mem_supported fun _ => rfl)
      · exact formalMap_succ_mem_badPrism ih
    · apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      exact
        formalEdgeCrossProduct_mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i) _
          (SingularMayerVietoris.formalSimplex_mem_supported fun j => Fin.succAbove_ne i.succ j)

/-! ### Vanishing of the oriented prism on bad terms -/

/-- The oriented prism realization vanishes on generators whose left coordinate is
`0`. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_left_zero {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).1 = 0) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (SingularChains.Simplex m) x := by
    ext s
    exact GenLoop.boundary p _ ⟨0, Or.inl (prismCubeSimplex_zero_of_left_zero e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

/-- The oriented prism realization vanishes on generators omitting the last index. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_last_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ Fin.last (n + 2)) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (SingularChains.Simplex m) x := by
    ext s
    exact
      GenLoop.boundary p _
        ⟨(e (Fin.last (n + 1))).succ, Or.inl (prismCubeSimplex_zero_of_last_omitted e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

/-- The oriented prism realization vanishes on generators omitting an interior index. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_interior_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 1))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  rw [orientedPrismRealization_simplex]
  apply
    signed_sum_eq_zero_of_swap_invariant i.castSucc i.succ
      (by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega)
  intro e
  exact
    congrArg (fun f => SingularChains.simplexChain X m (p.val.comp f))
      (prismCubeSimplex_swap_of_omitted e i v hv).symm

/-- The oriented prism realization vanishes on generators omitting any nonzero index. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_nonzero_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 3))
    (hi : i ≠ 0) (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  by_cases hlast : i = Fin.last (n + 2)
  · subst i
    exact orientedPrismRealization_last_omitted p v hv
  have hi0 : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  have hilast : i.val ≠ n + 2 := by
    intro h
    exact hlast (Fin.ext h)
  have hi_lt := i.isLt
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hj : j.succ.castSucc = i := by
    apply Fin.ext
    dsimp [j]
    omega
  apply orientedPrismRealization_interior_omitted p j v
  simpa only [hj] using hv

/-- The oriented prism realization kills the bad-prism submodule. -/
theorem Hurewicz.CubeSubdivision.badPrism_le_ker_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (m : ℕ) :
    badPrism (n + 2) (m + 1) ≤ LinearMap.ker (orientedPrismRealization p.val m) :=
  badPrism_le_ker _ (fun v hv => orientedPrismRealization_left_zero p v hv)
    (fun i hi v hv => orientedPrismRealization_nonzero_omitted p i hi v hv)

/-- The oriented prism realization of the canonical prism discrepancy vanishes. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_canonicalPrismDiscrepancy
    {X : Type} [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3) (canonicalPrismDiscrepancy (n + 2)) = 0 :=
  badPrism_le_ker_orientedPrismRealization p (n + 3)
    (canonicalPrismDiscrepancy_mem_badPrism (n + 2))

/-- The oriented prism realization of the edge cross product equals that of the
standard prism. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3)
        (SingularHomology.formalEdgeCrossProduct (n + 2)
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 3) => j))) =
      orientedPrismRealization p.val (n + 3)
        (standardPrism (n + 2) (fun i : Fin 2 => i) (fun j : Fin (n + 3) => j)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact orientedPrismRealization_canonicalPrismDiscrepancy p

private theorem Hurewicz.CubeSubdivision.linearMap_zsmul_apply_mo1973_8057 {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] (r : ℤ) (f : M →ₗ[ℤ] N) (a : M) :
    (r • f) a = r • f a :=
  map_zsmul (LinearMap.evalAddMonoidHom a) r f

/-- The oriented prism realization of `p` equals the signed sum of the `p`-pushforward
Kuhn-cell chains. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_eq_sum {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1)) :
    orientedPrismRealization p m c =
      ∑ e : Equiv.Perm (Fin n),
        Hurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m c := by
  classical
  have h :
    orientedPrismRealization p m =
      ∑ e : Equiv.Perm (Fin n),
        Hurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [orientedPrismRealization_simplex, LinearMap.sum_apply,
      linearMap_zsmul_apply_mo1973_8057, prismCubeRealization_simplex]
  simpa only [LinearMap.sum_apply, linearMap_zsmul_apply_mo1973_8057] using
    LinearMap.congr_fun h c

/-! ### Permutation insertion -/

/-- The permutation of `Fin (n+1)` obtained from `e : Perm (Fin n)` by inserting the
index `k` at position `0` (sending `k` to `0` and `succAbove`ing the rest). -/
def Hurewicz.CubeSubdivision.PermutationInsertion.insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e) * k.cycleRange

/-- `insert k e` sends `k` to `0`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_apply_self {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Hurewicz.CubeSubdivision.PermutationInsertion.insert k e k = 0 := by
  simp [Hurewicz.CubeSubdivision.PermutationInsertion.insert]

/-- `insert k e` sends `k.succAbove j` to `(e j).succ`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_apply_succAbove {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    Hurewicz.CubeSubdivision.PermutationInsertion.insert k e (k.succAbove j) = (e j).succ :=
  by simp [Hurewicz.CubeSubdivision.PermutationInsertion.insert]

/-- The inverse of `insert k e` sends `0` to `k`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_zero {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm 0 = k := by
  apply (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

/-- The inverse of `insert k e` sends `r.succ` to `k.succAbove (e.symm r)`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_succ {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm j.succ =
      k.succAbove (e.symm j) := by
  apply (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

/-- The sign of `insert k e` is `(-1)^k` times the sign of `e`. -/
@[simp]
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sign_insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e) =
      (-1) ^ (k : ℕ) * Equiv.Perm.sign e := by
  simp [Hurewicz.CubeSubdivision.PermutationInsertion.insert, mul_comm]

/-- The integer sign of `insert k e` is `(-1)^k` times the integer sign of `e`. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sign_insert_int {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e) : ℤ) =
      (-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ) := by simp

/-- `j.val < (k.predAbove r).val` iff `(k.succAbove j).val < r.val`. -/
theorem Hurewicz.CubeSubdivision.lt_predAbove_iff_succAbove_lt {n : ℕ} (k : Fin (n + 1))
    (j : Fin n) (r : Fin (n + 2)) : j.val < (k.predAbove r).val ↔ (k.succAbove j).val < r.val := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- The prism cube vertex of the shuffle at index `r` equals the prism cube vertex of
the inserted permutation `insert r e`. -/
theorem Hurewicz.CubeSubdivision.prismCubeVertex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (r : Fin (n + 2)) :
    prismCubeVertex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k r) =
      Hurewicz.CubeTriangulation.cubeVertex (PermutationInsertion.insert k e) r := by
  funext coord
  refine Fin.cases ?_ (fun j => ?_) coord
  · by_cases h : r ≤ k.castSucc
    · have h' : ¬k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_lt] using h
      simp [prismCubeVertex, shufflePrismVertices, h, Hurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
    · have h' : k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_le] using h
      simp [prismCubeVertex, shufflePrismVertices, h, Hurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
  · simp only [shufflePrismVertices, prismCubeVertex_succ,
      Hurewicz.CubeTriangulation.cubeVertex, PermutationInsertion.insert_symm_apply_succ]
    simp only [lt_predAbove_iff_succAbove_lt]

/-- The prism cube simplex of the shuffle at `k` equals the prism cube simplex of
`insert k e`. -/
theorem Hurewicz.CubeSubdivision.prismCubeSimplex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    prismCubeSimplex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k) =
      Hurewicz.CubeTriangulation.cubeSimplex (PermutationInsertion.insert k e) := by
  apply congrArg Hurewicz.CubeTriangulation.cubeAffineSimplex
  funext r
  exact prismCubeVertex_shuffle e k r

/-- Insertion `(k, e) ↦ insert k e` is injective. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_injective {n : ℕ} :
    Function.Injective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        Hurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  rintro ⟨k, e⟩ ⟨l, f⟩ h
  have hk : k = l := by simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0) h
  subst l
  refine Prod.ext rfl ?_
  apply Equiv.ext
  intro j
  apply Fin.succ_injective n
  simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (k.succAbove j)) h

/-- Insertion `(k, e) ↦ insert k e` is bijective onto `Perm (Fin (n+1))`. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.insert_bijective {n : ℕ} :
    Function.Bijective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        Hurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨insert_injective, by simp [Fintype.card_perm, Nat.factorial_succ]⟩

/-- Sums over `Perm (Fin (n+1))` reindex as double sums over `k` and
`Perm (Fin n)` via insertion. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sum_insert {n : ℕ} {A : Type*}
    [AddCommMonoid A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          f (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f σ := by
  rw [← Fintype.sum_prod_type']
  exact insert_bijective.sum_comp f

/-- The sign-weighted sum over `Perm (Fin (n+1))` reindexed by insertion picks up the
factor `(-1)^k`. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sum_sign_insert {n : ℕ} {A : Type*}
    [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          ((-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ)) •
            f (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [sign_insert_int] using sum_insert (fun σ => (Equiv.Perm.sign σ : ℤ) • f σ)

/-- The `(-1)^k •`-weighted sum over `Perm (Fin (n+1))` reindexed by insertion. -/
theorem Hurewicz.CubeSubdivision.PermutationInsertion.sum_sign_smul_insert {n : ℕ}
    {A : Type*} [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          (-1 : ℤ) ^ (k : ℕ) •
            ((Equiv.Perm.sign e : ℤ) •
              f (Hurewicz.CubeSubdivision.PermutationInsertion.insert k e))) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [SemigroupAction.mul_smul] using sum_sign_insert f

/-- The oriented prism realization of the standard prism equals the signed Kuhn-cell
sum of `p`. -/
theorem Hurewicz.CubeSubdivision.orientedPrismRealization_standardPrism {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(Hurewicz.CubeTriangulation.CubeN (n + 1), X)) :
    orientedPrismRealization p (n + 1)
        (standardPrism n (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j)) =
      ∑ perm : Equiv.Perm (Fin (n + 1)),
        Hurewicz.CubeTriangulation.cubeOrientation perm •
          SingularChains.simplexChain X (n + 1)
            (p.comp (Hurewicz.CubeTriangulation.cubeSimplex perm)) := by
  simp only [standardPrism, map_sum, map_zsmul, orientedPrismRealization_simplex,
    prismCubeSimplex_shuffle, ← Finset.sum_zsmul,
    Hurewicz.CubeTriangulation.cubeOrientation]
  exact
    PermutationInsertion.sum_sign_smul_insert
      (fun perm =>
        SingularChains.simplexChain X (n + 1)
          (p.comp (Hurewicz.CubeTriangulation.cubeSimplex perm)))

/-! ## The cube chain in every degree and its Kuhn decomposition (textbook §10.3) -/

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

/-- Scale coordinate `i` of the cube onto the left half `[0, 1/2]`. -/
def Hurewicz.cubeScaleLeft {n : ℕ} (i : Fin n) :
    C(Fin n → (unitInterval), Fin n → (unitInterval)) where
  toFun t := Function.update t i ⟨(t i : ℝ) / 2, by
    constructor
    · linarith [unitInterval.nonneg (t i)]
    · have := unitInterval.le_one (t i)
      linarith⟩
  continuous_toFun := by fun_prop

/-- Scale coordinate `i` of the cube onto the right half `[1/2, 1]`. -/
def Hurewicz.cubeScaleRight {n : ℕ} (i : Fin n) :
    C(Fin n → (unitInterval), Fin n → (unitInterval)) where
  toFun t := Function.update t i ⟨((t i : ℝ) + 1) / 2, by
    constructor
    · have := unitInterval.nonneg (t i)
      linarith
    · have := unitInterval.le_one (t i)
      linarith⟩
  continuous_toFun := by fun_prop

/-- Scale the interval onto the left half `[0, 1/2]`. -/
def Hurewicz.intervalScaleLeft : C((unitInterval), (unitInterval)) where
  toFun t := ⟨(t : ℝ) / 2, by
    constructor
    · linarith [unitInterval.nonneg t]
    · have := unitInterval.le_one t
      linarith⟩
  continuous_toFun := by fun_prop

/-- Scale the interval onto the right half `[1/2, 1]`. -/
def Hurewicz.intervalScaleRight : C((unitInterval), (unitInterval)) where
  toFun t := ⟨((t : ℝ) + 1) / 2, by
    constructor
    · have := unitInterval.nonneg t
      linarith
    · have := unitInterval.le_one t
      linarith⟩
  continuous_toFun := by fun_prop

/-- The path along `intervalScaleLeft`, from `0` to `1/2`. -/
def Hurewicz.intervalPathLeft : Path (0 : (unitInterval)) ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ where
  toContinuousMap := Hurewicz.intervalScaleLeft
  source' := by
    apply Subtype.ext
    change (0 : ℝ) / 2 = 0
    norm_num
  target' := by
    apply Subtype.ext
    change (1 : ℝ) / 2 = (1 : ℝ) / 2
    rfl

/-- The path along `intervalScaleRight`, from `1/2` to `1`. -/
def Hurewicz.intervalPathRight :
    Path ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ (1 : (unitInterval)) where
  toContinuousMap := Hurewicz.intervalScaleRight
  source' := by
    apply Subtype.ext
    change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
    norm_num
  target' := by
    apply Subtype.ext
    change ((1 : ℝ) + 1) / 2 = 1
    norm_num

/-- Concatenating the two half-interval paths recovers the identity path. -/
theorem Hurewicz.intervalPathLeft_trans_intervalPathRight :
    Hurewicz.intervalPathLeft.trans Hurewicz.intervalPathRight = Path.id := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · change (2 * (t : ℝ)) / 2 = (t : ℝ)
    ring
  · change ((2 * (t : ℝ) - 1) + 1) / 2 = (t : ℝ)
    ring

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The identity interval chain is the sum of the two half-interval chains, up to the
boundary of the concatenation 2-simplex. -/
theorem Hurewicz.intervalChain_split :
    SingularChains.inducedChain Hurewicz.intervalScaleLeft 1 Hurewicz.DegreeTwo.intervalChain +
        SingularChains.inducedChain Hurewicz.intervalScaleRight 1
          Hurewicz.DegreeTwo.intervalChain -
      Hurewicz.DegreeTwo.intervalChain =
      ((SingularChains.singularComplex (unitInterval)).d 2 1).hom
        (SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight) := by
  have h :=
    SingularChains.boundaryTwo_concatChain Hurewicz.intervalPathLeft
      Hurewicz.intervalPathRight
  rw [show ((SingularChains.singularComplex (unitInterval)).d 2 1).hom = SingularChains.boundaryTwo
      (unitInterval) from rfl, h, Hurewicz.intervalPathLeft_trans_intervalPathRight,
    ← Hurewicz.DegreeTwo.induced_intervalChain Hurewicz.intervalPathLeft,
    ← Hurewicz.DegreeTwo.induced_intervalChain Hurewicz.intervalPathRight]
  simp only [Hurewicz.intervalPathLeft, Hurewicz.intervalPathRight]
  abel

/-- Left scaling on coordinate `0` is left scaling of the interval factor. -/
theorem Hurewicz.cubeScaleLeft_zero_comp_cubeCoordinates (n : ℕ) :
    (Hurewicz.cubeScaleLeft (0 : Fin (n + 1))).comp
        (Hurewicz.cubeCoordinates n) =
      (Hurewicz.cubeCoordinates n).comp
        (Hurewicz.intervalScaleLeft.prodMap (ContinuousMap.id _)) := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_self,
      Hurewicz.cubeCoordinates_zero, Hurewicz.intervalScaleLeft]
  · have hj : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
    simp [Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_of_ne hj,
      Hurewicz.cubeCoordinates_succ]

/-- Right scaling on coordinate `0` is right scaling of the interval factor. -/
theorem Hurewicz.cubeScaleRight_zero_comp_cubeCoordinates (n : ℕ) :
    (Hurewicz.cubeScaleRight (0 : Fin (n + 1))).comp
        (Hurewicz.cubeCoordinates n) =
      (Hurewicz.cubeCoordinates n).comp
        (Hurewicz.intervalScaleRight.prodMap (ContinuousMap.id _)) := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self,
      Hurewicz.cubeCoordinates_zero, Hurewicz.intervalScaleRight]
  · have hj : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
    simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_of_ne hj,
      Hurewicz.cubeCoordinates_succ]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Scaling the zeroth coordinate of the fundamental `(n+2)`-cube onto each half, then
subtracting the unscaled cube, is the cross product of the interval-split 2-chain
against the remaining fundamental cube. -/
theorem Hurewicz.cubeScale_zero_sum_fundamentalCubeChain (n : ℕ) :
    SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2)) +
        SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2)) -
      Hurewicz.fundamentalCubeChain (n + 2) =
      SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
        (SingularHomology.crossProductEdge (unitInterval)
          (Fin (n + 1) → (unitInterval)) (n + 1)
          (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight))
          (Hurewicz.fundamentalCubeChain (n + 1))) := by
  rw [Hurewicz.fundamentalCubeChain_succ]
  have hL :
      SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
          (SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
            (SingularHomology.crossProductEdge (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1) Hurewicz.DegreeTwo.intervalChain
              (Hurewicz.fundamentalCubeChain (n + 1)))) =
        SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
          (SingularHomology.crossProductEdge (unitInterval)
            (Fin (n + 1) → (unitInterval)) (n + 1)
            (SingularChains.inducedChain Hurewicz.intervalScaleLeft 1
              Hurewicz.DegreeTwo.intervalChain)
            (Hurewicz.fundamentalCubeChain (n + 1))) := by
    rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.cubeScaleLeft_zero_comp_cubeCoordinates, SingularChains.inducedChain_comp,
      LinearMap.comp_apply, SingularHomology.crossProductEdge_natural,
      SingularChains.inducedChain_id, LinearMap.id_apply]
  have hR :
      SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
          (SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
            (SingularHomology.crossProductEdge (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1) Hurewicz.DegreeTwo.intervalChain
              (Hurewicz.fundamentalCubeChain (n + 1)))) =
        SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
          (SingularHomology.crossProductEdge (unitInterval)
            (Fin (n + 1) → (unitInterval)) (n + 1)
            (SingularChains.inducedChain Hurewicz.intervalScaleRight 1
              Hurewicz.DegreeTwo.intervalChain)
            (Hurewicz.fundamentalCubeChain (n + 1))) := by
    rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.cubeScaleRight_zero_comp_cubeCoordinates, SingularChains.inducedChain_comp,
      LinearMap.comp_apply, SingularHomology.crossProductEdge_natural,
      SingularChains.inducedChain_id, LinearMap.id_apply]
  rw [hL, hR, ← map_add, ← map_sub]
  rw [← LinearMap.add_apply, ← LinearMap.sub_apply, ← map_add, ← map_sub,
    Hurewicz.intervalChain_split]

/-- Concatenation along `i` composed with left scaling recovers the first cube. -/
theorem Hurewicz.transAt_comp_cubeScaleLeft {n : ℕ} [DecidableEq (Fin n)] {X : Type}
    [TopologicalSpace X] {x : X} (i : Fin n) (p q : GenLoop (Fin n) X x) :
    (GenLoop.transAt i p q).val.comp (Hurewicz.cubeScaleLeft i) = p.val := by
  apply ContinuousMap.ext
  intro t
  have hle : ((Hurewicz.cubeScaleLeft i t) i : ℝ) ≤ 1 / 2 := by
    simp [Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_self]
    have := unitInterval.le_one (t i)
    linarith
  have ht :
      (GenLoop.transAt i p q).val (Hurewicz.cubeScaleLeft i t) =
        if ((Hurewicz.cubeScaleLeft i t) i : ℝ) ≤ 1 / 2 then
          p (Function.update (Hurewicz.cubeScaleLeft i t) i
            (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleLeft i t) i : ℝ))))
        else
          q (Function.update (Hurewicz.cubeScaleLeft i t) i
            (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleLeft i t) i : ℝ) - 1))) :=
    rfl
  rw [ContinuousMap.comp_apply, ht, if_pos hle]
  apply congrArg p
  funext j
  by_cases hj : j = i
  · simp [hj, Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_self]
    apply Subtype.ext
    have hti := unitInterval.nonneg (t i)
    have hti' := unitInterval.le_one (t i)
    have hm : 2 * ((t i : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
      have hx : 2 * ((t i : ℝ) / 2) = (t i : ℝ) := by ring
      rw [hx]
      exact ⟨hti, hti'⟩
    rw [Set.projIcc_of_mem (hx := hm)]
    ring
  · simp [hj, Hurewicz.cubeScaleLeft, ContinuousMap.coe_mk, Function.update_of_ne]

/-- Concatenation along `i` composed with right scaling recovers the second cube. -/
theorem Hurewicz.transAt_comp_cubeScaleRight {n : ℕ} [DecidableEq (Fin n)] {X : Type}
    [TopologicalSpace X] {x : X} (i : Fin n) (p q : GenLoop (Fin n) X x) :
    (GenLoop.transAt i p q).val.comp (Hurewicz.cubeScaleRight i) = q.val := by
  apply ContinuousMap.ext
  intro t
  have hri : ((Hurewicz.cubeScaleRight i t) i : ℝ) = ((t i : ℝ) + 1) / 2 := by
    simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self]
  have ht :
      (GenLoop.transAt i p q).val (Hurewicz.cubeScaleRight i t) =
        if ((Hurewicz.cubeScaleRight i t) i : ℝ) ≤ 1 / 2 then
          p (Function.update (Hurewicz.cubeScaleRight i t) i
            (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleRight i t) i : ℝ))))
        else
          q (Function.update (Hurewicz.cubeScaleRight i t) i
            (Set.projIcc 0 1 zero_le_one
              (2 * ((Hurewicz.cubeScaleRight i t) i : ℝ) - 1))) :=
    rfl
  by_cases hle : ((Hurewicz.cubeScaleRight i t) i : ℝ) ≤ 1 / 2
  · have ht0 : (t i : ℝ) = 0 := by
      have := unitInterval.nonneg (t i)
      linarith
    rw [ContinuousMap.comp_apply, ht, if_pos hle]
    have hp : p (Function.update (Hurewicz.cubeScaleRight i t) i
        (Set.projIcc 0 1 zero_le_one (2 * ((Hurewicz.cubeScaleRight i t) i : ℝ)))) = x := by
      apply p.property
      refine ⟨i, Or.inr ?_⟩
      simp [Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self, hri, ht0]
    have hq : q t = x := by
      apply q.property
      refine ⟨i, Or.inl ?_⟩
      apply Subtype.ext
      exact ht0
    exact hp.trans hq.symm
  · rw [ContinuousMap.comp_apply, ht, if_neg hle]
    apply congrArg q
    funext j
    by_cases hj : j = i
    · simp [hj, Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_self]
      apply Subtype.ext
      have hti := unitInterval.nonneg (t i)
      have hti' := unitInterval.le_one (t i)
      have hm : 2 * (((t i : ℝ) + 1) / 2) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        have hx : 2 * (((t i : ℝ) + 1) / 2) - 1 = (t i : ℝ) := by ring
        rw [hx]
        exact ⟨hti, hti'⟩
      rw [Set.projIcc_of_mem (hx := hm)]
      ring
    · simp [hj, Hurewicz.cubeScaleRight, ContinuousMap.coe_mk, Function.update_of_ne]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cube chains of `p`, `q`, and `transAt 0 p q` differ by the pushforward of the
interval-split identity along the uncurrying of `transAt`. -/
theorem Hurewicz.cubeChain_transAt_zero_diff {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    Hurewicz.cubeChain p + Hurewicz.cubeChain q -
        Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (n + 2)) p q) =
      SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
        (SingularHomology.crossProductEdge (unitInterval)
          (Fin (n + 1) → (unitInterval)) (n + 1)
          (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight))
          (Hurewicz.fundamentalCubeChain (n + 1))) := by
  -- `Fin (n + 2)` already has `DecidableEq`.
  have hp : Hurewicz.cubeChain p =
      SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
        (SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2))) := by
    rw [Hurewicz.cubeChain, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.transAt_comp_cubeScaleLeft]
  have hq : Hurewicz.cubeChain q =
      SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
        (SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
          (Hurewicz.fundamentalCubeChain (n + 2))) := by
    rw [Hurewicz.cubeChain, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
      Hurewicz.transAt_comp_cubeScaleRight]
  calc
    Hurewicz.cubeChain p + Hurewicz.cubeChain q -
          Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (n + 2)) p q) =
        SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
            (SingularChains.inducedChain (Hurewicz.cubeScaleLeft (0 : Fin (n + 2))) (n + 2)
                (Hurewicz.fundamentalCubeChain (n + 2)) +
              SingularChains.inducedChain (Hurewicz.cubeScaleRight (0 : Fin (n + 2))) (n + 2)
                (Hurewicz.fundamentalCubeChain (n + 2)) -
              Hurewicz.fundamentalCubeChain (n + 2)) := by
      rw [hp, hq, Hurewicz.cubeChain]
      simp only [map_add, map_sub]
    _ = SingularChains.inducedChain (GenLoop.transAt (0 : Fin (n + 2)) p q).val (n + 2)
          (SingularChains.inducedChain (Hurewicz.cubeCoordinates (n + 1)) (n + 2)
            (SingularHomology.crossProductEdge (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1)
              (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
                (SingularChains.concatChain Hurewicz.intervalPathLeft
                  Hurewicz.intervalPathRight))
              (Hurewicz.fundamentalCubeChain (n + 1)))) := by
      rw [Hurewicz.cubeScale_zero_sum_fundamentalCubeChain]
    _ = _ := by
      rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `transAt 0` cube-chain difference is a boundary minus the extra term coming from
the remaining cube's own boundary. -/
theorem Hurewicz.cubeChain_transAt_zero_diff_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    Hurewicz.cubeChain p + Hurewicz.cubeChain q -
        Hurewicz.cubeChain (GenLoop.transAt (0 : Fin (n + 2)) p q) =
      ((SingularChains.singularComplex X).d (n + 3) (n + 2)).hom
          (SingularChains.inducedChain
            ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
              (Hurewicz.cubeCoordinates (n + 1))) (n + 3)
            (SingularHomology.crossProductTriangle (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1)
              (SingularChains.concatChain Hurewicz.intervalPathLeft
                Hurewicz.intervalPathRight)
              (Hurewicz.fundamentalCubeChain (n + 1)))) -
        SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
          (SingularHomology.crossProductTriangle (unitInterval)
            (Fin (n + 1) → (unitInterval)) n
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight)
            (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
              (Hurewicz.fundamentalCubeChain (n + 1)))) := by
  rw [Hurewicz.cubeChain_transAt_zero_diff]
  have h := SingularHomology.crossProductTriangle_boundary n
    (SingularChains.concatChain Hurewicz.intervalPathLeft
      Hurewicz.intervalPathRight)
    (Hurewicz.fundamentalCubeChain (n + 1))
  have h' :
      SingularHomology.crossProductEdge (unitInterval)
            (Fin (n + 1) → (unitInterval)) (n + 1)
          (((SingularChains.singularComplex (unitInterval)).d 2 1).hom
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight))
          (Hurewicz.fundamentalCubeChain (n + 1)) =
        ((SingularChains.singularComplex
              (unitInterval × (Fin (n + 1) → (unitInterval)))).d (n + 3) (n + 2)).hom
            (SingularHomology.crossProductTriangle (unitInterval)
              (Fin (n + 1) → (unitInterval)) (n + 1)
              (SingularChains.concatChain Hurewicz.intervalPathLeft
                Hurewicz.intervalPathRight)
              (Hurewicz.fundamentalCubeChain (n + 1))) -
          SingularHomology.crossProductTriangle (unitInterval)
            (Fin (n + 1) → (unitInterval)) n
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight)
            (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
              (Hurewicz.fundamentalCubeChain (n + 1))) := by
    rw [h]
    abel
  rw [h', map_sub, SingularChains.inducedChain_boundary]

/-- Concatenation along coordinate `0` is based on every remaining-coordinate slice that
lies on the remaining cube's boundary. -/
theorem Hurewicz.transAt_cubeCoordinates_of_mem_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) (s : (unitInterval))
    {u : Fin (n + 1) → (unitInterval)} (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    (GenLoop.transAt (0 : Fin (n + 2)) p q).val
        (Hurewicz.cubeCoordinates (n + 1) (s, u)) = x :=
  (GenLoop.transAt (0 : Fin (n + 2)) p q).property _
    (Hurewicz.cubeCoordinates_boundary_right (n + 1) s hu)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The extra term vanishes in degree `2`: the remaining cube is an interval, whose
boundary is two points, and concatenation is based at both. -/
theorem Hurewicz.cubeChain_transAt_zero_extra_zero {X : Type} [TopologicalSpace X]
    {x : X} (p q : GenLoop (Fin 2) X x) :
    SingularChains.inducedChain
        ((GenLoop.transAt (0 : Fin 2) p q).val.comp (Hurewicz.cubeCoordinates 1)) 2
      (SingularHomology.crossProductTriangle (unitInterval)
        (Fin 1 → (unitInterval)) 0
        (SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight)
        (((SingularChains.singularComplex (Fin 1 → (unitInterval))).d 1 0).hom
          (Hurewicz.fundamentalCubeChain 1))) = 0 := by
  have hfun :
      (Hurewicz.fundamentalCubeChain 1) =
        SingularChains.inducedChain
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain :=
    rfl
  rw [hfun, ← SingularChains.inducedChain_boundary, Hurewicz.DegreeTwo.intervalChain_boundary, map_sub]
  have hnat (c : SingularChains.Chains (unitInterval) 0) :
      SingularHomology.crossProductTriangle (unitInterval)
            (Fin 1 → (unitInterval)) 0
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight)
          (SingularChains.inducedChain
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval))) 0 c) =
        SingularChains.inducedChain
          ((ContinuousMap.id (unitInterval)).prodMap
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval)))) 2
          (SingularHomology.crossProductTriangle (unitInterval) (unitInterval) 0
            (SingularChains.concatChain Hurewicz.intervalPathLeft
              Hurewicz.intervalPathRight) c) := by
    have h := SingularHomology.crossProductTriangle_natural
      (ContinuousMap.id (unitInterval))
      ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
        Fin 1 → (unitInterval))) 0
      (SingularChains.concatChain Hurewicz.intervalPathLeft
        Hurewicz.intervalPathRight) c
    simpa [SingularChains.inducedChain_id] using h.symm
  rw [map_sub, hnat (SingularChains.pointChain 1), hnat (SingularChains.pointChain 0),
    ← map_sub]
  simp only [Hurewicz.DegreeTwo.crossProductTriangle_point_right]
  have hx (y : (unitInterval))
      (hy : ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm y) ∈ Cube.boundary (Fin 1)) :
      ((GenLoop.transAt (0 : Fin 2) p q).val.comp (Hurewicz.cubeCoordinates 1)).comp
          (((ContinuousMap.id (unitInterval)).prodMap
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval)))).comp
            (SingularHomology.crossInsertRight y)) =
        ContinuousMap.const (unitInterval) x := by
    apply ContinuousMap.ext
    intro s
    exact Hurewicz.transAt_cubeCoordinates_of_mem_boundary p q s hy
  have h0 : ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm (0 : (unitInterval))) ∈
      Cube.boundary (Fin 1) := ⟨0, Or.inl (by simp [Homeomorph.funUnique])⟩
  have h1 : ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm (1 : (unitInterval))) ∈
      Cube.boundary (Fin 1) := ⟨0, Or.inr (by simp [Homeomorph.funUnique])⟩
  simp only [map_sub, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
  rw [hx 1 h1, hx 0 h0, sub_self]

/-- Pushforward along a map whose image lies in `V` lands in the `V`-supported chains. -/
theorem SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (V : Set Y)
    (hf : ∀ x, f x ∈ V) (n : ℕ) (a : SingularChains.Chains X n) :
    SingularChains.inducedChain f n a ∈
      SingularMayerVietoris.supportedChainSubmodule V n := by
  have hle : (⊤ : Submodule ℤ (SingularChains.Chains X n)) ≤
      (SingularMayerVietoris.supportedChainSubmodule V n).comap
        (SingularChains.inducedChain f n) := by
    rw [← SingularChains.simplexChain_span X n]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, rfl⟩
    change SingularChains.inducedChain f n (SingularChains.simplexChain X n σ) ∈
      SingularMayerVietoris.supportedChainSubmodule V n
    rw [SingularChains.inducedChain_simplex]
    apply SingularMayerVietoris.simplexChain_mem_supported
    rintro y ⟨s, rfl⟩
    exact hf (σ s)
  exact hle (Submodule.mem_top)

/-- The zero-simplex value of the constant `0`-simplex at `x` is `x`. -/
theorem SingularHomology.zeroSimplexValue_const {X : Type} [TopologicalSpace X]
    (x : X) :
    SingularHomology.zeroSimplexValue
      (ContinuousMap.const (SingularChains.Simplex 0) x) = x :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degree-`0`-left cross product of the point chain at `x` with `b` is the
`x`-insertion pushforward of `b`. -/
theorem SingularHomology.crossProductZeroLeft_pointChain {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (x : X)
    (b : SingularChains.Chains Y n) :
    SingularHomology.crossProductZeroLeft X Y n (SingularChains.pointChain x) b =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft x) n b := by
  rw [SingularChains.pointChain, SingularHomology.crossProductZeroLeft_simplex_left,
    SingularHomology.zeroSimplexValue_const]

/-- The pushforward of the point chain at `x` along `f` is the point chain at `f x`. -/
theorem SingularChains.inducedChain_pointChain {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    SingularChains.inducedChain f 0 (SingularChains.pointChain x) =
      SingularChains.pointChain (f x) := by
  simp [SingularChains.pointChain, SingularChains.inducedChain_simplex, ContinuousMap.const_comp]

/-- The point chain at `x ∈ U` is supported on `U`. -/
theorem SingularChains.pointChain_mem_supported {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) (hx : x ∈ U) :
    SingularChains.pointChain x ∈ SingularMayerVietoris.supportedChainSubmodule U 0 := by
  apply SingularMayerVietoris.simplexChain_mem_supported
  rintro y ⟨s, rfl⟩
  simpa [ContinuousMap.const_apply] using hx

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of the fundamental `(n+1)`-cube is supported on the cube boundary. -/
theorem Hurewicz.fundamentalCubeChain_boundary_supported :
    ∀ n : ℕ,
      ((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
          (Hurewicz.fundamentalCubeChain (n + 1)) ∈
        SingularMayerVietoris.supportedChainSubmodule (Cube.boundary (Fin (n + 1))) n
  | 0 => by
    have hfun :
        Hurewicz.fundamentalCubeChain 1 =
          SingularChains.inducedChain
            ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
              Fin 1 → (unitInterval))) 1 Hurewicz.DegreeTwo.intervalChain :=
      rfl
    rw [hfun, ← SingularChains.inducedChain_boundary, Hurewicz.DegreeTwo.intervalChain_boundary,
      map_sub, SingularChains.inducedChain_pointChain, SingularChains.inducedChain_pointChain]
    apply Submodule.sub_mem
    · apply SingularChains.pointChain_mem_supported
      refine ⟨0, Or.inr ?_⟩
      simp [Homeomorph.funUnique]
    · apply SingularChains.pointChain_mem_supported
      refine ⟨0, Or.inl ?_⟩
      simp [Homeomorph.funUnique]
  | n + 1 => by
    have ih := Hurewicz.fundamentalCubeChain_boundary_supported n
    rw [Hurewicz.fundamentalCubeChain_succ, ← SingularChains.inducedChain_boundary,
      SingularHomology.crossProductEdge_boundary n Hurewicz.DegreeTwo.intervalChain
        (Hurewicz.fundamentalCubeChain (n + 1)), map_sub]
    apply Submodule.sub_mem
    · have hd : ((SingularChains.singularComplex (unitInterval)).d 1 0).hom
          Hurewicz.DegreeTwo.intervalChain =
        SingularChains.pointChain (1 : (unitInterval)) -
          SingularChains.pointChain (0 : (unitInterval)) :=
        Hurewicz.DegreeTwo.intervalChain_boundary
      rw [hd, map_sub, LinearMap.sub_apply, SingularHomology.crossProductZeroLeft_pointChain,
        SingularHomology.crossProductZeroLeft_pointChain, map_sub]
      apply Submodule.sub_mem
      · rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
        apply SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo
        intro u
        exact Hurewicz.cubeCoordinates_boundary_left (n + 1) 1 u (Or.inr rfl)
      · rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
        apply SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo
        intro u
        exact Hurewicz.cubeCoordinates_boundary_left (n + 1) 0 u (Or.inl rfl)
    · rw [← SingularMayerVietoris.subtypeInclusion_chain_range
          (Cube.boundary (Fin (n + 1))) n] at ih
      obtain ⟨c, hc⟩ := ih
      rw [← hc]
      have hinterval : Hurewicz.DegreeTwo.intervalChain =
          SingularChains.inducedChain (ContinuousMap.id (unitInterval)) 1
            Hurewicz.DegreeTwo.intervalChain := by
        rw [SingularChains.inducedChain_id, LinearMap.id_apply]
      rw [hinterval, ← SingularHomology.crossProductEdge_natural
          (ContinuousMap.id (unitInterval))
          (SingularMayerVietoris.subtypeInclusion (Cube.boundary (Fin (n + 1)))) n
          Hurewicz.DegreeTwo.intervalChain c, ← LinearMap.comp_apply,
        ← SingularChains.inducedChain_comp]
      apply SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo
      intro z
      exact Hurewicz.cubeCoordinates_boundary_right (n + 1) z.1 z.2.property

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The extra term of the `transAt 0` cube-chain difference is a multiple of the constant
simplex: concatenation is based on the remaining boundary, and `d(fund)` is supported
there. -/
theorem Hurewicz.cubeChain_transAt_zero_extra_eq_smul {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    ∃ k : ℤ,
      SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))) (n + 2)
        (SingularHomology.crossProductTriangle (unitInterval)
          (Fin (n + 1) → (unitInterval)) n
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight)
          (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
            (Hurewicz.fundamentalCubeChain (n + 1)))) =
        k • SingularChains.simplexChain X (n + 2)
          (ContinuousMap.const (SingularChains.Simplex (n + 2)) x) := by
  have hsup := Hurewicz.fundamentalCubeChain_boundary_supported n
  rw [← SingularMayerVietoris.subtypeInclusion_chain_range (Cube.boundary (Fin (n + 1))) n]
    at hsup
  obtain ⟨c, hc⟩ := hsup
  have hconcat :
      SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight =
        SingularChains.inducedChain (ContinuousMap.id (unitInterval)) 2
          (SingularChains.concatChain Hurewicz.intervalPathLeft
            Hurewicz.intervalPathRight) := by
    rw [SingularChains.inducedChain_id, LinearMap.id_apply]
  have hconst :
      ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (Hurewicz.cubeCoordinates (n + 1))).comp
          ((ContinuousMap.id (unitInterval)).prodMap
            (SingularMayerVietoris.subtypeInclusion (Cube.boundary (Fin (n + 1))))) =
        ContinuousMap.const
          ((unitInterval) × Cube.boundary (Fin (n + 1))) x := by
    apply ContinuousMap.ext
    intro z
    exact Hurewicz.transAt_cubeCoordinates_of_mem_boundary p q z.1 z.2.property
  refine ⟨Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation
      ((unitInterval) × Cube.boundary (Fin (n + 1))) (n + 2)
      (SingularHomology.crossProductTriangle (unitInterval)
        (Cube.boundary (Fin (n + 1))) n
        (SingularChains.concatChain Hurewicz.intervalPathLeft
          Hurewicz.intervalPathRight) c), ?_⟩
  rw [← hc, hconcat, ← SingularHomology.crossProductTriangle_natural
      (ContinuousMap.id (unitInterval))
      (SingularMayerVietoris.subtypeInclusion (Cube.boundary (Fin (n + 1)))) n
      (SingularChains.concatChain Hurewicz.intervalPathLeft
        Hurewicz.intervalPathRight) c, ← LinearMap.comp_apply,
    ← SingularChains.inducedChain_comp, hconst, SingularChains.inducedChain_const, ← hconcat]

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
degree `k + 3`, through the prism realization (textbook §10.3). -/
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
`[Π n] = Σ_σ sign(σ)·σ_e` of the lane's textbook (§9, L5), proved by induction through the
prism realization (§10.3). -/
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
/-- The face trichotomy for sums over `Fin (m + 3)`: the zeroth face, the interior faces
`j.succ.castSucc`, and the last face. -/
theorem Hurewicz.CubeTriangulation.sum_face_trichotomy {m : ℕ} {A : Type*}
    [AddCommGroup A] (f : Fin (m + 3) → A) :
    (∑ i : Fin (m + 3), f i) =
      f 0 + (∑ j : Fin (m + 1), f j.succ.castSucc) + f (Fin.last (m + 2)) := by
  calc (∑ i : Fin (m + 3), f i) = f 0 + ∑ i : Fin (m + 2), f i.succ :=
    Fin.sum_univ_succ f
  _ = f 0 + (∑ i : Fin (m + 1), f (i.castSucc).succ + f ((Fin.last (m + 1)).succ)) := by
    rw [Fin.sum_univ_castSucc]
  _ = (f 0 + ∑ i : Fin (m + 1), f i.succ.castSucc) + f (Fin.last (m + 2)) := by
    rw [show (Fin.last (m + 1)).succ = Fin.last (m + 2) from Fin.ext rfl]
    rw [← add_assoc]
    congr 1

/-- The chamber-face sum with alternating signs vanishes: the interior faces cancel in pairs
by the transposition gluing of the Kuhn triangulation, and the two boundary-face
contributions are constant over the chambers with vanishing total orientation. This is the
combinatorial core of "the cube chain of a loop is a cycle" and of the evaluation-cancel
lemmas (textbook §9). -/
theorem Hurewicz.CubeTriangulation.sum_cubeOrientation_faces {m : ℕ} {A : Type*}
    [AddCommGroup A]
    (T : Equiv.Perm (Fin (m + 2)) → Fin (m + 3) → A)
    (hT : ∀ (e : Equiv.Perm (Fin (m + 2))) (j : Fin (m + 1)),
      T ((Equiv.swap j.castSucc j.succ).trans e) j.succ.castSucc = T e j.succ.castSucc)
    (C : A) (hC₀ : ∀ e, T e 0 = C) (hC₁ : ∀ e, T e (Fin.last (m + 2)) = C) :
    ∑ e : Equiv.Perm (Fin (m + 2)), Hurewicz.CubeTriangulation.cubeOrientation e •
        (∑ i : Fin (m + 3), (-1 : ℤ) ^ i.val • T e i) = 0 := by
  classical
  have hinner : ∀ e : Equiv.Perm (Fin (m + 2)),
      (∑ i : Fin (m + 3), (-1 : ℤ) ^ i.val • T e i) =
        T e 0 + (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) +
          (-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)) := by
    intro e
    rw [Hurewicz.CubeTriangulation.sum_face_trichotomy
      (f := fun i => (-1 : ℤ) ^ i.val • T e i)]
    simp
  have hmid : ∀ j : Fin (m + 1),
      ∑ e : Equiv.Perm (Fin (m + 2)),
        Hurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc = 0 :=
    fun j =>
    Hurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant
      j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne
      (fun e => T e j.succ.castSucc) (fun e => hT e j)
  have hsum (C' : A) :
      (∑ e : Equiv.Perm (Fin (m + 2)),
          Hurewicz.CubeTriangulation.cubeOrientation e • C') = 0 :=
    Hurewicz.CubeSubdivision.signed_sum_constant_eq_zero C'
  have hmid' :
      (∑ e : Equiv.Perm (Fin (m + 2)), Hurewicz.CubeTriangulation.cubeOrientation e •
          ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) = 0 := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc
      ∑ e : Equiv.Perm (Fin (m + 2)),
            Hurewicz.CubeTriangulation.cubeOrientation e •
              ((-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) =
          ∑ e, ((-1 : ℤ) ^ (j.val + 1)) •
            (Hurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [smul_smul, mul_comm, ← smul_smul]
      _ = ((-1 : ℤ) ^ (j.val + 1)) •
            ∑ e, Hurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc := by
        rw [Finset.smul_sum]
      _ = ((-1 : ℤ) ^ (j.val + 1)) • 0 := by rw [hmid j]
      _ = 0 := smul_zero _
  simp only [hinner]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
          Hurewicz.CubeTriangulation.cubeOrientation e • T e 0) = 0 from by
      simp_rw [hC₀]
      exact hsum C]
  rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
          Hurewicz.CubeTriangulation.cubeOrientation e •
            ((-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)))) = 0 from by
      rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
              Hurewicz.CubeTriangulation.cubeOrientation e •
                ((-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)))) =
            (-1 : ℤ) ^ (m + 2) •
              (∑ e : Equiv.Perm (Fin (m + 2)),
                Hurewicz.CubeTriangulation.cubeOrientation e • C) from by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro e _
          rw [hC₁ e, smul_smul, mul_comm, ← smul_smul]]
      rw [hsum C, smul_zero]]
  rw [hmid']
  simp

/-- The cube chain of a based loop is a cycle: its boundary is the chamber-face sum, which
vanishes by the transposition gluing on interior faces and the loop's boundary constancy on
the outer faces. General-`n` form of the per-degree `boundary*_cubeChain` facts. -/
theorem Hurewicz.cubeChain_boundary {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    ((SingularChains.singularComplex X).d (m + 2) (m + 1)).hom
        (Hurewicz.cubeChain p) = 0 := by
  rw [Hurewicz.cubeChain_eq_sum_simplices, map_sum]
  simp only [map_zsmul, SingularChains.boundary_simplex]
  apply Hurewicz.CubeTriangulation.sum_cubeOrientation_faces
    (C := SingularChains.simplexChain X (m + 1)
      (ContinuousMap.const (SingularChains.Simplex (m + 1)) x))
  · intro e j
    show SingularChains.simplexChain X (m + 1)
        ((p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex
            ((Equiv.swap j.castSucc j.succ).trans e))).comp
          (SingularChains.simplexFace (m + 1) j.succ.castSucc)) = _
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
      ← Hurewicz.CubeTriangulation.cubeSimplex_face_swap]
  · intro e
    apply congrArg (SingularChains.simplexChain X (m + 1))
    apply ContinuousMap.ext
    intro s
    show p.val (Hurewicz.CubeTriangulation.cubeSimplex e
        (SingularChains.simplexFace (m + 1) 0 s)) = x
    exact GenLoop.boundary p _
      (Hurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary e s)
  · intro e
    apply congrArg (SingularChains.simplexChain X (m + 1))
    apply ContinuousMap.ext
    intro s
    show p.val (Hurewicz.CubeTriangulation.cubeSimplex e
        (SingularChains.simplexFace (m + 1) (Fin.last (m + 2)) s)) = x
    exact GenLoop.boundary p _
      (Hurewicz.CubeTriangulation.cubeSimplex_face_last_boundary e s)

/-- The cube cycle of a based loop: the triangulated cube chain, which is a cycle by
`cubeChain_boundary`. -/
def Hurewicz.cubeCycle {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (m + 2) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (m + 2)
    (Hurewicz.cubeChain p) (by
      show ((SingularChains.singularComplex X).d (m + 2) (m + 1)).hom
          (Hurewicz.cubeChain p) = 0
      exact Hurewicz.cubeChain_boundary p)

/-- The underlying chain of `cubeCycle p` is `cubeChain p`. -/
@[simp]
theorem Hurewicz.cubeCycle_val {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    (Hurewicz.cubeCycle p).1 = Hurewicz.cubeChain p :=
  rfl

/-- The cube homology class of a based loop: the class of its cube cycle. This is the
Hurewicz image of the loop's homotopy class. -/
def Hurewicz.cubeHomologyClass {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) : SingularMayerVietoris.SingularHomology X (m + 2) :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (m + 2)
    (Hurewicz.cubeCycle p)

/-- The cube class of the constant loop vanishes: its cube chain is literally zero, the
chamber orientations summing to zero. -/
theorem Hurewicz.cubeHomologyClass_const {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} :
    Hurewicz.cubeHomologyClass (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 := by
  have hconst : ∀ e : Equiv.Perm (Fin (m + 2)),
      (GenLoop.const : GenLoop (Fin (m + 2)) X x).val.comp
          (Hurewicz.CubeTriangulation.cubeSimplex e) =
        ContinuousMap.const (SingularChains.Simplex (m + 2)) x := by
    intro e
    apply ContinuousMap.ext
    intro s
    rfl
  have hchain : Hurewicz.cubeChain (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 := by
    rw [Hurewicz.cubeChain_eq_sum_simplices]
    simp_rw [hconst]
    have h := (map_sum (zmultiplesHom _ (SingularChains.simplexChain X (m + 2)
        (ContinuousMap.const (SingularChains.Simplex (m + 2)) x)))
      (Hurewicz.CubeTriangulation.cubeOrientation (n := m + 2)) Finset.univ).symm
    rw [Hurewicz.CubeTriangulation.cubeOrientation_sum, map_zero] at h
    exact h
  unfold Hurewicz.cubeHomologyClass
  rw [show Hurewicz.cubeCycle (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 from
    Subtype.ext hchain]
  exact map_zero _


