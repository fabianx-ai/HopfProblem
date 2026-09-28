/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator

/-!
# The prism realization of a based cube

The `(n + 1)`-cube `I × Iⁿ` is triangulated by the prisms `Δ¹ × (Kuhn cell of e)`,
`e : Perm (Fin n)`. A formal chain on the vertex set `Fin 2 × Fin (n + 1)` (a time `0`/`1`
and a Kuhn vertex index) is *realized* in `X` by a map `p : C(I × Iⁿ, X)`:
`Hurewicz.CubeSubdivision.prismCubeRealization p e m` sends a formal `m`-simplex `v` to the
singular simplex `p ∘ prismCubeSimplex e v`, the affine simplex of the cube on the prism
vertices `prismCubeVertex e (v j)`. The *oriented* realization
`orientedPrismRealization p m` is the signed sum over `e` with the orientations
`Hurewicz.CubeTriangulation.cubeOrientation e`.

Two facts are proved here. The realization at `e` of the formal edge cross product of the
interval with a simplex is the pushforward along the prism map `prismCubeMap e` of the
singular edge cross product (`prismCubeRealization_edgeCrossProduct`), so that the
realization is the singular cross product of Hatcher §3.B read on the cube. And the
*bad-prism* submodule `badPrism q m` — the formal chains supported at time `0` or omitting
a nonzero Kuhn index — is stable under the formal cone and under the edge cross product
(`formalCone_mem_badPrism`, `formalEdgeCrossProduct_mem_badPrism_of_omit`); these are the
terms that the oriented realization of a based cube kills.

Signed sums over permutations that are invariant under a transposition vanish
(`signed_sum_eq_zero_of_swap_invariant`); this is the cancellation that underlies both the
vanishing on bad prisms and the cycle property of the cube chain.

The prism decomposition of `Δ¹ × Δⁿ` is the one of the prism operator (Hatcher,
*Algebraic Topology*, proof of Theorem 2.10).

## Main definitions

* `Hurewicz.CubeSubdivision.prismCubeVertex`, `Hurewicz.CubeSubdivision.prismCubeSimplex`,
  `Hurewicz.CubeSubdivision.prismCubeMap`
* `Hurewicz.CubeSubdivision.prismCubeRealization`, `Hurewicz.CubeSubdivision.orientedPrismRealization`
* `Hurewicz.CubeSubdivision.badPrism`

## Main results

* `Hurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct`
* `Hurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant`
* `Hurewicz.CubeSubdivision.formalCone_mem_badPrism`
-/

open Set Function Topology

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
