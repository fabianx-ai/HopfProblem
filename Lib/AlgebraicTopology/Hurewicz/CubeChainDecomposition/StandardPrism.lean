/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization

/-!
# The standard prism and the vanishing on bad terms

The formal edge cross product `Δ¹ × Δ^q` of the universal edge with the universal simplex
differs from the *standard prism* `standardPrism q v w` — the signed sum of the `q + 1`
shuffle simplices `shufflePrismVertices v w i` — by the *prism discrepancy*
`prismDiscrepancy q v w`. The discrepancy is natural in the vertices, so it is the image
of the canonical one `canonicalPrismDiscrepancy q`, and the canonical discrepancy is a
bad-prism chain (`canonicalPrismDiscrepancy_mem_badPrism`): by the recursion
`prismDiscrepancy_succ` it is built from cones at time `0` and edge cross products with
chains omitting a nonzero index.

For a based cube `p : GenLoop (Fin (n + 2)) X x` the oriented prism realization kills every
bad-prism generator: at time `0` the prism simplex lies on the cube boundary
(`orientedPrismRealization_left_zero`), a generator omitting the last Kuhn index lies on
the boundary face (`orientedPrismRealization_last_omitted`), and a generator omitting an
interior index is invariant under an adjacent transposition of `e`, so its signed sum
cancels (`orientedPrismRealization_interior_omitted`). Hence the realizations of the edge
cross product and of the standard prism agree (`orientedPrismRealization_edge_eq_standard`),
and the oriented realization is the signed sum of the realizations at each `e`
(`orientedPrismRealization_eq_sum`).

The shuffle decomposition of `Δ¹ × Δ^q` into `q + 1` simplices is the one of the prism
operator (Hatcher, *Algebraic Topology*, proof of Theorem 2.10); the cross-product
convention is that of Hatcher §3.B.

## Main definitions

* `Hurewicz.CubeSubdivision.retainedFirstBoundary`
* `Hurewicz.CubeSubdivision.shufflePrismVertices`, `Hurewicz.CubeSubdivision.standardPrism`
* `Hurewicz.CubeSubdivision.prismDiscrepancy`, `Hurewicz.CubeSubdivision.canonicalPrismDiscrepancy`

## Main results

* `Hurewicz.CubeSubdivision.canonicalPrismDiscrepancy_mem_badPrism`
* `Hurewicz.CubeSubdivision.badPrism_le_ker_orientedPrismRealization`
* `Hurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard`
* `Hurewicz.CubeSubdivision.orientedPrismRealization_eq_sum`
-/

open Set Function Topology

noncomputable section

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

/-- Scalar multiplication of a `ℤ`-linear map acts pointwise: `(r • f) a = r • f a`. -/
private theorem Hurewicz.CubeSubdivision.linearMap_zsmul_apply {M N : Type*}
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
      linearMap_zsmul_apply, prismCubeRealization_simplex]
  simpa only [LinearMap.sum_apply, linearMap_zsmul_apply] using
    LinearMap.congr_fun h c
