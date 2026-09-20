/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The singular chain complex and its cycle-class homology

For a topological space `X` (in `Type`, universe 0, wherever singular chains appear), the
singular chain complex with `ℤ` coefficients and its degree-one homology are presented
through explicit singular simplices and explicit cycles:

* `SingularChains.singularComplex (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ` — the singular chain complex;
* `SingularChains.SingularH1 (X : Type) [TopologicalSpace X] := (singularComplex X).homology 1`
  — singular first homology.

A path becomes a singular one-simplex (`pathSimplex`) and a one-simplex becomes a path
(`simplexPath`); the boundary of a simplex is the alternating sum of its faces
(`boundary_simplex`, `boundaryOne_simplex`, `boundaryTwo_simplex`). Homology is handled
through explicit cycle classes: `cycleClass : Cycles1 X →ₗ[ℤ] SingularH1 X` is surjective
with kernel the image of the boundary (`cycleClass_eq_zero_iff` side), and a continuous map
induces chain and homology maps (`inducedChain`, `inducedHomology`, functorial
`inducedChain_id`, `inducedChain_comp`). Every chain is a finite `ℤ`-combination of
simplices (`chainLift`, `chainMap_ext`, `chainBasis`, `chainsEquivFinsupp`).

## Outline of the proof

This is [hatcher02], §2.1, the definitions and the elementary computations behind Theorem 2.10's
setup, in six steps.

1. *Faces of the standard simplex.*  `Simplex n`, `simplexFace n i` (the `i`-th face),
   `simplexCoordinate`; the face identities `simplexFace_one_zero/one_one/one_two` and
   `simplexFace_zero_zero/zero_one`, `simplexZero_eq_vertex`.
2. *Paths and simplices.*  `pathSimplex` turns a path into a one-simplex; `simplexPath`
   inverts it up to the reparametrization `concatTime`; `concatSimplex p q` realizes the
   concatenation `p.trans q` on the two-simplex with its three face identities
   (`concatSimplex_face_zero/one/two`).
3. *The chain complex.*  `singularComplex`, `Chains`, `SingularSimplex`, `simplexIndex`,
   `simplexChain`, `boundaryOne`, `boundaryTwo`; `simplexIndex_face` and `boundary_simplex`
   compute the boundary of a simplex, specialized by `boundaryOne_simplex`,
   `boundaryTwo_simplex`; `chainLift`/`chainLift_simplex`/`chainMap_ext` present chains as
   finite combinations of simplices.
4. *The cycle-class presentation of homology.*  The abstract short-complex API
   `ChainHomology.*` (instantiated at `singularComplex X` by `Cycles1`, `cycleClass`,
   `Opchains`, `chainClass`, `homologyDesc`, `homologyDescOfChain`): `cycleClass` surjective
   with kernel the boundaries; `homologyToChainClass` injective.
5. *Functoriality.*  `singularChainMap`, `inducedChain`, `inducedHomology` with
   `inducedChain_simplex`, `inducedChain_boundary`, `inducedChain_id`, `inducedChain_comp`;
   the finite-support presentation `chainsRepr`, `chainsFromFinsupp`, `chainsEquivFinsupp`,
   `chainBasis`, `simplexChain_span`.
6. *Loops up to homotopy.*  `lowerTriangleMap` and the loop-homotopy two-chains
   (`boundaryTwo_loopHomotopy` etc.): a loop homotopy is a two-chain whose boundary is the
   difference of the loops — the engine behind H₁'s homotopy invariance.

## Main definitions and results

* `SingularChains.singularComplex`, `SingularChains.Chains`, `SingularChains.SingularH1` :
  the chain complex and its first homology.
* `SingularChains.pathSimplex`, `SingularChains.simplexPath`, `SingularChains.concatSimplex` :
  the path/complex dictionary.
* `SingularChains.ChainHomology.*`, `SingularChains.Cycles1`, `SingularChains.cycleClass` :
  the explicit cycle-class presentation of homology.
* `SingularChains.inducedChain`, `SingularChains.inducedHomology` : functoriality.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1

## Tags

singular homology, chain complex, simplex, cycles
-/



open Set Function Filter Manifold Topology

open scoped CategoryTheory

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-- The standard singular `n`-simplex: continuous maps from the model simplex to a space (Hatcher, Algebraic Topology, Section 2.1). -/
abbrev SingularChains.Simplex (n : ℕ) :=
  stdSimplex ℝ (Fin (n + 1))

/-- The `i`-th face inclusion of the model simplex: the affine embedding omitting vertex `i` (Hatcher, Algebraic Topology, Section 2.1). -/
def SingularChains.simplexFace (n : ℕ) (i : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

/-! ### Faces of the standard simplex -/

/-- The `i`-th face map composes with the `succAbove` inclusion. -/
theorem SingularChains.simplexFace_apply (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s = stdSimplex.map i.succAbove s :=
  rfl

/-- The `i`-th barycentric coordinate of the model simplex, as a continuous map into the unit interval. -/
def SingularChains.simplexCoordinate (n : ℕ) (i : Fin (n + 1)) : C(Simplex n, unitInterval)
    where
  toFun s := ⟨s i, stdSimplex.zero_le s i, stdSimplex.le_one s i⟩
  continuous_toFun := ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- The `i`-th face map sends vertex `i` to `0`. -/
@[simp]
theorem SingularChains.simplexFace_apply_self (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact False.elim (Fin.succAbove_ne i k (Finset.mem_filter.mp hk).2)

/-- The `i`-th face map sends `succAbove k` to vertex `k`. -/
@[simp]
theorem SingularChains.simplexFace_apply_succAbove (n : ℕ) (i : Fin (n + 2)) (s : Simplex n)
    (k : Fin (n + 1)) : simplexFace n i s (i.succAbove k) = s k := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) (i.succAbove k) = s k
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

/-- The zeroth face of a 1-simplex inserts `0` first. -/
theorem SingularChains.simplexFace_one_zero (s : Simplex 1) :
    (simplexFace 1 0 s : Fin 3 → ℝ) = ![0, s 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_self 1 0 s
  · exact simplexFace_apply_succAbove 1 0 s 0
  · exact simplexFace_apply_succAbove 1 0 s 1

/-- The first face of a 1-simplex inserts `0` in the middle. -/
theorem SingularChains.simplexFace_one_one (s : Simplex 1) :
    (simplexFace 1 1 s : Fin 3 → ℝ) = ![s 0, 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 1 s 0
  · exact simplexFace_apply_self 1 1 s
  · exact simplexFace_apply_succAbove 1 1 s 1

/-- The second face of a 1-simplex inserts `0` last. -/
theorem SingularChains.simplexFace_one_two (s : Simplex 1) :
    (simplexFace 1 2 s : Fin 3 → ℝ) = ![s 0, s 1, 0] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 2 s 0
  · exact simplexFace_apply_succAbove 1 2 s 1
  · exact simplexFace_apply_self 1 2 s

/-- A 0-simplex is its unique vertex. -/
theorem SingularChains.simplexZero_eq_vertex (s : Simplex 0) :
    s = stdSimplex.vertex (S := ℝ) (0 : Fin 1) := by
  let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  apply Subtype.ext
  funext k
  fin_cases k
  change s 0 = 1
  exact stdSimplex.eq_one_of_unique (s : stdSimplex ℝ (Fin 1)) (0 : Fin 1)

/-- The zeroth face of a 0-simplex is the final vertex. -/
@[simp]
theorem SingularChains.simplexFace_zero_zero (s : Simplex 0) :
    simplexFace 0 0 s = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_apply, stdSimplex.map_vertex]
  rfl

/-- The first face of a 0-simplex is the initial vertex. -/
@[simp]
theorem SingularChains.simplexFace_zero_one (s : Simplex 0) :
    simplexFace 0 1 s = stdSimplex.vertex (S := ℝ) (0 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_apply, stdSimplex.map_vertex]
  rfl

/-- The singular 1-simplex of a path: the affine parametrisation of `Path x y` as a simplex, the bridge between path theory and singular chains. -/
def SingularChains.pathSimplex {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y) :
    C(Simplex 1, X) :=
  p.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The path simplex starts at the path's source. -/
@[simp]
theorem SingularChains.pathSimplex_vertex_zero {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) : pathSimplex p (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change p (stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero, p.source]

/-- The path simplex ends at the path's target. -/
@[simp]
theorem SingularChains.pathSimplex_vertex_one {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) : pathSimplex p (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = y := by
  change p (stdSimplexHomeomorphUnitInterval _) = y
  rw [stdSimplexHomeomorphUnitInterval_one, p.target]

/-- The zeroth face of the path simplex is the constant at `y`. -/
@[simp]
theorem SingularChains.pathSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) : (pathSimplex p).comp (simplexFace 0 0) = ContinuousMap.const (Simplex 0) y :=
  by
  apply ContinuousMap.ext
  intro s
  change pathSimplex p (simplexFace 0 0 s) = y
  rw [simplexFace_zero_zero, pathSimplex_vertex_one]

/-- The first face of the path simplex is the constant at `x`. -/
@[simp]
theorem SingularChains.pathSimplex_face_one {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) : (pathSimplex p).comp (simplexFace 0 1) = ContinuousMap.const (Simplex 0) x :=
  by
  apply ContinuousMap.ext
  intro s
  change pathSimplex p (simplexFace 0 1 s) = x
  rw [simplexFace_zero_one, pathSimplex_vertex_zero]

/-- The path underlying a singular 1-simplex: the inverse bridge from singular chains to path theory. -/
def SingularChains.simplexPath {X : Type*} [TopologicalSpace X] (σ : C(Simplex 1, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)))
    where
  toFun t := σ (stdSimplexHomeomorphUnitInterval.symm t)
  continuous_toFun := σ.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  source' :=
    congrArg σ
      (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
        stdSimplexHomeomorphUnitInterval_zero.symm)
  target' :=
    congrArg σ
      (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
        stdSimplexHomeomorphUnitInterval_one.symm)

/-- A 1-simplex is the path simplex of its edge path. -/
@[simp]
theorem SingularChains.pathSimplex_simplexPath {X : Type*} [TopologicalSpace X]
    (σ : C(Simplex 1, X)) : pathSimplex (simplexPath σ) = σ := by
  apply ContinuousMap.ext
  intro s
  change σ (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = σ s
  rw [Homeomorph.symm_apply_apply]

/-! ### The concatenation 2-simplex -/

/-- The affine time function on the 2-simplex used for concatenation. -/
def SingularChains.concatTime : C(Simplex 2, unitInterval)
    where
  toFun
    s :=
    ⟨s 1 / 2 + s 2, by
      have h0 := stdSimplex.zero_le s 0
      have h1 := stdSimplex.zero_le s 1
      have h2 := stdSimplex.zero_le s 2
      have hs := stdSimplex.sum_eq_one s
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
      change s 0 + (s 1 + s 2) = 1 at hs
      constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val).div_const 2 |>.add
        ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)

/-- The 2-simplex filling the concatenation of two paths. -/
def SingularChains.concatSimplex {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) : C(Simplex 2, X) :=
  (p.trans q).toContinuousMap.comp concatTime

/-- The concatenation simplex evaluates the composite path at `s₁/2 + s₂`. -/
theorem SingularChains.concatSimplex_apply {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) (s : Simplex 2) :
    concatSimplex p q s = (p.trans q).extend (s 1 / 2 + s 2) :=
  (Path.extend_apply (p.trans q) (concatTime s).property).symm

/-- The zeroth face of the concatenation simplex is `q`. -/
@[simp]
theorem SingularChains.concatSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) : (concatSimplex p q).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 0 s) = pathSimplex q s
  rw [concatSimplex_apply]
  have h1 : simplexFace 1 0 s 1 = s 0 := simplexFace_apply_succAbove 1 0 s 0
  have h2 : simplexFace 1 0 s 2 = s 1 := simplexFace_apply_succAbove 1 0 s 1
  rw [h1, h2]
  have hs := stdSimplex.add_eq_one s
  have hnonneg := stdSimplex.zero_le s 1
  rw [Path.extend_trans_of_half_le p q (show 1 / 2 ≤ s 0 / 2 + s 1 by linarith)]
  have he : 2 * (s 0 / 2 + s 1) - 1 = s 1 := by linarith
  rw [he]
  exact Path.extend_apply q (simplexCoordinate 1 1 s).property

/-- The middle face of the concatenation simplex is the composite path. -/
@[simp]
theorem SingularChains.concatSimplex_face_one {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 1) = pathSimplex (p.trans q) := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 1 s) = pathSimplex (p.trans q) s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h2 : simplexFace 1 1 s 2 = s 1 := simplexFace_apply_succAbove 1 1 s 1
  rw [h2, zero_div, zero_add]
  exact Path.extend_apply (p.trans q) (simplexCoordinate 1 1 s).property

/-- The last face of the concatenation simplex is `p`. -/
@[simp]
theorem SingularChains.concatSimplex_face_two {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) : (concatSimplex p q).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 2 s) = pathSimplex p s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h1 : simplexFace 1 2 s 1 = s 1 := simplexFace_apply_succAbove 1 2 s 1
  rw [h1, add_zero]
  have hle := stdSimplex.le_one s 1
  rw [Path.extend_trans_of_le_half p q (show s 1 / 2 ≤ 1 / 2 by linarith)]
  rw [show 2 * (s 1 / 2) = s 1 by ring]
  exact Path.extend_apply p (simplexCoordinate 1 1 s).property

/-- The singular chain complex of a space: the chain complex with `n`-chains the free abelian group on singular `n`-simplices and the alternating boundary operator (Hatcher, Algebraic Topology, Section 2.1). -/
abbrev SingularChains.singularComplex (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)

/-- The group of singular `n`-chains of a space: elements of the degree-`n` group of the singular chain complex, finite `Z`-combinations of singular `n`-simplices. -/
abbrev SingularChains.Chains (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (singularComplex X).X n

/-- The first singular homology `H_1(X)` of a space, as the degree-1 homology of the singular chain complex (Hatcher, Algebraic Topology, Section 2.1). -/
abbrev SingularChains.SingularH1 (X : Type) [TopologicalSpace X] :=
  (singularComplex X).homology 1

/-! ### Singular chains and boundaries -/

/-- A singular `n`-simplex: a continuous map from the standard simplex. -/
abbrev SingularChains.SingularSimplex (X : Type) [TopologicalSpace X] (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X)

/-- A singular simplex as an element of the singular simplicial set. -/
def SingularChains.simplexIndex (X : Type) [TopologicalSpace X] (n : ℕ) (σ : SingularSimplex X n) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n))) :=
  ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n)))).symm σ

/-- A singular simplex as a generator of the chain group. -/
def SingularChains.simplexChain (X : Type) [TopologicalSpace X] (n : ℕ) (σ : SingularSimplex X n) :
    Chains X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) (simplexIndex X n σ)) 1

/-- The boundary map from 1-chains to 0-chains. -/
abbrev SingularChains.boundaryOne (X : Type) [TopologicalSpace X] : Chains X 1 →ₗ[ℤ] Chains X 0 :=
  (singularComplex X).d 1 0 |>.hom

/-- The boundary map from 2-chains to 1-chains. -/
abbrev SingularChains.boundaryTwo (X : Type) [TopologicalSpace X] : Chains X 2 →ₗ[ℤ] Chains X 1 :=
  (singularComplex X).d 2 1 |>.hom

/-- The simplicial face of a simplex index is the face composite. -/
theorem SingularChains.simplexIndex_face (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplexIndex X (n + 1) σ) =
      simplexIndex X n (σ.comp (simplexFace n i)) := by rfl

/-- The boundary of a simplex chain is the alternating sum of its faces. -/
theorem SingularChains.boundary_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X (n + 1)) :
    (singularComplex X).d (n + 1) n (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexChain X n (σ.comp (simplexFace n i)) := by
  have h :=
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d (R := ModuleCat.of ℤ ℤ)
      (simplexIndex X (n + 1) σ)
  let ev : (ModuleCat.of ℤ ℤ ⟶ Chains X n) →+ Chains X n :=
    { toFun := fun f => f.hom 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  rw [map_sum] at he
  simp only [map_zsmul, simplexIndex_face] at he
  exact he

/-- The boundary of a 1-simplex chain is its last vertex minus its first. -/
theorem SingularChains.boundaryOne_simplex (X : Type) [TopologicalSpace X]
    (σ : SingularSimplex X 1) :
    boundaryOne X (simplexChain X 1 σ) =
      simplexChain X 0 (σ.comp (simplexFace 0 0)) - simplexChain X 0 (σ.comp (simplexFace 0 1)) :=
  by simpa [Fin.sum_univ_succ, sub_eq_add_neg] using boundary_simplex X 0 σ

/-- The boundary of a 2-simplex is the alternating sum of its three faces. -/
theorem SingularChains.boundaryTwo_simplex (X : Type) [TopologicalSpace X]
    (σ : SingularSimplex X 2) :
    boundaryTwo X (simplexChain X 2 σ) =
      simplexChain X 1 (σ.comp (simplexFace 1 0)) - simplexChain X 1 (σ.comp (simplexFace 1 1)) +
        simplexChain X 1 (σ.comp (simplexFace 1 2)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using boundary_simplex X 1 σ

/-! ### Extension by simplices -/

/-- A function on simplices extends linearly to chains. -/
def SingularChains.chainLift (X : Type) [TopologicalSpace X] (n : ℕ) {M : Type} [AddCommGroup M]
    [Module ℤ M] (f : SingularSimplex X n → M) : Chains X n →ₗ[ℤ] M :=
  (CategoryTheory.Limits.Sigma.desc
        (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n))) =>
          ModuleCat.ofHom
            (LinearMap.toSpanSingleton ℤ M
              (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) s)))) :
      Chains X n ⟶ ModuleCat.of ℤ M).hom

/-- The chain lift evaluates the function on a simplex. -/
@[simp]
theorem SingularChains.chainLift_simplex (X : Type) [TopologicalSpace X] (n : ℕ) {M : Type}
    [AddCommGroup M] [Module ℤ M] (f : SingularSimplex X n → M) (σ : SingularSimplex X n) :
    chainLift X n f (simplexChain X n σ) = f σ := by
  have h :=
    CategoryTheory.Limits.Sigma.ι_desc
      (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n))) =>
        ModuleCat.ofHom
          (LinearMap.toSpanSingleton ℤ M
            (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) s))))
      (simplexIndex X n σ)
  have he := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M => g.hom 1) h
  change
    chainLift X n f (simplexChain X n σ) =
      (LinearMap.toSpanSingleton ℤ M
          (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) (simplexIndex X n σ))))
        1 at he
  simpa only [LinearMap.toSpanSingleton_apply_one, simplexIndex, Equiv.apply_symm_apply] using he

/-- Chain maps agreeing on all simplices are equal. -/
theorem SingularChains.chainMap_ext (X : Type) [TopologicalSpace X] (n : ℕ) {M : Type}
    [AddCommGroup M] [Module ℤ M] {f g : Chains X n →ₗ[ℤ] M}
    (h : ∀ σ : SingularSimplex X n, f (simplexChain X n σ) = g (simplexChain X n σ)) : f = g := by
  have hcat : (ModuleCat.ofHom f : Chains X n ⟶ ModuleCat.of ℤ M) = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change
      f (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) =
        g (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
    have hs := h ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) s)
    simpa only [simplexChain, simplexIndex, Equiv.symm_apply_apply] using hs
  exact congrArg ModuleCat.Hom.hom hcat

/-! ### Degree-one homology of short complexes -/

/-- The kernel of the last map of a short complex. -/
abbrev SingularChains.ChainHomology.ShortCycle
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) :=
  LinearMap.ker S.g.hom

/-- The module structure on short-complex cycles. -/
@[instance_reducible]
def SingularChains.ChainHomology.shortCycleModule
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) : Module ℤ (ShortCycle S) :=
  (LinearMap.ker S.g.hom).module

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- The boundaries submodule inside the short cycles. -/
abbrev SingularChains.ChainHomology.ShortBoundaries
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) : Submodule ℤ (ShortCycle S) :=
  LinearMap.range S.moduleCatToCycles

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- The homology class of a short cycle. -/
def SingularChains.ChainHomology.shortCycleClass
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) : ShortCycle S →ₗ[ℤ] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (ShortBoundaries S).mkQ

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- Every homology class is a short cycle class. -/
theorem SingularChains.ChainHomology.shortCycleClass_surjective
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) :
    Function.Surjective (shortCycleClass S) :=
  ((ModuleCat.epi_iff_surjective S.moduleCatHomologyIso.inv).mp inferInstance).comp
    (ShortBoundaries S).mkQ_surjective

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- A short cycle class vanishes exactly on boundaries. -/
theorem SingularChains.ChainHomology.shortCycleClass_eq_zero_iff
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) (c : ShortCycle S) :
    shortCycleClass S c = 0 ↔ ∃ b : S.X₁, S.f b = c.1 := by
  have hinj : Function.Injective S.moduleCatHomologyIso.inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro h
    have hq : (Submodule.Quotient.mk c : ShortCycle S ⧸ ShortBoundaries S) = 0 :=
      hinj (h.trans S.moduleCatHomologyIso.inv.hom.map_zero.symm)
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (ShortBoundaries S)).mp hq
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hc : c ∈ ShortBoundaries S := ⟨b, Subtype.ext hb⟩
    have hq := (Submodule.Quotient.mk_eq_zero (ShortBoundaries S)).mpr hc
    exact
      (congrArg S.moduleCatHomologyIso.inv.hom hq).trans S.moduleCatHomologyIso.inv.hom.map_zero

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- The opchains of a short complex. -/
abbrev SingularChains.ChainHomology.ShortOpchains
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) :=
  S.X₂ ⧸ LinearMap.range S.f.hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- The module structure on short opchains. -/
@[instance_reducible]
def SingularChains.ChainHomology.shortOpchainsModule
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) : Module ℤ (ShortOpchains S) :=
  Submodule.Quotient.module (LinearMap.range S.f.hom)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- The map from short-complex homology to opchains. -/
def SingularChains.ChainHomology.shortHomologyToChainClass
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) : S.homology →ₗ[ℤ] ShortOpchains S :=
  (S.homologyι ≫ S.moduleCatOpcyclesIso.hom).hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- Homology embeds into opchains. -/
theorem SingularChains.ChainHomology.shortHomologyToChainClass_injective
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) :
    Function.Injective (shortHomologyToChainClass S) :=
  (ModuleCat.mono_iff_injective (S.homologyι ≫ S.moduleCatOpcyclesIso.hom)).mp inferInstance

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- The embedding sends a cycle class to its chain class. -/
theorem SingularChains.ChainHomology.shortHomologyToChainClass_cycleClass
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ)) (c : ShortCycle S) :
    shortHomologyToChainClass S (shortCycleClass S c) =
      (Submodule.Quotient.mk c.1 : ShortOpchains S) := by
  have hcat :
    S.moduleCatLeftHomologyData.π ≫
        S.moduleCatHomologyIso.inv ≫ S.homologyι ≫ S.moduleCatOpcyclesIso.hom =
      S.moduleCatLeftHomologyData.i ≫ ModuleCat.ofHom (LinearMap.range S.f.hom).mkQ := by
    rw [← S.moduleCatCyclesIso_inv_π_assoc, S.homology_π_ι_assoc,
      S.moduleCatCyclesIso_inv_iCycles_assoc, S.pOpcycles_comp_moduleCatOpcyclesIso_hom]
  exact congrArg (fun f => f.hom c) hcat

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-! ### Degree-one homology of chain complexes -/

/-- The degree-one cycles of a chain complex. -/
abbrev SingularChains.ChainHomology.Cycle1 (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortCycle (K.sc 1)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- The degree-one boundaries inside the cycles. -/
abbrev SingularChains.ChainHomology.Boundaries1 (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    Submodule ℤ (Cycle1 K) :=
  ShortBoundaries (K.sc 1)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- The homology class of a degree-one cycle. -/
def SingularChains.ChainHomology.cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    Cycle1 K →ₗ[ℤ] K.homology 1 :=
  shortCycleClass (K.sc 1)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- Every degree-one homology class is a cycle class. -/
theorem SingularChains.ChainHomology.cycleClass_surjective (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    Function.Surjective (cycleClass K) :=
  shortCycleClass_surjective (K.sc 1)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- A degree-one element with zero boundary is a cycle. -/
def SingularChains.ChainHomology.mkCycle1 (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (z : K.X 1)
    (hz : (K.d 1 0).hom z = 0) : Cycle1 K :=
  ⟨z, by
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom z = 0
    have hn : (ComplexShape.down ℕ).next 1 = 0 := (ComplexShape.down ℕ).next_eq' (by simp)
    rw [hn]
    exact hz⟩

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- A cycle class vanishes exactly when it is a boundary. -/
theorem SingularChains.ChainHomology.cycleClass_eq_zero_iff (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (c : Cycle1 K) : cycleClass K c = 0 ↔ ∃ b : K.X 2, (K.d 2 1).hom b = c.1 := by
  change shortCycleClass (K.sc 1) c = 0 ↔ _
  rw [shortCycleClass_eq_zero_iff]
  change
    (∃ b : K.X ((ComplexShape.down ℕ).prev 1),
        (K.d ((ComplexShape.down ℕ).prev 1) 1).hom b = c.1) ↔
      _
  have hp : (ComplexShape.down ℕ).prev 1 = 2 := (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hp]

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- A degree-two boundary viewed as a degree-one cycle. -/
def SingularChains.ChainHomology.boundaryCycle1 (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (b : K.X 2) : Cycle1 K :=
  mkCycle1 K ((K.d 2 1).hom b) (congrArg (fun f : K.X 2 ⟶ K.X 0 => f.hom b) (K.d_comp_d 2 1 0))

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- Degree-one chains modulo boundaries. -/
abbrev SingularChains.ChainHomology.Opchains (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  K.X 1 ⧸ LinearMap.range (K.d 2 1).hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule in
/-- The module structure on chain-complex opchains. -/
@[instance_reducible]
def SingularChains.ChainHomology.opchainsModule (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    Module ℤ (Opchains K) :=
  Submodule.Quotient.module (LinearMap.range (K.d 2 1).hom)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The opchain class of a degree-one chain. -/
def SingularChains.ChainHomology.chainClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    K.X 1 →ₗ[ℤ] Opchains K :=
  (LinearMap.range (K.d 2 1).hom).mkQ

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The chain class of a boundary is zero. -/
@[simp]
theorem SingularChains.ChainHomology.chainClass_boundary (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (b : K.X 2) : chainClass K ((K.d 2 1).hom b) = 0 :=
  (Submodule.Quotient.mk_eq_zero (LinearMap.range (K.d 2 1).hom)).mpr ⟨b, rfl⟩

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- Two chains have equal classes exactly when they differ by a boundary. -/
theorem SingularChains.ChainHomology.chainClass_eq_iff (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (x y : K.X 1) : chainClass K x = chainClass K y ↔ ∃ b : K.X 2, (K.d 2 1).hom b = x - y :=
  Submodule.Quotient.eq _

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The short-complex map range is the degree-two boundary range. -/
theorem SingularChains.ChainHomology.range_sc_one_f (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    LinearMap.range (K.sc 1).f.hom = LinearMap.range (K.d 2 1).hom := by
  change LinearMap.range (K.d ((ComplexShape.down ℕ).prev 1) 1).hom = _
  have hp : (ComplexShape.down ℕ).prev 1 = 2 := (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hp]

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- Short opchains are linearly equivalent to opchains. -/
def SingularChains.ChainHomology.opchainsEquiv (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    ShortOpchains (K.sc 1) ≃ₗ[ℤ] Opchains K :=
  Submodule.quotEquivOfEq _ _ (range_sc_one_f K)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- Degree-one homology embeds into opchains. -/
def SingularChains.ChainHomology.homologyToChainClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    K.homology 1 →ₗ[ℤ] Opchains K :=
  (opchainsEquiv K).toLinearMap.comp (shortHomologyToChainClass (K.sc 1))

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The homology-to-opchain map is injective. -/
theorem SingularChains.ChainHomology.homologyToChainClass_injective
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) : Function.Injective (homologyToChainClass K) :=
  (opchainsEquiv K).injective.comp (shortHomologyToChainClass_injective (K.sc 1))

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The homology-to-chain map sends a cycle class to its chain class. -/
@[simp]
theorem SingularChains.ChainHomology.homologyToChainClass_cycleClass
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (c : Cycle1 K) :
    homologyToChainClass K (cycleClass K c) = chainClass K c.1 := by
  change opchainsEquiv K (shortHomologyToChainClass (K.sc 1) (shortCycleClass (K.sc 1) c)) = _
  rw [shortHomologyToChainClass_cycleClass]
  rfl

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- A map killing boundaries contains the boundary submodule in its kernel. -/
theorem SingularChains.ChainHomology.boundaries1_le_ker (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M] (f : Cycle1 K →ₗ[ℤ] M)
    (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) : Boundaries1 K ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : cycleClass K c = 0 :=
    (shortCycleClass_eq_zero_iff (K.sc 1) c).mpr ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (cycleClass_eq_zero_iff K c).mp hc
  have he : boundaryCycle1 K b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- A map on cycles killing boundaries descends to homology. -/
def SingularChains.ChainHomology.homologyDesc (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) {M : Type*}
    [AddCommGroup M] [Module ℤ M] (f : Cycle1 K →ₗ[ℤ] M)
    (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) : K.homology 1 →ₗ[ℤ] M :=
  ((Boundaries1 K).liftQ f (boundaries1_le_ker K f hf)).comp (K.sc 1).moduleCatHomologyIso.hom.hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
attribute [local instance] SingularChains.ChainHomology.shortOpchainsModule in
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The descended map computes on cycle classes. -/
@[simp]
theorem SingularChains.ChainHomology.homologyDesc_cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M] (f : Cycle1 K →ₗ[ℤ] M)
    (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) (c : Cycle1 K) :
    homologyDesc K f hf (cycleClass K c) = f c := by
  have h :=
    congrArg (fun q => q.hom (Submodule.Quotient.mk c)) (K.sc 1).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((Boundaries1 K).liftQ f (boundaries1_le_ker K f hf)) h

/-! ### Singular cycles and classes -/

/-- The singular 1-cycles of a space. -/
abbrev SingularChains.Cycles1 (X : Type) [TopologicalSpace X] :=
  ChainHomology.Cycle1 (singularComplex X)

/-- Singular 1-cycles form a `ℤ`-module. -/
instance SingularChains.cycles1Module (X : Type) [TopologicalSpace X] : Module ℤ (Cycles1 X) :=
  ChainHomology.shortCycleModule ((singularComplex X).sc 1)

/-- The underlying chain of a singular cycle. -/
def SingularChains.cycleVal (X : Type) [TopologicalSpace X] : Cycles1 X →ₗ[ℤ] Chains X 1 :=
  (LinearMap.ker ((singularComplex X).sc 1).g.hom).subtype

/-- A 1-chain with zero boundary is a singular cycle. -/
def SingularChains.mkCycle1 (X : Type) [TopologicalSpace X] (c : Chains X 1)
    (hc : boundaryOne X c = 0) : Cycles1 X :=
  ChainHomology.mkCycle1 (singularComplex X) c hc

/-- A singular cycle has zero boundary. -/
theorem SingularChains.cycles1_boundary (X : Type) [TopologicalSpace X] (c : Cycles1 X) :
    boundaryOne X c.1 = 0 := by
  have hc := c.2
  change ((singularComplex X).d 1 ((ComplexShape.down ℕ).next 1)).hom c.1 = 0 at hc
  have hn : (ComplexShape.down ℕ).next 1 = 0 := (ComplexShape.down ℕ).next_eq' (by simp)
  rw [hn] at hc
  exact hc

/-- The homology class of a singular 1-cycle. -/
abbrev SingularChains.cycleClass (X : Type) [TopologicalSpace X] : Cycles1 X →ₗ[ℤ] SingularH1 X :=
  ChainHomology.cycleClass (singularComplex X)

/-- Every first homology class is represented by a cycle. -/
theorem SingularChains.cycleClass_surjective (X : Type) [TopologicalSpace X] :
    Function.Surjective (cycleClass X) :=
  ChainHomology.cycleClass_surjective (singularComplex X)

/-- A 2-chain boundary viewed as a 1-cycle. -/
def SingularChains.boundaryCycle (X : Type) [TopologicalSpace X] (b : Chains X 2) : Cycles1 X :=
  ChainHomology.boundaryCycle1 (singularComplex X) b

/-- Singular 1-chains modulo boundaries. -/
abbrev SingularChains.Opchains (X : Type) [TopologicalSpace X] :=
  ChainHomology.Opchains (singularComplex X)

/-- Singular opchains form a `ℤ`-module. -/
instance SingularChains.opchainsModule (X : Type) [TopologicalSpace X] : Module ℤ (Opchains X) :=
  ChainHomology.opchainsModule (singularComplex X)

/-- The opchain class of a singular 1-chain. -/
abbrev SingularChains.chainClass (X : Type) [TopologicalSpace X] : Chains X 1 →ₗ[ℤ] Opchains X :=
  ChainHomology.chainClass (singularComplex X)

/-- The chain class of a boundary 2-chain is zero. -/
@[simp]
theorem SingularChains.chainClass_boundary (X : Type) [TopologicalSpace X] (b : Chains X 2) :
    chainClass X (boundaryTwo X b) = 0 :=
  ChainHomology.chainClass_boundary (singularComplex X) b

/-- Two chains have equal classes exactly when they differ by a boundary. -/
theorem SingularChains.chainClass_eq_iff (X : Type) [TopologicalSpace X] (x y : Chains X 1) :
    chainClass X x = chainClass X y ↔ ∃ b : Chains X 2, boundaryTwo X b = x - y :=
  ChainHomology.chainClass_eq_iff (singularComplex X) x y

/-- First homology embeds into opchains. -/
abbrev SingularChains.homologyToChainClass (X : Type) [TopologicalSpace X] :
    SingularH1 X →ₗ[ℤ] Opchains X :=
  ChainHomology.homologyToChainClass (singularComplex X)

/-- The homology-to-opchain map is injective. -/
theorem SingularChains.homologyToChainClass_injective (X : Type) [TopologicalSpace X] :
    Function.Injective (homologyToChainClass X) :=
  ChainHomology.homologyToChainClass_injective (singularComplex X)

/-- The homology-to-chain map on a singular cycle class. -/
@[simp]
theorem SingularChains.homologyToChainClass_cycleClass (X : Type) [TopologicalSpace X]
    (c : Cycles1 X) : homologyToChainClass X (cycleClass X c) = chainClass X c.1 :=
  ChainHomology.homologyToChainClass_cycleClass (singularComplex X) c

/-- A map on cycles killing boundaries descends to first homology. -/
def SingularChains.homologyDesc (X : Type) [TopologicalSpace X] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : Cycles1 X →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryCycle X b) = 0) :
    SingularH1 X →ₗ[ℤ] M :=
  ChainHomology.homologyDesc (singularComplex X) f hf

/-- The singular descended map computes on cycle classes. -/
@[simp]
theorem SingularChains.homologyDesc_cycleClass (X : Type) [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (f : Cycles1 X →ₗ[ℤ] M)
    (hf : ∀ b : Chains X 2, f (boundaryCycle X b) = 0) (c : Cycles1 X) :
    homologyDesc X f hf (cycleClass X c) = f c :=
  ChainHomology.homologyDesc_cycleClass (singularComplex X) f hf c

/-- A map on chains killing boundaries descends to first homology. -/
def SingularChains.homologyDescOfChain (X : Type) [TopologicalSpace X] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : Chains X 1 →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryTwo X b) = 0) :
    SingularH1 X →ₗ[ℤ] M :=
  homologyDesc X (f.comp (cycleVal X)) hf

/-- The chain-level descended map computes on cycle classes. -/
@[simp]
theorem SingularChains.homologyDescOfChain_cycleClass (X : Type) [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (f : Chains X 1 →ₗ[ℤ] M)
    (hf : ∀ b : Chains X 2, f (boundaryTwo X b) = 0) (c : Cycles1 X) :
    homologyDescOfChain X f hf (cycleClass X c) = f c.1 :=
  homologyDesc_cycleClass X (f.comp (cycleVal X)) hf c

/-! ### Functoriality -/

/-- The chain map induced by a continuous map. -/
abbrev SingularChains.singularChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : singularComplex X ⟶ singularComplex Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)

/-- The induced map on `n`-chains. -/
abbrev SingularChains.inducedChain {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : Chains X n →ₗ[ℤ] Chains Y n :=
  ((singularChainMap f).f n).hom

/-- The induced map on first homology. -/
abbrev SingularChains.inducedHomology {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : SingularH1 X →ₗ[ℤ] SingularH1 Y :=
  (HomologicalComplex.homologyMap (singularChainMap f) 1).hom

/-- The induced chain map sends each simplex to its composition with `f` (covariance of the singular chain construction). -/
@[simp]
theorem SingularChains.inducedChain_simplex {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (σ : SingularSimplex X n) :
    inducedChain f n (simplexChain X n σ) = simplexChain Y n (f.comp σ) := by
  have h :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) (simplexIndex X n σ)
  have he := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ Chains Y n => g.hom 1) h
  change inducedChain f n (simplexChain X n σ) = simplexChain Y n (f.comp σ) at he
  exact he

/-- The induced chain map commutes with the boundary operator (naturality of the singular chain complex in the space). -/
theorem SingularChains.inducedChain_boundary {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i j : ℕ) (c : Chains X i) :
    inducedChain f j (((singularComplex X).d i j).hom c) =
      ((singularComplex Y).d i j).hom (inducedChain f i c) :=
  congrArg (fun g : Chains X i ⟶ Chains Y j => g.hom c) ((singularChainMap f).comm i j).symm

/-- The chain map induced by the identity is the identity (functoriality). -/
@[simp]
theorem SingularChains.inducedChain_id {X : Type} [TopologicalSpace X] (n : ℕ) :
    inducedChain (ContinuousMap.id X) n = LinearMap.id := by
  apply chainMap_ext X n
  intro σ
  simp only [inducedChain_simplex, LinearMap.id_apply]
  rfl

/-- The chain map induced by a composition is the composition of the induced chain maps (functoriality of singular chains). -/
theorem SingularChains.inducedChain_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    inducedChain (g.comp f) n = (inducedChain g n).comp (inducedChain f n) := by
  apply chainMap_ext X n
  intro σ
  simp only [LinearMap.comp_apply, inducedChain_simplex]
  rfl

/-- The homology map induced by the identity is the identity (functoriality on homology). -/
@[simp]
theorem SingularChains.inducedHomology_id {X : Type} [TopologicalSpace X] :
    inducedHomology (ContinuousMap.id X) = LinearMap.id := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map_id
      (TopCat.of X)
  exact congrArg ModuleCat.Hom.hom h

/-- The homology map induced by a composition is the composition of the induced homology maps (singular homology is a functor). -/
theorem SingularChains.inducedHomology_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    inducedHomology (g.comp f) = (inducedHomology g).comp (inducedHomology f) := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg ModuleCat.Hom.hom h

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- A chain map restricted to the degree-one short complexes. -/
abbrev SingularChains.ChainHomology.shortMap {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (F : K ⟶ L) :
    K.sc 1 ⟶ L.sc 1 :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 1).map F

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- A chain map sends cycles to cycles. -/
def SingularChains.ChainHomology.mapCycles {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (F : K ⟶ L) :
    Cycle1 K →ₗ[ℤ] Cycle1 L :=
  ((K.sc 1).moduleCatCyclesIso.inv ≫
      CategoryTheory.ShortComplex.cyclesMap (shortMap F) ≫ (L.sc 1).moduleCatCyclesIso.hom).hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The mapped cycle's underlying chain. -/
@[simp]
theorem SingularChains.ChainHomology.mapCycles_val {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (F : K ⟶ L) (c : Cycle1 K) : (mapCycles F c).1 = (F.f 1).hom c.1 := by
  have hcat :
    (K.sc 1).moduleCatCyclesIso.inv ≫
        CategoryTheory.ShortComplex.cyclesMap (shortMap F) ≫
          (L.sc 1).moduleCatCyclesIso.hom ≫ (L.sc 1).moduleCatLeftHomologyData.i =
      (K.sc 1).moduleCatLeftHomologyData.i ≫ (shortMap F).τ₂ := by
    rw [(L.sc 1).moduleCatCyclesIso_hom_i, CategoryTheory.ShortComplex.cyclesMap_i,
      (K.sc 1).moduleCatCyclesIso_inv_iCycles_assoc]
  exact congrArg (fun f => f.hom c) hcat

attribute [local instance] SingularChains.ChainHomology.shortCycleModule
attribute [local instance] SingularChains.ChainHomology.shortCycleModule
    SingularChains.ChainHomology.shortOpchainsModule SingularChains.ChainHomology.opchainsModule in
/-- The homology map sends a cycle class to the mapped cycle's class. -/
theorem SingularChains.ChainHomology.homologyMap_cycleClass
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (F : K ⟶ L) (c : Cycle1 K) :
    (HomologicalComplex.homologyMap F 1).hom (cycleClass K c) = cycleClass L (mapCycles F c) := by
  have hcat :
    (K.sc 1).moduleCatLeftHomologyData.π ≫
        (K.sc 1).moduleCatHomologyIso.inv ≫ CategoryTheory.ShortComplex.homologyMap (shortMap F) =
      ((K.sc 1).moduleCatCyclesIso.inv ≫
          CategoryTheory.ShortComplex.cyclesMap (shortMap F) ≫ (L.sc 1).moduleCatCyclesIso.hom) ≫
        (L.sc 1).moduleCatLeftHomologyData.π ≫ (L.sc 1).moduleCatHomologyIso.inv := by
    simp only [CategoryTheory.Category.assoc, ← (K.sc 1).moduleCatCyclesIso_inv_π_assoc,
      ← (L.sc 1).moduleCatCyclesIso_inv_π, CategoryTheory.Iso.hom_inv_id_assoc]
    rw [CategoryTheory.ShortComplex.homologyπ_naturality]
  exact congrArg (fun f => f.hom c) hcat

/-- A continuous map sends singular cycles to cycles. -/
def SingularChains.inducedCycles {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Cycles1 X →ₗ[ℤ] Cycles1 Y :=
  ChainHomology.mapCycles (singularChainMap f)

/-- The induced cycle's underlying chain. -/
@[simp]
theorem SingularChains.inducedCycles_val {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (c : Cycles1 X) : (inducedCycles f c).1 = inducedChain f 1 c.1 :=
  ChainHomology.mapCycles_val (singularChainMap f) c

/-- The induced homology map sends cycle classes to cycle classes. -/
@[simp]
theorem SingularChains.inducedHomology_cycleClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : Cycles1 X) :
    inducedHomology f (cycleClass X c) = cycleClass Y (inducedCycles f c) :=
  ChainHomology.homologyMap_cycleClass (singularChainMap f) c

/-! ### The simplex basis of chains -/

/-- The finsupp representation of a chain on the simplex basis. -/
def SingularChains.chainsRepr (X : Type) [TopologicalSpace X] (n : ℕ) :
    Chains X n →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  chainLift X n (fun σ => Finsupp.single σ 1)

/-- A simplex chain represents as the single finsupp. -/
@[simp]
theorem SingularChains.chainsRepr_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X n) : chainsRepr X n (simplexChain X n σ) = Finsupp.single σ 1 :=
  chainLift_simplex X n _ σ

/-- A finsupp of simplices assembled into a chain. -/
def SingularChains.chainsFromFinsupp (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularSimplex X n →₀ ℤ) →ₗ[ℤ] Chains X n :=
  Finsupp.linearCombination ℤ (simplexChain X n)

/-- A single finsupp builds the scaled simplex chain. -/
@[simp]
theorem SingularChains.chainsFromFinsupp_single (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X n) (a : ℤ) :
    chainsFromFinsupp X n (Finsupp.single σ a) = a • simplexChain X n σ :=
  (Finsupp.linearCombination_single ℤ (v := simplexChain X n) a σ).trans
    (int_smul_eq_zsmul (Chains X n).isModule a (simplexChain X n σ))

/-- Assembling after representing is the identity. -/
theorem SingularChains.chainsFromFinsupp_comp_repr (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chainsFromFinsupp X n).comp (chainsRepr X n) = LinearMap.id := by
  apply chainMap_ext X n
  intro σ
  simp only [LinearMap.comp_apply, chainsRepr_simplex, chainsFromFinsupp_single, one_smul,
    LinearMap.id_apply]

/-- Representing after assembling is the identity. -/
theorem SingularChains.chainsRepr_comp_fromFinsupp (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chainsRepr X n).comp (chainsFromFinsupp X n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply, chainsFromFinsupp_single, map_zsmul, chainsRepr_simplex,
    Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

/-- Chains are linearly equivalent to finsupported simplex functions. -/
def SingularChains.chainsEquivFinsupp (X : Type) [TopologicalSpace X] (n : ℕ) :
    Chains X n ≃ₗ[ℤ] (SingularSimplex X n →₀ ℤ)
    where
  toLinearMap := chainsRepr X n
  invFun := chainsFromFinsupp X n
  left_inv c := LinearMap.congr_fun (chainsFromFinsupp_comp_repr X n) c
  right_inv c := LinearMap.congr_fun (chainsRepr_comp_fromFinsupp X n) c

/-- The simplex basis of the chain group. -/
def SingularChains.chainBasis (X : Type) [TopologicalSpace X] (n : ℕ) :
    Module.Basis (SingularSimplex X n) ℤ (Chains X n) :=
  Module.Basis.ofRepr (chainsEquivFinsupp X n)

/-- The chain basis representation is the finsupp equivalence. -/
@[simp]
theorem SingularChains.chainBasis_repr (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chainBasis X n).repr = chainsEquivFinsupp X n :=
  rfl

/-- The chain basis sends a simplex to its chain. -/
@[simp]
theorem SingularChains.chainBasis_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X n) : chainBasis X n σ = simplexChain X n σ := by
  change chainsFromFinsupp X n (Finsupp.single σ 1) = _
  rw [chainsFromFinsupp_single, one_smul]

/-- The basis coerces to the simplex chain map. -/
theorem SingularChains.chainBasis_coe (X : Type) [TopologicalSpace X] (n : ℕ) :
    ⇑(chainBasis X n) = simplexChain X n :=
  funext (chainBasis_apply X n)

/-- Simplex chains span the chain group. -/
theorem SingularChains.simplexChain_span (X : Type) [TopologicalSpace X] (n : ℕ) :
    Submodule.span ℤ (Set.range (simplexChain X n)) = ⊤ := by
  simpa only [chainBasis_coe] using (chainBasis X n).span_eq

/-- A chain lies in a simplex span exactly when its support does. -/
theorem SingularChains.mem_simplex_span_iff (X : Type) [TopologicalSpace X] (n : ℕ)
    (S : Set (SingularSimplex X n)) (c : Chains X n) :
    c ∈ Submodule.span ℤ (simplexChain X n '' S) ↔ ↑(chainsEquivFinsupp X n c).support ⊆ S := by
  simpa only [chainBasis_coe, chainBasis_repr] using
    (chainBasis X n).mem_span_image (m := c) (s := S)

/-- Intersections of simplex spans are the span of the intersection. -/
theorem SingularChains.simplex_span_inter (X : Type) [TopologicalSpace X] (n : ℕ)
    (S T : Set (SingularSimplex X n)) :
    Submodule.span ℤ (simplexChain X n '' S) ⊓ Submodule.span ℤ (simplexChain X n '' T) =
      Submodule.span ℤ (simplexChain X n '' (S ∩ T)) := by
  ext c
  simp only [Submodule.mem_inf, mem_simplex_span_iff, Set.subset_inter_iff]

/-! ### The homotopy 2-simplices -/

/-- The lower triangle parametrization of the 2-simplex. -/
def SingularChains.lowerTriangleMap : C(Simplex 2, unitInterval × unitInterval)
    where
  toFun s := (simplexCoordinate 2 2 s, unitInterval.symm (simplexCoordinate 2 0 s))
  continuous_toFun :=
    (simplexCoordinate 2 2).continuous.prodMk
      (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous)

/-- The upper triangle parametrization of the 2-simplex. -/
def SingularChains.upperTriangleMap : C(Simplex 2, unitInterval × unitInterval)
    where
  toFun s := (unitInterval.symm (simplexCoordinate 2 0 s), simplexCoordinate 2 2 s)
  continuous_toFun :=
    (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous).prodMk
      (simplexCoordinate 2 2).continuous

/-- The lower triangle's zeroth face. -/
theorem SingularChains.lowerTriangle_face_zero (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 0 s) = (simplexCoordinate 1 1 s, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring

/-- The lower triangle's first face is the diagonal. -/
theorem SingularChains.lowerTriangle_face_one (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 1 s) = (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

/-- The lower triangle's second face. -/
theorem SingularChains.lowerTriangle_face_two (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 2 s) = (0, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

/-- The upper triangle's zeroth face. -/
theorem SingularChains.upperTriangle_face_zero (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 0 s) = (1, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2

/-- The upper triangle's first face is the diagonal. -/
theorem SingularChains.upperTriangle_face_one (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 1 s) = (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2

/-- The upper triangle's second face. -/
theorem SingularChains.upperTriangle_face_two (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 2 s) = (simplexCoordinate 1 1 s, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s

/-- The lower 2-simplex of a path homotopy. -/
def SingularChains.homotopyLowerSimplex {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp lowerTriangleMap

/-- The upper 2-simplex of a path homotopy. -/
def SingularChains.homotopyUpperSimplex {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp upperTriangleMap

/-- The diagonal 1-simplex of a path homotopy. -/
def SingularChains.homotopyDiagonalSimplex {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : C(Simplex 1, X)
    where
  toFun s := H (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s)
  continuous_toFun :=
    H.continuous.comp
      ((simplexCoordinate 1 1).continuous.prodMk (simplexCoordinate 1 1).continuous)

/-- The lower homotopy simplex's zeroth face is constant at `y`. -/
@[simp]
theorem SingularChains.homotopyLowerSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 0) = ContinuousMap.const (Simplex 1) y := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 0 s)) = y
  rw [lowerTriangle_face_zero, H.target]

/-- The lower homotopy simplex's middle face is the diagonal simplex. -/
@[simp]
theorem SingularChains.homotopyLowerSimplex_face_one {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 1 s)) = _
  rw [lowerTriangle_face_one]
  rfl

/-- The lower homotopy simplex's last face is `p`. -/
@[simp]
theorem SingularChains.homotopyLowerSimplex_face_two {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 2 s)) = pathSimplex p s
  rw [lowerTriangle_face_two]
  exact H.map_zero_left _

/-- The upper homotopy simplex's zeroth face is `q`. -/
@[simp]
theorem SingularChains.homotopyUpperSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 0 s)) = pathSimplex q s
  rw [upperTriangle_face_zero]
  exact H.map_one_left _

/-- The upper homotopy simplex's middle face is the diagonal simplex. -/
@[simp]
theorem SingularChains.homotopyUpperSimplex_face_one {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 1 s)) = _
  rw [upperTriangle_face_one]
  rfl

/-- The upper homotopy simplex's last face is constant at `x`. -/
@[simp]
theorem SingularChains.homotopyUpperSimplex_face_two {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 2) = ContinuousMap.const (Simplex 1) x := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 2 s)) = x
  rw [upperTriangle_face_two, H.source]

/-! ### Chains of paths and homotopies -/

/-- The 0-chain of a point. -/
def SingularChains.pointChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 0 :=
  simplexChain X 0 (ContinuousMap.const (Simplex 0) x)

/-- The 1-chain of a path. -/
def SingularChains.pathChain {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    Chains X 1 :=
  simplexChain X 1 (pathSimplex p)

/-- The boundary of a path chain is target minus source. -/
theorem SingularChains.boundaryOne_pathChain {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : boundaryOne X (pathChain p) = pointChain y - pointChain x := by
  rw [pathChain, boundaryOne_simplex, pathSimplex_face_zero, pathSimplex_face_one]
  rfl

/-- The boundary of a loop chain is zero. -/
theorem SingularChains.boundaryOne_loop {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    boundaryOne X (pathChain p) = 0 := by rw [boundaryOne_pathChain, sub_self]

/-- The 2-chain witnessing the boundary of a concatenation. -/
def SingularChains.concatChain {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) : Chains X 2 :=
  simplexChain X 2 (concatSimplex p q)

/-- The concatenation 2-chain has boundary `q - p∘q + p`. -/
theorem SingularChains.boundaryTwo_concatChain {X : Type} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    boundaryTwo X (concatChain p q) = pathChain q - pathChain (p.trans q) + pathChain p := by
  rw [concatChain, boundaryTwo_simplex, concatSimplex_face_zero, concatSimplex_face_one,
    concatSimplex_face_two]
  rfl

/-- The constant 1-chain at a point. -/
def SingularChains.constantEdgeChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 1 :=
  simplexChain X 1 (ContinuousMap.const (Simplex 1) x)

/-- The constant 2-chain at a point. -/
def SingularChains.constantTriangleChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 2 :=
  simplexChain X 2 (ContinuousMap.const (Simplex 2) x)

/-- The constant 2-chain's boundary is the constant edge. -/
theorem SingularChains.boundaryTwo_constantTriangleChain {X : Type} [TopologicalSpace X] (x : X) :
    boundaryTwo X (constantTriangleChain x) = constantEdgeChain x := by
  rw [constantTriangleChain, boundaryTwo_simplex]
  change constantEdgeChain x - constantEdgeChain x + constantEdgeChain x = _
  abel

/-- The chain of the constant path is the constant edge chain. -/
@[simp]
theorem SingularChains.pathChain_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathChain (Path.refl x) = constantEdgeChain x :=
  rfl

/-- The 2-chain of a path homotopy. -/
def SingularChains.homotopyChain {X : Type} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : Chains X 2 :=
  simplexChain X 2 (homotopyLowerSimplex H) - simplexChain X 2 (homotopyUpperSimplex H)

/-- The homotopy chain's boundary is `p - q` plus constant edges. -/
theorem SingularChains.boundaryTwo_homotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) =
      pathChain p - pathChain q + constantEdgeChain y - constantEdgeChain x := by
  rw [homotopyChain, map_sub, boundaryTwo_simplex, boundaryTwo_simplex,
    homotopyLowerSimplex_face_zero, homotopyLowerSimplex_face_one, homotopyLowerSimplex_face_two,
    homotopyUpperSimplex_face_zero, homotopyUpperSimplex_face_one, homotopyUpperSimplex_face_two]
  change
    constantEdgeChain y - simplexChain X 1 (homotopyDiagonalSimplex H) + pathChain p -
        (pathChain q - simplexChain X 1 (homotopyDiagonalSimplex H) + constantEdgeChain x) =
      _
  abel

/-- The homotopy 2-chain corrected to remove the constant edges. -/
def SingularChains.correctedHomotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  homotopyChain H - constantTriangleChain y + constantTriangleChain x

/-- The corrected chain's boundary is exactly `p - q`. -/
theorem SingularChains.boundaryTwo_correctedHomotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (correctedHomotopyChain H) = pathChain p - pathChain q := by
  rw [correctedHomotopyChain, map_add, map_sub, boundaryTwo_homotopyChain,
    boundaryTwo_constantTriangleChain, boundaryTwo_constantTriangleChain]
  abel

/-- A loop homotopy's chain boundary is `p - q`. -/
theorem SingularChains.boundaryTwo_loopHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) = pathChain p - pathChain q := by
  rw [boundaryTwo_homotopyChain]
  abel
