/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
-- Reference copy of Mathlib PR fabianx-ai/mathlib4#4 (branch first-hurewicz-structure-v2, commit d9dafd54). Kept verbatim except for import paths.
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Analysis.Convex.Contractible

/-!
# Standard simplices, paths, and homotopy squares

Topological groundwork for the degree-one Hurewicz theorem: the standard
`n`-simplex and its faces, paths as singular one-simplices, the triangle
witnessing path concatenation, the unit square of a path homotopy cut into two
triangles, and the fact that the edges of any continuous triangle compose up to
path homotopy (the standard 2-simplex is simply connected).

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], proof of Theorem 2A.1: the constant
  2-simplex whose boundary is a constant edge (fact (i)), the square of a path homotopy cut
  into two singular 2-simplices along its diagonal (fact (ii)), and the 2-simplex whose
  three faces are `q`, `p·q`, `p` (fact (iii)). The nullhomotopy of the boundary loop of a
  singular 2-simplex used at the end of Hatcher's proof is `triangleEdges_homotopic`.
-/

open Set Function Topology
open scoped CategoryTheory ContinuousMap

@[expose] public noncomputable section

namespace AlgebraicTopology.Hurewicz

variable {X : Type*} [TopologicalSpace X]

/-! ### The standard simplex and its faces -/

/-- The standard topological `n`-simplex, realized as `stdSimplex ℝ (Fin (n + 1))`. -/
abbrev Simplex (n : ℕ) :=
  stdSimplex ℝ (Fin (n + 1))

/-- The `i`-th face inclusion of the standard `n`-simplex into the `(n + 1)`-simplex,
the topological realization of the simplicial face map `SimplexCategory.δ i`. -/
def simplexFace (n : ℕ) (i : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

/-- The face inclusion is `stdSimplex.map` along `Fin.succAbove`. -/
theorem simplexFace_apply (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s = stdSimplex.map i.succAbove s :=
  rfl

/-- The `i`-th barycentric coordinate on the standard `n`-simplex, as a continuous map to
the unit interval. -/
def simplexCoordinate (n : ℕ) (i : Fin (n + 1)) : C(Simplex n, unitInterval) where
  toFun s := ⟨s i, stdSimplex.zero_le s i, stdSimplex.le_one s i⟩
  continuous_toFun := ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- The `i`-th barycentric coordinate vanishes on the `i`-th face. -/
@[simp]
theorem simplexFace_apply_self (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact absurd (Finset.mem_filter.mp hk).2 (Fin.succAbove_ne i k)

/-- Away from the inserted position, the face inclusion preserves barycentric
coordinates. -/
@[simp]
theorem simplexFace_apply_succAbove (n : ℕ) (i : Fin (n + 2)) (s : Simplex n)
    (k : Fin (n + 1)) : simplexFace n i s (i.succAbove k) = s k := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) (i.succAbove k) = s k
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

/-- The zeroth face of the standard 2-simplex, in explicit coordinates. -/
theorem simplexFace_one_zero (s : Simplex 1) :
    (simplexFace 1 0 s : Fin 3 → ℝ) = ![0, s 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_self 1 0 s
  · exact simplexFace_apply_succAbove 1 0 s 0
  · exact simplexFace_apply_succAbove 1 0 s 1

/-- The first face of the standard 2-simplex, in explicit coordinates. -/
theorem simplexFace_one_one (s : Simplex 1) : (simplexFace 1 1 s : Fin 3 → ℝ) = ![s 0, 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 1 s 0
  · exact simplexFace_apply_self 1 1 s
  · exact simplexFace_apply_succAbove 1 1 s 1

/-- The second face of the standard 2-simplex, in explicit coordinates. -/
theorem simplexFace_one_two (s : Simplex 1) : (simplexFace 1 2 s : Fin 3 → ℝ) = ![s 0, s 1, 0] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 2 s 0
  · exact simplexFace_apply_succAbove 1 2 s 1
  · exact simplexFace_apply_self 1 2 s

/-- The standard 0-simplex is a single vertex. -/
theorem simplexZero_eq_vertex (s : Simplex 0) : s = stdSimplex.vertex (S := ℝ) (0 : Fin 1) := by
  have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  apply Subtype.ext
  funext k
  fin_cases k
  change s 0 = 1
  exact stdSimplex.eq_one_of_unique (s : stdSimplex ℝ (Fin 1)) (0 : Fin 1)

/-- The zeroth face of the standard 1-simplex is its second vertex. -/
@[simp]
theorem simplexFace_zero_zero (s : Simplex 0) :
    simplexFace 0 0 s = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_apply, stdSimplex.map_vertex]
  rfl

/-- The first face of the standard 1-simplex is its first vertex. -/
@[simp]
theorem simplexFace_zero_one (s : Simplex 0) :
    simplexFace 0 1 s = stdSimplex.vertex (S := ℝ) (0 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_apply, stdSimplex.map_vertex]
  rfl

/-! ### Paths as singular one-simplices -/

/-- A path in `X`, viewed as a singular one-simplex through the homeomorphism between the
standard 1-simplex and the unit interval. -/
def pathSimplex {x y : X} (p : Path x y) : C(Simplex 1, X) :=
  p.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- A path's one-simplex sends the first vertex to the path's source. -/
@[simp]
theorem pathSimplex_vertex_zero {x y : X}
    (p : Path x y) : pathSimplex p (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change p (stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero, p.source]

/-- A path's one-simplex sends the second vertex to the path's target. -/
@[simp]
theorem pathSimplex_vertex_one {x y : X}
    (p : Path x y) : pathSimplex p (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = y := by
  change p (stdSimplexHomeomorphUnitInterval _) = y
  rw [stdSimplexHomeomorphUnitInterval_one, p.target]

/-- The zeroth face of a path's one-simplex is the constant simplex at the target. -/
@[simp]
theorem pathSimplex_face_zero {x y : X} (p : Path x y) :
    (pathSimplex p).comp (simplexFace 0 0) = ContinuousMap.const (Simplex 0) y := by
  ext s
  change pathSimplex p (simplexFace 0 0 s) = y
  rw [simplexFace_zero_zero, pathSimplex_vertex_one]

/-- The first face of a path's one-simplex is the constant simplex at the source. -/
@[simp]
theorem pathSimplex_face_one {x y : X} (p : Path x y) :
    (pathSimplex p).comp (simplexFace 0 1) = ContinuousMap.const (Simplex 0) x := by
  ext s
  change pathSimplex p (simplexFace 0 1 s) = x
  rw [simplexFace_zero_one, pathSimplex_vertex_zero]

/-- The path traced by a singular one-simplex, from its first to its second vertex. -/
def simplexPath (σ : C(Simplex 1, X)) : Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) where
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

/-- Tracing the path of a one-simplex and forming its one-simplex again recovers the
simplex. -/
@[simp]
theorem pathSimplex_simplexPath (σ : C(Simplex 1, X)) : pathSimplex (simplexPath σ) = σ := by
  ext s
  change σ (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = σ s
  rw [Homeomorph.symm_apply_apply]

/-! ### The concatenation triangle

A path `p : x ⟶ y` and a path `q : y ⟶ z` fit together into one singular two-simplex whose
three faces are `q`, `p.trans q`, and `p`. Its boundary therefore witnesses, on the chain
level, that concatenation is addition. -/

/-- The time reparametrization of the concatenation triangle: barycentric coordinates
`(s₀, s₁, s₂)` are sent to the time `s₁ / 2 + s₂` of the concatenated path. -/
def concatTime : C(Simplex 2, unitInterval) where
  toFun s :=
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

/-- The singular two-simplex witnessing path concatenation: its faces are `q`,
`p.trans q`, and `p` (see `concatSimplex_face_zero/one/two`). -/
def concatSimplex {x y z : X} (p : Path x y) (q : Path y z) : C(Simplex 2, X) :=
  (p.trans q).toContinuousMap.comp concatTime

/-- The concatenation triangle evaluates the concatenated path at time `s 1 / 2 + s 2`. -/
theorem concatSimplex_apply {x y z : X} (p : Path x y) (q : Path y z) (s : Simplex 2) :
    concatSimplex p q s = (p.trans q).extend (s 1 / 2 + s 2) :=
  (Path.extend_apply (p.trans q) (concatTime s).property).symm

/-- The zeroth face of the concatenation triangle is the second path. -/
@[simp]
theorem concatSimplex_face_zero {x y z : X}
    (p : Path x y) (q : Path y z) : (concatSimplex p q).comp (simplexFace 1 0) = pathSimplex q := by
  ext s
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

/-- The first face of the concatenation triangle is the concatenated path. -/
@[simp]
theorem concatSimplex_face_one {x y z : X} (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 1) = pathSimplex (p.trans q) := by
  ext s
  change concatSimplex p q (simplexFace 1 1 s) = pathSimplex (p.trans q) s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h2 : simplexFace 1 1 s 2 = s 1 := simplexFace_apply_succAbove 1 1 s 1
  rw [h2, zero_div, zero_add]
  exact Path.extend_apply (p.trans q) (simplexCoordinate 1 1 s).property

/-- The second face of the concatenation triangle is the first path. -/
@[simp]
theorem concatSimplex_face_two {x y z : X}
    (p : Path x y) (q : Path y z) : (concatSimplex p q).comp (simplexFace 1 2) = pathSimplex p := by
  ext s
  change concatSimplex p q (simplexFace 1 2 s) = pathSimplex p s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h1 : simplexFace 1 2 s 1 = s 1 := simplexFace_apply_succAbove 1 2 s 1
  rw [h1, add_zero]
  have hle := stdSimplex.le_one s 1
  rw [Path.extend_trans_of_le_half p q (show s 1 / 2 ≤ 1 / 2 by linarith)]
  rw [show 2 * (s 1 / 2) = s 1 by ring]
  exact Path.extend_apply p (simplexCoordinate 1 1 s).property

/-! ### The homotopy square, cut into two triangles

A path homotopy is a map on the unit square. Cutting the square along its diagonal produces
two singular two-simplices whose boundaries combine to show that homotopic paths differ by a
boundary. -/

/-- The affine map from the standard 2-simplex onto the lower triangle of the unit
square. -/
def lowerTriangleMap : C(Simplex 2, unitInterval × unitInterval) where
  toFun s := (simplexCoordinate 2 2 s, unitInterval.symm (simplexCoordinate 2 0 s))
  continuous_toFun :=
    (simplexCoordinate 2 2).continuous.prodMk
      (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous)

/-- The affine map from the standard 2-simplex onto the upper triangle of the unit
square. -/
def upperTriangleMap : C(Simplex 2, unitInterval × unitInterval) where
  toFun s := (unitInterval.symm (simplexCoordinate 2 0 s), simplexCoordinate 2 2 s)
  continuous_toFun :=
    (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous).prodMk
      (simplexCoordinate 2 2).continuous

/-- The zeroth face of the lower triangle lies on the edge `t = 1` of the square. -/
theorem lowerTriangle_face_zero (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 0 s) = (simplexCoordinate 1 1 s, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring

/-- The first face of the lower triangle is the diagonal of the square. -/
theorem lowerTriangle_face_one (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 1 s) = (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

/-- The second face of the lower triangle lies on the edge `s = 0` of the square. -/
theorem lowerTriangle_face_two (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 2 s) = (0, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

/-- The zeroth face of the upper triangle lies on the edge `s = 1` of the square. -/
theorem upperTriangle_face_zero (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 0 s) = (1, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2

/-- The first face of the upper triangle is the diagonal of the square. -/
theorem upperTriangle_face_one (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 1 s) = (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2

/-- The second face of the upper triangle lies on the edge `t = 0` of the square. -/
theorem upperTriangle_face_two (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 2 s) = (simplexCoordinate 1 1 s, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s

/-- The restriction of a path homotopy to the lower triangle of its square, as a singular
two-simplex. -/
def homotopyLowerSimplex {x y : X} {p q : Path x y} (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp lowerTriangleMap

/-- The restriction of a path homotopy to the upper triangle of its square, as a singular
two-simplex. -/
def homotopyUpperSimplex {x y : X} {p q : Path x y} (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp upperTriangleMap

/-- The diagonal of a path homotopy square, as a singular one-simplex. -/
def homotopyDiagonalSimplex {x y : X} {p q : Path x y} (H : p.Homotopy q) : C(Simplex 1, X) where
  toFun s := H (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s)
  continuous_toFun :=
    H.continuous.comp
      ((simplexCoordinate 1 1).continuous.prodMk (simplexCoordinate 1 1).continuous)

/-- The zeroth face of the lower homotopy simplex is constant at the common target. -/
@[simp]
theorem homotopyLowerSimplex_face_zero {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 0) = ContinuousMap.const (Simplex 1) y := by
  ext s
  change H (lowerTriangleMap (simplexFace 1 0 s)) = y
  rw [lowerTriangle_face_zero, H.target]

/-- The first face of the lower homotopy simplex is the diagonal simplex. -/
@[simp]
theorem homotopyLowerSimplex_face_one {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  ext s
  change H (lowerTriangleMap (simplexFace 1 1 s)) = _
  rw [lowerTriangle_face_one]
  rfl

/-- The second face of the lower homotopy simplex is the one-simplex of the first path. -/
@[simp]
theorem homotopyLowerSimplex_face_two {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 2) = pathSimplex p := by
  ext s
  change H (lowerTriangleMap (simplexFace 1 2 s)) = pathSimplex p s
  rw [lowerTriangle_face_two]
  exact H.map_zero_left _

/-- The zeroth face of the upper homotopy simplex is the one-simplex of the second path. -/
@[simp]
theorem homotopyUpperSimplex_face_zero {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 0) = pathSimplex q := by
  ext s
  change H (upperTriangleMap (simplexFace 1 0 s)) = pathSimplex q s
  rw [upperTriangle_face_zero]
  exact H.map_one_left _

/-- The first face of the upper homotopy simplex is the diagonal simplex. -/
@[simp]
theorem homotopyUpperSimplex_face_one {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  ext s
  change H (upperTriangleMap (simplexFace 1 1 s)) = _
  rw [upperTriangle_face_one]
  rfl

/-- The second face of the upper homotopy simplex is constant at the common source. -/
@[simp]
theorem homotopyUpperSimplex_face_two {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 2) = ContinuousMap.const (Simplex 1) x := by
  ext s
  change H (upperTriangleMap (simplexFace 1 2 s)) = x
  rw [upperTriangle_face_two, H.source]

/-- Face inclusions send vertices to vertices along `Fin.succAbove`. -/
@[simp]
theorem simplexFace_vertex (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    simplexFace n i (stdSimplex.vertex (S := ℝ) k) = stdSimplex.vertex (S := ℝ) (i.succAbove k) :=
  by rw [simplexFace_apply, stdSimplex.map_vertex]

/-- The standard `n`-simplex is contractible, being a nonempty convex set. In particular it
is simply connected, which is what `triangleEdges_homotopic` uses. -/
instance (n : ℕ) : ContractibleSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨(stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).val,
      (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).property⟩

/-- The path traced by the `i`-th edge of a continuous triangle, with endpoints normalized
to the triangle's vertices. -/
def triangleFacePath (σ : C(Simplex 2, X)) (i : Fin 3) :
    Path (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2))))
      (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2)))) :=
  (simplexPath (σ.comp (simplexFace 1 i))).cast (congrArg σ (simplexFace_vertex 1 i 0)).symm
    (congrArg σ (simplexFace_vertex 1 i 1)).symm

/-- The edge of a continuous triangle from vertex `0` to vertex `1`. -/
abbrev triangleEdge01 (σ : C(Simplex 2, X)) : Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3))) :=
  triangleFacePath σ 2

/-- The edge of a continuous triangle from vertex `1` to vertex `2`. -/
abbrev triangleEdge12 (σ : C(Simplex 2, X)) : Path (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 0

/-- The edge of a continuous triangle from vertex `0` to vertex `2`. -/
abbrev triangleEdge02 (σ : C(Simplex 2, X)) : Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 1

/-- In any continuous triangle, the edge from `0` to `1` followed by the edge from `1` to
`2` is path-homotopic to the edge from `0` to `2`, because the standard 2-simplex is simply
connected. On the chain level this is why boundaries of two-simplices die in the abelianized
fundamental group. -/
theorem triangleEdges_homotopic (σ : C(Simplex 2, X)) :
    ((triangleEdge01 σ).trans (triangleEdge12 σ)).Homotopic (triangleEdge02 σ) := by
  have h :=
    SimplyConnectedSpace.paths_homotopic
      ((triangleEdge01 (ContinuousMap.id (Simplex 2))).trans
        (triangleEdge12 (ContinuousMap.id (Simplex 2))))
      (triangleEdge02 (ContinuousMap.id (Simplex 2)))
  have hmap := h.map σ
  rw [Path.map_trans] at hmap
  exact hmap

end AlgebraicTopology.Hurewicz
