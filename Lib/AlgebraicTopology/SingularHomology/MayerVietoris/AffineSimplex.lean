/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains

/-!
# Affine simplices in the standard simplex

For vertices `v : Fin (n + 1) → Δ^p` in the standard `p`-simplex, `affineSimplex v : C(Δ^n, Δ^p)`
is the affine map in barycentric coordinates, `t ↦ ∑ i, t i • v i`, sending the `i`-th vertex of
`Δ^n` to `v i` (`affineSimplex_vertex`).  The standard vertices `stdVertices n` give the
identity (`affineSimplex_stdVertices`); affine simplices compose by vertex lists
(`affineSimplex_comp`), their faces are the affine simplices on the deleted vertex lists
(`affineSimplex_face`), and their images lie in the convex hull of the vertices
(`affineSimplex_mem_convexHull`).  `simplexBarycenter v` is the barycenter of the affine
simplex, the image of the barycenter of `Δ^n`, with all coordinates averaged
(`simplexBarycenter_coe`).  These are the linear simplices `[v₀, …, vₙ]` of Hatcher,
*Algebraic Topology*, proof of Proposition 2.21.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Affine simplices and the barycenter -/

/-- The affine simplex on a list of vertices. -/
def SingularMayerVietoris.affineSimplex {n p : ℕ} (v : Fin (n + 1) → SingularChains.Simplex p) :
    C(SingularChains.Simplex n, SingularChains.Simplex p)
    where
  toFun
    t :=
    ⟨∑ i, t i • (v i : Fin (p + 1) → ℝ),
      (convex_stdSimplex ℝ (Fin (p + 1))).sum_mem (fun i _ => stdSimplex.zero_le t i)
        (stdSimplex.sum_eq_one t) (fun i _ => (v i).property)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_finsetSum _
        (fun i _ => ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

/-- The affine simplex evaluates the convex combination. -/
@[simp]
theorem SingularMayerVietoris.affineSimplex_coordinate {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (t : SingularChains.Simplex n) (j : Fin (p + 1)) :
    affineSimplex v t j = ∑ i, t i * v i j := by
  change (∑ i, t i • (v i : Fin (p + 1) → ℝ)) j = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The affine simplex at a vertex. -/
@[simp]
theorem SingularMayerVietoris.affineSimplex_vertex {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (i : Fin (n + 1)) :
    affineSimplex v (stdSimplex.vertex (S := ℝ) i) = v i := by
  apply Subtype.ext
  change
    (∑ j : Fin (n + 1), ((Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j) • (v j : Fin (p + 1) → ℝ)) =
      (v i : Fin (p + 1) → ℝ)
  simp [Pi.single_apply]

/-- The standard basis vertices of the simplex. -/
def SingularMayerVietoris.stdVertices (n : ℕ) : Fin (n + 1) → SingularChains.Simplex n :=
  stdSimplex.vertex

/-- The affine simplex on the standard vertices is the identity. -/
@[simp]
theorem SingularMayerVietoris.affineSimplex_stdVertices (n : ℕ) :
    affineSimplex (stdVertices n) = ContinuousMap.id (SingularChains.Simplex n) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext j
  change (∑ i, t i • Pi.single i (1 : ℝ)) j = t j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- The face of an affine simplex is affine on the deleted vertices. -/
theorem SingularMayerVietoris.affineSimplex_face {n p : ℕ}
    (v : Fin (n + 2) → SingularChains.Simplex p) (i : Fin (n + 2)) :
    (affineSimplex v).comp (SingularChains.simplexFace n i) =
      affineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change
    (∑ j : Fin (n + 2), SingularChains.simplexFace n i t j • (v j : Fin (p + 1) → ℝ)) =
      ∑ j : Fin (n + 1), t j • (v (i.succAbove j) : Fin (p + 1) → ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [SingularChains.simplexFace_apply_self, zero_smul,
    SingularChains.simplexFace_apply_succAbove, zero_add]

/-- Affine simplices compose by vertex lists. -/
theorem SingularMayerVietoris.affineSimplex_comp {m n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (w : Fin (m + 1) → SingularChains.Simplex n) :
    (affineSimplex v).comp (affineSimplex w) = affineSimplex (fun j => affineSimplex v (w j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext k
  change
    affineSimplex v (affineSimplex w t) k = affineSimplex (fun j => affineSimplex v (w j)) t k
  simp only [affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The affine simplex lands in the convex hull of its vertices. -/
theorem SingularMayerVietoris.affineSimplex_mem_convexHull {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (t : SingularChains.Simplex n) :
    (affineSimplex v t : Fin (p + 1) → ℝ) ∈
      convexHull ℝ (Set.range fun i => (v i : Fin (p + 1) → ℝ)) := by
  change (∑ i, t i • (v i : Fin (p + 1) → ℝ)) ∈ _
  apply (convex_convexHull ℝ _).sum_mem
  · intro i _
    exact stdSimplex.zero_le t i
  · exact stdSimplex.sum_eq_one t
  · intro i _
    exact subset_convexHull ℝ _ (Set.mem_range_self i)

/-- The barycenter of the standard simplex. -/
def SingularMayerVietoris.simplexBarycenter {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) : SingularChains.Simplex p :=
  affineSimplex v (stdSimplex.barycenter : SingularChains.Simplex n)

/-- The barycenter's coordinates are all `1/(n+1)`. -/
theorem SingularMayerVietoris.simplexBarycenter_coe {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (v i : Fin (p + 1) → ℝ) := by
  change (∑ i, (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ • (v i : Fin (p + 1) → ℝ)) = _
  simp only [Fintype.card_fin, Finset.smul_sum]

/-- The affine simplex sends the barycenter to the vertex average. -/
theorem SingularMayerVietoris.affineSimplex_simplexBarycenter {m n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (w : Fin (m + 1) → SingularChains.Simplex n) :
    affineSimplex v (simplexBarycenter w) = simplexBarycenter (fun j => affineSimplex v (w j)) :=
  ContinuousMap.congr_fun (affineSimplex_comp v w)
    (stdSimplex.barycenter : SingularChains.Simplex m)
