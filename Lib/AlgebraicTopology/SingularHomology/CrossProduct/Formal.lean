/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Multilinear

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Formal cross products of a point, an edge and a triangle with a simplex

The combinatorial core of the singular cross product, on *formal chains* (free abelian groups on
vertex lists `Fin (n + 1) → V`): the triangulations of the prisms `Δ⁰ × Δ^q`, `Δ¹ × Δ^q` and
`Δ² × Δ^q` into affine simplices, built inductively in `q` by coning off the boundary
(`SingularMayerVietoris.formalCone`), as bilinear maps on formal chains

* `SingularHomology.formalPointCrossProduct q : FormalChains V 1 →ₗ FormalChains W (q+1) →ₗ
  FormalChains (V × W) (q+1)`,
* `SingularHomology.formalEdgeCrossProduct q : FormalChains V 2 →ₗ FormalChains W (q+1) →ₗ
  FormalChains (V × W) (q+2)`,
* `SingularHomology.formalTriangleCrossProduct q : FormalChains V 3 →ₗ FormalChains W (q+1) →ₗ
  FormalChains (V × W) (q+3)`,

with the Leibniz boundary laws `SingularHomology.formalBoundary_pointCrossProduct`,
`.formalBoundary_edgeCrossProduct` (`∂(e × c) = ∂e × c - e × ∂c`) and
`.formalBoundary_triangleCrossProduct` (`∂(t × c) = ∂t × c + t × ∂c`), naturality under maps of
the vertex sets (`SingularHomology.formalMap_pointCrossProduct`, `.formalMap_edgeCrossProduct`,
`.formalMap_triangleCrossProduct`), and support bounds
(`SingularHomology.formalPointCrossProduct_mem_supported`, `.formalEdgeCrossProduct_mem_supported`).
The file also records the elementary facts about pushforward of formal chains used downstream
(`SingularHomology.formalMap_comp`, `.formalMap_comp_apply`, `.formalMap_id_apply`,
`.formalMap_prod_swap`).

This is Hatcher's subdivision of `Δᵖ × Δ^q` into `(p+q)`-simplices (Hatcher, *Algebraic
Topology*, §3.B), specialised to `p = 0, 1, 2`; the general shuffle formula is not formalised.
-/


@[expose] public noncomputable section


/-! ### The formal point cross product -/

/-- The bilinear product of a formal point chain and a formal `q`-chain, obtained by
inserting the point as the left coordinate of each vertex. -/
def SingularHomology.formalPointCrossProduct {V W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 1 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
        SingularMayerVietoris.FormalChains (V × W) (q + 1) :=
  SingularMayerVietoris.formalLift fun v =>
    SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1)

/-- On a point generator `v : Fin 1 → V`, the formal point cross product maps `w`
to the formal chain of `(v 0, w)`. -/
@[simp]
theorem SingularHomology.formalPointCrossProduct_simplex_left {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    SingularHomology.formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d =
      SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) d

/-- `formalPointCrossProduct` on generators `v, w` is the formal map of `w ↦ (v 0, w)`. -/
@[simp]
theorem SingularHomology.formalPointCrossProduct_simplex {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (w : Fin (q + 1) → W) :
    SingularHomology.formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (fun i => (v 0, w i)) := by
  rw [SingularHomology.formalPointCrossProduct_simplex_left, SingularMayerVietoris.formalMap_simplex]
  rfl

/-- The formal point cross product at a `0`-simplex `w` in the right argument is the
formal chain of the constant pair map. -/
@[simp]
theorem SingularHomology.formalPointCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (w : Fin 1 → W) :
    SingularHomology.formalPointCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 1 c := by
  have h :
    (SingularHomology.formalPointCrossProduct (V := V) 0).flip (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 1 := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.flip_apply, SingularHomology.formalPointCrossProduct_simplex,
      SingularMayerVietoris.formalMap_simplex]
    congr 1
    funext i
    rw [Fin.eq_zero i]
    rfl
  exact LinearMap.congr_fun h c

/-- Boundary compatibility of the formal point cross product: the boundary of
`point × c` relates to `point × ∂c`. -/
theorem SingularHomology.formalBoundary_pointCrossProduct {V W : Type*} (q : ℕ)
    (c : SingularMayerVietoris.FormalChains V 1)
    (d : SingularMayerVietoris.FormalChains W (q + 2)) :
    SingularMayerVietoris.formalBoundary (q + 1) (SingularHomology.formalPointCrossProduct (q + 1) c d) =
      SingularHomology.formalPointCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  have h :
    (SingularHomology.formalPointCrossProduct (V := V) (W := W) (q + 1)).compr₂
        (SingularMayerVietoris.formalBoundary (q + 1)) =
      (SingularHomology.formalPointCrossProduct q).compl₂ (SingularMayerVietoris.formalBoundary (q + 1)) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      SingularHomology.formalPointCrossProduct_simplex_left]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (v 0, z)) (q + 1)
          (SingularMayerVietoris.formalSimplex w)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Naturality of the formal point cross product under maps `f : V → V'`, `g : W → W'`. -/
theorem SingularHomology.formalMap_pointCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (c : SingularMayerVietoris.FormalChains V 1)
    (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 1) (SingularHomology.formalPointCrossProduct q c d) =
      SingularHomology.formalPointCrossProduct q (SingularMayerVietoris.formalMap f 1 c)
        (SingularMayerVietoris.formalMap g (q + 1) d) := by
  have h :
    (SingularHomology.formalPointCrossProduct (V := V) (W := W) q).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) (q + 1)) =
      ((SingularHomology.formalPointCrossProduct q).compl₂ (SingularMayerVietoris.formalMap g (q + 1))).comp
        (SingularMayerVietoris.formalMap f 1) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularHomology.formalPointCrossProduct_simplex, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d


/-! ### The formal edge cross product and its boundary law -/

/-- The formal edge cross product `FormalChains V 2 →ₗ FormalChains W (q+1) →ₗ`
formal chains of degree `q + 2`: the formal-chain shadow of the `1`-dimensional
cross product. -/
def SingularHomology.formalEdgeCrossProduct {V W : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × W) (q + 2)
  | 0 =>
    (SingularMayerVietoris.formalLift fun w : Fin 1 → W =>
        SingularMayerVietoris.formalMap (fun v => (v, w 0)) 2).flip
  | q + 1 =>
    SingularHomology.formalBilinearLift fun v w =>
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (SingularHomology.formalPointCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) -
          SingularHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w)))

/-- The formal edge cross product at a `0`-simplex right argument `w` is
`formalMap (v ↦ (v, w 0))` applied to `c`. -/
@[simp]
theorem SingularHomology.formalEdgeCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (w : Fin 1 → W) :
    SingularHomology.formalEdgeCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 2 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

/-- On an edge generator `v` and a `(q+1)`-simplex `w`, the formal edge cross product
is the sum of the two prism terms of the edge. -/
@[simp]
theorem SingularHomology.formalEdgeCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    SingularHomology.formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (SingularHomology.formalPointCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) -
          SingularHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w))) :=
  SingularHomology.formalBilinearLift_simplex _ _ _

/-- The boundary of the formal edge cross product at right degree `0` is the point
cross product of the edge's boundary. -/
theorem SingularHomology.formalBoundary_edgeCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalBoundary 1 (SingularHomology.formalEdgeCrossProduct 0 c d) =
      SingularHomology.formalPointCrossProduct 0 (SingularMayerVietoris.formalBoundary 1 c) d := by
  have h :
    (SingularHomology.formalEdgeCrossProduct (V := V) (W := W) 0).compr₂ (SingularMayerVietoris.formalBoundary 1) =
      (SingularHomology.formalPointCrossProduct 0).comp (SingularMayerVietoris.formalBoundary 1) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      SingularHomology.formalEdgeCrossProduct_zero_simplex_right, SingularHomology.formalPointCrossProduct_zero_simplex_right]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (z, w 0)) 1
          (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The boundary law for the formal edge cross product: `∂(e × c) = ∂e × c - e × ∂c`
at the formal-chain level. -/
theorem SingularHomology.formalBoundary_edgeCrossProduct {V W : Type*} :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 2)
      (d : SingularMayerVietoris.FormalChains W (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 2) (SingularHomology.formalEdgeCrossProduct (q + 1) c d) =
        SingularHomology.formalPointCrossProduct (q + 1) (SingularMayerVietoris.formalBoundary 1 c) d -
          SingularHomology.formalEdgeCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (SingularHomology.formalEdgeCrossProduct (V := V) (W := W) 1).compr₂
          (SingularMayerVietoris.formalBoundary 2) =
        (SingularHomology.formalPointCrossProduct 1).comp (SingularMayerVietoris.formalBoundary 1) -
          (SingularHomology.formalEdgeCrossProduct 0).compl₂ (SingularMayerVietoris.formalBoundary 1) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary 2
            (SingularHomology.formalEdgeCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [SingularHomology.formalEdgeCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary 1
            (SingularHomology.formalPointCrossProduct 1
                (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) -
              SingularHomology.formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_sub, SingularHomology.formalBoundary_pointCrossProduct, SingularHomology.formalBoundary_edgeCrossProduct_zero,
          sub_self]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (SingularHomology.formalEdgeCrossProduct (V := V) (W := W) (q + 2)).compr₂
          (SingularMayerVietoris.formalBoundary (q + 3)) =
        (SingularHomology.formalPointCrossProduct (q + 2)).comp (SingularMayerVietoris.formalBoundary 1) -
          (SingularHomology.formalEdgeCrossProduct (q + 1)).compl₂
            (SingularMayerVietoris.formalBoundary (q + 2)) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary (q + 3)
            (SingularHomology.formalEdgeCrossProduct (q + 2) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [SingularHomology.formalEdgeCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary (q + 2)
            (SingularHomology.formalPointCrossProduct (q + 2)
                (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) -
              SingularHomology.formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_sub, SingularHomology.formalBoundary_pointCrossProduct, ih,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, sub_zero, sub_self]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Naturality of the formal edge cross product under maps `f : V → V'`, `g : W → W'`. -/
theorem SingularHomology.formalMap_edgeCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 2)
      (d : SingularMayerVietoris.FormalChains W (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (SingularHomology.formalEdgeCrossProduct q c d) =
        SingularHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalMap f 2 c)
          (SingularMayerVietoris.formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (SingularHomology.formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) 2) =
        ((SingularHomology.formalEdgeCrossProduct 0).compl₂ (SingularMayerVietoris.formalMap g 1)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularHomology.formalEdgeCrossProduct_zero_simplex_right, SingularMayerVietoris.formalMap_simplex]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (SingularHomology.formalEdgeCrossProduct (V := V) (W := W) (q + 1)).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) (q + 3)) =
        ((SingularHomology.formalEdgeCrossProduct (q + 1)).compl₂ (SingularMayerVietoris.formalMap g (q + 2))).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularMayerVietoris.formalMap_simplex, SingularHomology.formalEdgeCrossProduct_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, SingularHomology.formalMap_pointCrossProduct, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d


/-! ### The formal triangle cross product -/

/-- The formal triangle cross product `FormalChains V 3 →ₗ FormalChains W (q+1) →ₗ`
formal chains of degree `q + 3`: the formal-chain shadow of the `2`-dimensional
cross product. -/
def SingularHomology.formalTriangleCrossProduct {V W : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × W) (q + 3)
  | 0 =>
    (SingularMayerVietoris.formalLift fun w : Fin 1 → W =>
        SingularMayerVietoris.formalMap (fun v => (v, w 0)) 3).flip
  | q + 1 =>
    SingularHomology.formalBilinearLift fun v w =>
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 3)
        (SingularHomology.formalEdgeCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) +
          SingularHomology.formalTriangleCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w)))

/-- The formal triangle cross product at a `0`-simplex right argument `w` is
`formalMap (v ↦ (v, w 0))` applied to `c`. -/
@[simp]
theorem SingularHomology.formalTriangleCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (w : Fin 1 → W) :
    SingularHomology.formalTriangleCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 3 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

/-- On a triangle generator `v` and a `(q+1)`-simplex `w`, the formal triangle cross
product is the signed sum of the three prism terms. -/
@[simp]
theorem SingularHomology.formalTriangleCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
    (v : Fin 3 → V) (w : Fin (q + 2) → W) :
    SingularHomology.formalTriangleCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 3)
        (SingularHomology.formalEdgeCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) +
          SingularHomology.formalTriangleCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w))) :=
  SingularHomology.formalBilinearLift_simplex _ _ _

/-- The boundary of the formal triangle cross product at right degree `0` is the point
cross product of the triangle's boundary. -/
theorem SingularHomology.formalBoundary_triangleCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalBoundary 2 (SingularHomology.formalTriangleCrossProduct 0 c d) =
      SingularHomology.formalEdgeCrossProduct 0 (SingularMayerVietoris.formalBoundary 2 c) d := by
  have h :
    (SingularHomology.formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
        (SingularMayerVietoris.formalBoundary 2) =
      (SingularHomology.formalEdgeCrossProduct 0).comp (SingularMayerVietoris.formalBoundary 2) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      SingularHomology.formalTriangleCrossProduct_zero_simplex_right, SingularHomology.formalEdgeCrossProduct_zero_simplex_right]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (z, w 0)) 2
          (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The boundary law for the formal triangle cross product:
`∂(t × c) = ∂t × c + t × ∂c` (sign by left degree `2`) at the formal-chain level. -/
theorem SingularHomology.formalBoundary_triangleCrossProduct {V W : Type*} :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 3)
      (d : SingularMayerVietoris.FormalChains W (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 3) (SingularHomology.formalTriangleCrossProduct (q + 1) c d) =
        SingularHomology.formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalBoundary 2 c) d +
          SingularHomology.formalTriangleCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (SingularHomology.formalTriangleCrossProduct (V := V) (W := W) 1).compr₂
          (SingularMayerVietoris.formalBoundary 3) =
        (SingularHomology.formalEdgeCrossProduct 1).comp (SingularMayerVietoris.formalBoundary 2) +
          (SingularHomology.formalTriangleCrossProduct 0).compl₂ (SingularMayerVietoris.formalBoundary 1) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary 3
            (SingularHomology.formalTriangleCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [SingularHomology.formalTriangleCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary 2
            (SingularHomology.formalEdgeCrossProduct 1
                (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) +
              SingularHomology.formalTriangleCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_add, SingularHomology.formalBoundary_edgeCrossProduct,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
          SingularHomology.formalBoundary_triangleCrossProduct_zero, neg_add_cancel]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (SingularHomology.formalTriangleCrossProduct (V := V) (W := W) (q + 2)).compr₂
          (SingularMayerVietoris.formalBoundary (q + 4)) =
        (SingularHomology.formalEdgeCrossProduct (q + 2)).comp (SingularMayerVietoris.formalBoundary 2) +
          (SingularHomology.formalTriangleCrossProduct (q + 1)).compl₂
            (SingularMayerVietoris.formalBoundary (q + 2)) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary (q + 4)
            (SingularHomology.formalTriangleCrossProduct (q + 2) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [SingularHomology.formalTriangleCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary (q + 3)
            (SingularHomology.formalEdgeCrossProduct (q + 2)
                (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) +
              SingularHomology.formalTriangleCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_add, SingularHomology.formalBoundary_edgeCrossProduct,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
          ih, SingularMayerVietoris.formalBoundary_boundary, map_zero, add_zero, neg_add_cancel]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Naturality of the formal triangle cross product under maps `f : V → V'`,
`g : W → W'`. -/
theorem SingularHomology.formalMap_triangleCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 3)
      (d : SingularMayerVietoris.FormalChains W (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f g) (q + 3) (SingularHomology.formalTriangleCrossProduct q c d) =
        SingularHomology.formalTriangleCrossProduct q (SingularMayerVietoris.formalMap f 3 c)
          (SingularMayerVietoris.formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (SingularHomology.formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) 3) =
        ((SingularHomology.formalTriangleCrossProduct 0).compl₂ (SingularMayerVietoris.formalMap g 1)).comp
          (SingularMayerVietoris.formalMap f 3) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularHomology.formalTriangleCrossProduct_zero_simplex_right, SingularMayerVietoris.formalMap_simplex]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (SingularHomology.formalTriangleCrossProduct (V := V) (W := W) (q + 1)).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) (q + 4)) =
        ((SingularHomology.formalTriangleCrossProduct (q + 1)).compl₂
              (SingularMayerVietoris.formalMap g (q + 2))).comp
          (SingularMayerVietoris.formalMap f 3) := by
      apply SingularHomology.formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularMayerVietoris.formalMap_simplex, SingularHomology.formalTriangleCrossProduct_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_add, SingularHomology.formalMap_edgeCrossProduct, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d


/-! ### Edge boundaries and supports -/

/-- The formal boundary of the `1`-simplex generator `v` is the formal difference
`w ↦ v 1 - v 0` of its endpoints. -/
theorem SingularHomology.formalBoundary_edge_simplex {V : Type*} (v : Fin 2 → V) :
    SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v) =
      SingularMayerVietoris.formalSimplex (fun _ : Fin 1 => v 1) -
        SingularMayerVietoris.formalSimplex (fun _ : Fin 1 => v 0) := by
  rw [SingularMayerVietoris.formalBoundary_simplex]
  change
    (∑ i : Fin 2, (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (v ∘ i.succAbove)) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul, ← sub_eq_add_neg]
  congr 1 <;> congr 1 <;> funext i <;> rw [Fin.eq_zero i] <;> rfl

/-- The formal point cross product of an edge generator's boundary is the difference
of the two endpoint insertions. -/
theorem SingularHomology.formalPointCrossProduct_edge_boundary {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    SingularHomology.formalPointCrossProduct q
        (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v)) d =
      SingularMayerVietoris.formalMap (fun w => (v 1, w)) (q + 1) d -
        SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  rw [SingularHomology.formalBoundary_edge_simplex, map_sub, LinearMap.sub_apply,
    SingularHomology.formalPointCrossProduct_simplex_left, SingularHomology.formalPointCrossProduct_simplex_left]


/-- If `c` is supported on `T` and `v 0 ∈ S`, the formal point cross product of `v`
and `c` is supported on `S × T`. -/
theorem SingularHomology.formalPointCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} (q : ℕ) {c : SingularMayerVietoris.FormalChains V 1}
    {d : SingularMayerVietoris.FormalChains W (q + 1)}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported S 1)
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1)) :
    SingularHomology.formalPointCrossProduct q c d ∈
      SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1) := by
  apply
    SingularMayerVietoris.formalLinearMap_mem_of_supported ((SingularHomology.formalPointCrossProduct q).flip d)
      (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1)) hc
  intro v hv
  change SingularHomology.formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d ∈ _
  rw [SingularHomology.formalPointCrossProduct_simplex_left]
  exact
    SingularMayerVietoris.formalMap_mem_supported (S := T) (T := S ×ˢ T) (fun w => (v 0, w))
      (fun _ hw => ⟨hv 0, hw⟩) hd

/-- If the edge generator's vertices lie in `S` and `c` is supported on `T`, the
formal edge cross product is supported on `S × T`. -/
theorem SingularHomology.formalEdgeCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} :
    ∀ (q : ℕ) {c : SingularMayerVietoris.FormalChains V 2}
      {d : SingularMayerVietoris.FormalChains W (q + 1)},
      c ∈ SingularMayerVietoris.formalChainsSupported S 2 →
        d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1) →
          SingularHomology.formalEdgeCrossProduct q c d ∈
            SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 2) := by
  intro q
  induction q with
  | zero =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported (SingularHomology.formalEdgeCrossProduct 0 c)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) 2) hd
    intro w hw
    rw [SingularHomology.formalEdgeCrossProduct_zero_simplex_right]
    exact
      SingularMayerVietoris.formalMap_mem_supported (S := S) (T := S ×ˢ T) (fun v => (v, w 0))
        (fun _ hv => ⟨hv, hw 0⟩) hc
  | succ q ih =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        ((SingularHomology.formalEdgeCrossProduct (q + 1)).flip d)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hc
    intro v hv
    change SingularHomology.formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v) d ∈ _
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        (SingularHomology.formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v))
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hd
    intro w hw
    rw [SingularHomology.formalEdgeCrossProduct_simplex_succ]
    apply
      SingularMayerVietoris.formalCone_mem_supported (show (v 0, w 0) ∈ S ×ˢ T from ⟨hv 0, hw 0⟩)
    apply Submodule.sub_mem
    · exact
        SingularHomology.formalPointCrossProduct_mem_supported (q + 1)
          (SingularMayerVietoris.formalBoundary_mem_supported 1
            (SingularMayerVietoris.formalSimplex_mem_supported hv))
          (SingularMayerVietoris.formalSimplex_mem_supported hw)
    · exact
        ih (SingularMayerVietoris.formalSimplex_mem_supported hv)
          (SingularMayerVietoris.formalBoundary_mem_supported (q + 1)
            (SingularMayerVietoris.formalSimplex_mem_supported hw))

/-! ### Pushforward of formal chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Formal chain maps compose: pushing forward along `g` then `f` is pushing forward along `f ∘ g`. -/
@[simp]
theorem SingularHomology.formalMap_comp {V W Z : Type*} (f : W → Z) (g : V → W) (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap f n (SingularMayerVietoris.formalMap g n c) =
      SingularMayerVietoris.formalMap (f ∘ g) n c := by
  have h :
    (SingularMayerVietoris.formalMap f n).comp (SingularMayerVietoris.formalMap g n) =
      SingularMayerVietoris.formalMap (f ∘ g) n := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c
/-- Formal chain maps along a product of maps commute with the factor swap in the stated sense. -/
theorem SingularHomology.formalMap_prod_swap {V W V' W' : Type*} (f : V → V')
    (g : W → W') (n : ℕ) (c : SingularMayerVietoris.FormalChains (W × V) n) :
    SingularMayerVietoris.formalMap (Prod.map f g) n
        (SingularMayerVietoris.formalMap Prod.swap n c) =
      SingularMayerVietoris.formalMap Prod.swap n
        (SingularMayerVietoris.formalMap (Prod.map g f) n c) := by
  rw [SingularHomology.formalMap_comp, SingularHomology.formalMap_comp]
  rfl


/-- Formal chain maps compose, applied form. -/
theorem SingularHomology.formalMap_comp_apply {V W Z : Type*} (f : W → Z) (g : V → W)
    (n : ℕ) (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap f n (SingularMayerVietoris.formalMap g n c) =
      SingularMayerVietoris.formalMap (f ∘ g) n c := by
  have h :
    (SingularMayerVietoris.formalMap f n).comp (SingularMayerVietoris.formalMap g n) =
      SingularMayerVietoris.formalMap (f ∘ g) n := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c
/-- The formal chain map along the identity is the identity. -/
theorem SingularHomology.formalMap_id_apply {V : Type*} (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap (id : V → V) n c = c := by
  have h : SingularMayerVietoris.formalMap (id : V → V) n = LinearMap.id := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [SingularMayerVietoris.formalMap_simplex, LinearMap.id_apply]
    rfl
  exact LinearMap.congr_fun h c
