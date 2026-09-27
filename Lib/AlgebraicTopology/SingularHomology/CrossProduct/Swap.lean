/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.CrossInsert
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Homology

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Graded commutativity of the cross product

The factor swap `T : X × Y → Y × X` satisfies `T_#(a × b) = (-1)^{pq} b × a` on homology
(Hatcher, *Algebraic Topology*, §3.B).  This file proves it for `(p, q) = (1, 1)` and uses the
`(2, 1)`/`(1, 2)` case to define the cross product in left degree two.

* `(1, 1)`: the formal defect `SingularHomology.formalEdgeSwapDefect` (`e × e' + T_#(e' × e)`)
  is the boundary of `SingularHomology.formalEdgeSwapHomotopy`
  (`.formalEdgeSwapHomotopy_boundary`); on singular chains this gives
  `SingularHomology.crossProductSwapHomotopy` with
  `∂H(a, b) = a × b + T_#(b × a)` (`.crossProductSwapHomotopy_boundary`), hence
  `T_#(b × a) = -(a × b)` for `1`-classes (`SingularHomology.crossProductHomology_swap`,
  `.crossProductHomology_add_swap_eq_zero`) and
  `f_#(a × b) = -f_#(b × a)` for a swap-invariant `f : X × X → Z`
  (`.crossProductHomology_pushforward_anticommute`).
* `(2, 1)` against `(1, 2)`: the mixed defect `SingularHomology.formalMixedSwapDefect`
  (`t × e - T_#(e × t)`) and its homotopy `.formalMixedSwapHomotopy`, whose boundary identity
  `.formalMixedSwapHomotopy_boundary` carries a lower-order edge-swap term; on singular chains
  `SingularHomology.crossProductMixedSwapHomotopy` with
  `.crossProductMixedSwapHomotopy_boundary` and `_boundary_of_cycle`.
* The cross product in left degree two, `SingularHomology.crossProductHomologyTwoOne X Y :
  H₂(X) →ₗ H₁(Y) →ₗ H₃(X × Y)`, defined as `T_#` of the `(1, 2)` product
  `SingularHomology.crossProductHomology Y X 2`; by the mixed swap it is computed on cycle
  representatives by the triangle product (`SingularHomology.crossProductTwoOneCycles`,
  `.crossProductHomologyTwoOne_cycleClass`).
-/


@[expose] public noncomputable section


/-! ### The edge swap defect and its homotopy on formal chains -/

/-- Swapping factors turns a point cross product (1, 2) into an edge cross product (0) of the swapped chains. -/
theorem SingularHomology.formalMap_swap_pointCrossProduct_one {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap Prod.swap 2 (SingularHomology.formalPointCrossProduct 1 c d) =
      SingularHomology.formalEdgeCrossProduct 0 d c := by
  have h :
    (SingularHomology.formalPointCrossProduct (V := V) (W := W) 1).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 2) =
      (SingularHomology.formalEdgeCrossProduct 0).flip := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 2
          (SingularHomology.formalPointCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        SingularHomology.formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 2
            (SingularMayerVietoris.formalMap (fun z => (v 0, z)) 2
              (SingularMayerVietoris.formalSimplex w)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 2)
          (SingularHomology.formalPointCrossProduct_simplex_left 1 v (SingularMayerVietoris.formalSimplex w))
      _ =
          SingularMayerVietoris.formalMap (fun z => (z, v 0)) 2
            (SingularMayerVietoris.formalSimplex w) := by
        rw [SingularHomology.formalMap_comp]
        rfl
      _ = _ :=
        (SingularHomology.formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w) v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
/-- Swapping factors turns an edge cross product in degree zero into a point cross product of the swapped chains. -/
theorem SingularHomology.formalMap_swap_edgeCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalMap Prod.swap 2 (SingularHomology.formalEdgeCrossProduct 0 c d) =
      SingularHomology.formalPointCrossProduct 1 d c := by
  have h :
    (SingularHomology.formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 2) =
      (SingularHomology.formalPointCrossProduct 1).flip := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 2
          (SingularHomology.formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        SingularHomology.formalPointCrossProduct 1 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 2
            (SingularMayerVietoris.formalMap (fun z => (z, w 0)) 2
              (SingularMayerVietoris.formalSimplex v)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 2)
          (SingularHomology.formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex v) w)
      _ =
          SingularMayerVietoris.formalMap (fun z => (w 0, z)) 2
            (SingularMayerVietoris.formalSimplex v) := by
        rw [SingularHomology.formalMap_comp]
        rfl
      _ = _ :=
        (SingularHomology.formalPointCrossProduct_simplex_left 1 w (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
/-- The defect measuring the failure of the edge cross product to commute with the factor swap: the sum of the edge cross product and its swap. -/
def SingularHomology.formalEdgeSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 3 :=
  SingularHomology.formalEdgeCrossProduct 1 +
    (SingularHomology.formalEdgeCrossProduct 1).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 3)
/-- Explicit form of the edge swap defect: `σ ×₁ τ + swap#(τ ×₁ σ)`. -/
@[simp]
theorem SingularHomology.formalEdgeSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularHomology.formalEdgeSwapDefect c d =
      SingularHomology.formalEdgeCrossProduct 1 c d +
        SingularMayerVietoris.formalMap Prod.swap 3 (SingularHomology.formalEdgeCrossProduct 1 d c) :=
  rfl
/-- The edge swap defect is a cycle — its boundary vanishes, so it represents the graded-commutativity obstruction in homology. -/
theorem SingularHomology.formalBoundary_edgeSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 2 (SingularHomology.formalEdgeSwapDefect c d) = 0 := by
  rw [SingularHomology.formalEdgeSwapDefect_apply, map_add, SingularHomology.formalBoundary_edgeCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, SingularHomology.formalBoundary_edgeCrossProduct, map_sub,
    SingularHomology.formalMap_swap_pointCrossProduct_one, SingularHomology.formalMap_swap_edgeCrossProduct_zero]
  abel
/-- The edge swap defect is natural under maps of both factors. -/
theorem SingularHomology.formalMap_edgeSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 3 (SingularHomology.formalEdgeSwapDefect c d) =
      SingularHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [SingularHomology.formalEdgeSwapDefect_apply, map_add, SingularHomology.formalMap_edgeCrossProduct, SingularHomology.formalMap_prod_swap,
    SingularHomology.formalMap_edgeCrossProduct, SingularHomology.formalEdgeSwapDefect_apply]
/-- A degree-3 chain homotopy witnessing that the edge swap defect is a boundary: the chain-level proof of graded commutativity of the cross product. -/
def SingularHomology.formalEdgeSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  SingularHomology.formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 3
      (SingularHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w))
/-- On simplices the swap homotopy is the cone over `(v 0, w 0)` of the swap defect. -/
@[simp]
theorem SingularHomology.formalEdgeSwapHomotopy_simplex {V W : Type*} (v : Fin 2 → V)
    (w : Fin 2 → W) :
    SingularHomology.formalEdgeSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 3
        (SingularHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)) :=
  SingularHomology.formalBilinearLift_simplex _ _ _
/-- The boundary of the swap homotopy is exactly the swap defect: `∂H = σ ×₁ τ + swap#(τ ×₁ σ)`. -/
theorem SingularHomology.formalEdgeSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (SingularHomology.formalEdgeSwapHomotopy c d) =
      SingularHomology.formalEdgeSwapDefect c d := by
  have h :
    (SingularHomology.formalEdgeSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 3) =
      SingularHomology.formalEdgeSwapDefect := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, SingularHomology.formalEdgeSwapHomotopy_simplex,
      SingularMayerVietoris.formalBoundary_cone, SingularHomology.formalBoundary_edgeSwapDefect, map_zero,
      sub_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
/-- The swap homotopy is natural under maps of both factors. -/
theorem SingularHomology.formalMap_edgeSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (SingularHomology.formalEdgeSwapHomotopy c d) =
      SingularHomology.formalEdgeSwapHomotopy (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have h :
    (SingularHomology.formalEdgeSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 4) =
      ((SingularHomology.formalEdgeSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 2) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.formalEdgeSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone, SingularHomology.formalMap_edgeSwapDefect,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d


/-! ### The swap homotopy on singular chains and graded commutativity -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Chains induced by a product map after a factor swap equal the swapped double pushforward. -/
theorem SingularHomology.inducedChain_prodMap_swap {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (c : SingularChains.Chains (Y × X) n) :
    SingularChains.inducedChain (f.prodMap g) n
        (SingularChains.inducedChain ContinuousMap.prodSwap n c) =
      SingularChains.inducedChain ContinuousMap.prodSwap n
        (SingularChains.inducedChain (g.prodMap f) n c) := by
  calc
    _ = SingularChains.inducedChain ((f.prodMap g).comp ContinuousMap.prodSwap) n c :=
      (LinearMap.congr_fun (SingularChains.inducedChain_comp _ _ n) c).symm
    _ = SingularChains.inducedChain (ContinuousMap.prodSwap.comp (g.prodMap f)) n c := rfl
    _ = _ := LinearMap.congr_fun (SingularChains.inducedChain_comp _ _ n) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The chain homotopy on `X × Y` in degree 3 witnessing graded commutativity of the 1-1 cross product. -/
def SingularHomology.crossProductSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ] SingularChains.Chains (X × Y) 3 :=
  SingularHomology.chainBilinearLift X Y 1 1 fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) 3
      (SingularHomology.productAffineChainMap 1 1 3
        (SingularHomology.formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplices the cross product swap homotopy is induced by the explicit prism data of the product simplex. -/
@[simp]
theorem SingularHomology.crossProductSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : SingularChains.SingularSimplex X 1)
    (τ : SingularChains.SingularSimplex Y 1) :
    SingularHomology.crossProductSwapHomotopy X Y (SingularChains.simplexChain X 1 σ)
        (SingularChains.simplexChain Y 1 τ) =
      SingularChains.inducedChain (σ.prodMap τ) 3
        (SingularHomology.productAffineChainMap 1 1 3
          (SingularHomology.formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  SingularHomology.chainBilinearLift_simplex X Y 1 1 _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product swap homotopy is natural under maps of both factors. -/
theorem SingularHomology.crossProductSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1) :
    SingularChains.inducedChain (f.prodMap g) 3 (SingularHomology.crossProductSwapHomotopy X Y a b) =
      SingularHomology.crossProductSwapHomotopy X' Y' (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g 1 b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductSwapHomotopy X Y)
        (SingularChains.inducedChain (f.prodMap g) 3) =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductSwapHomotopy X' Y') (SingularChains.inducedChain f 1)
        (SingularChains.inducedChain g 1) := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 1
    intro σ τ
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, SingularHomology.crossProductSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The swap homotopy commutes with the affine chain maps on standard simplices. -/
theorem SingularHomology.crossProductSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    SingularHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      SingularHomology.productAffineChainMap p q 3 (SingularHomology.formalEdgeSwapHomotopy a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q))
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1) =
      SingularHomology.integerBilinearPostcompose SingularHomology.formalEdgeSwapHomotopy (SingularHomology.productAffineChainMap p q 3) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.crossProductSwapHomotopy_simplex]
    rw [SingularHomology.inducedChain_productAffineChainMap]
    change
      SingularHomology.productAffineChainMap p q 3
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            4
            (SingularHomology.formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [SingularHomology.formalMap_edgeSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Affine form of the swap homotopy boundary identity on standard simplices. -/
theorem SingularHomology.crossProductSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 3
            2).hom
        (SingularHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)) =
      SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b) +
        SingularChains.inducedChain ContinuousMap.prodSwap 2
          (SingularHomology.crossProductEdge (SingularChains.Simplex q) (SingularChains.Simplex p) 1
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 1 a)) := by
  rw [SingularHomology.crossProductSwapHomotopy_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularHomology.formalEdgeSwapHomotopy_boundary, SingularHomology.formalEdgeSwapDefect_apply, map_add,
    SingularHomology.crossProductEdge_affineChainMap, SingularHomology.crossProductEdge_affineChainMap,
    SingularHomology.inducedChain_swap_productAffineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The defining identity of the swap homotopy: `∂H = a ×₁ b + swap#(b ×₁ a)` — graded commutativity at chain level. -/
theorem SingularHomology.crossProductSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) :
    ((SingularChains.singularComplex (X × Y)).d 3 2).hom (SingularHomology.crossProductSwapHomotopy X Y a b) =
      SingularHomology.crossProductEdge X Y 1 a b +
        SingularChains.inducedChain ContinuousMap.prodSwap 2 (SingularHomology.crossProductEdge Y X 1 b a) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductSwapHomotopy X Y)
        ((SingularChains.singularComplex (X × Y)).d 3 2).hom =
      SingularHomology.crossProductEdge X Y 1 +
        SingularHomology.integerBilinearPostcompose (SingularHomology.integerBilinearFlip (SingularHomology.crossProductEdge Y X 1))
          (SingularChains.inducedChain ContinuousMap.prodSwap 2) := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 1
    intro σ τ
    have hstd :=
      SingularHomology.crossProductSwapHomotopy_boundary_affine 1 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 2) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearFlip_apply, LinearMap.add_apply,
      map_add, SingularChains.inducedChain_boundary, SingularHomology.crossProductSwapHomotopy_natural,
      SingularHomology.inducedChain_prodMap_swap, SingularHomology.crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cycle-class cross product of two 1-cycles plus its swap pushforward vanishes: `a × b + swap#(b × a) = 0` in homology. -/
theorem SingularHomology.crossProductCycleClasses_add_swap_eq_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1) :
    SingularHomology.crossProductCycleClasses X Y 1 a b +
        SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
          (SingularHomology.crossProductCycleClasses Y X 1 b a) =
      0 := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y)) 2
          (SingularHomology.crossProductCycles X Y 1 a b) +
        (HomologicalComplex.homologyMap (SingularChains.singularChainMap ContinuousMap.prodSwap)
              2).hom
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (Y × X))
            2 (SingularHomology.crossProductCycles Y X 1 b a)) =
      0
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, ← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) 2 _).mpr
  refine ⟨SingularHomology.crossProductSwapHomotopy X Y a.1 b.1, ?_⟩
  rw [Submodule.coe_add, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact SingularHomology.crossProductSwapHomotopy_boundary a.1 b.1

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Graded commutativity on homology: `a × b + swap#(b × a) = 0` for 1-classes. -/
theorem SingularHomology.crossProductHomology_add_swap_eq_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    SingularHomology.crossProductHomology X Y 1 a b +
        SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
          (SingularHomology.crossProductHomology Y X 1 b a) =
      0 := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Y) 1
      b
  rw [SingularHomology.crossProductHomology_cycleClass, SingularHomology.crossProductHomology_cycleClass]
  exact SingularHomology.crossProductCycleClasses_add_swap_eq_zero a b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Graded commutativity: swapping the factors of a 1-1 cross product negates it. -/
theorem SingularHomology.crossProductHomology_swap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
        (SingularHomology.crossProductHomology X Y 1 a b) =
      -SingularHomology.crossProductHomology Y X 1 b a := by
  have h := SingularHomology.crossProductHomology_add_swap_eq_zero b a
  exact eq_neg_of_add_eq_zero_right h

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Anticommutativity under a swap-invariant map: `f#(a × a') = -f#(b × b')` pairing structure on the same space. -/
theorem SingularHomology.crossProductHomology_pushforward_anticommute {X Z : Type}
    [TopologicalSpace X] [TopologicalSpace Z] (f : C(X × X, Z))
    (hf : f.comp ContinuousMap.prodSwap = f) (a b : SingularMayerVietoris.SingularHomology X 1) :
    SingularMayerVietoris.singularHomologyMap f 2 (SingularHomology.crossProductHomology X X 1 a b) =
      -SingularMayerVietoris.singularHomologyMap f 2 (SingularHomology.crossProductHomology X X 1 b a) := by
  have h :=
    congrArg (SingularMayerVietoris.singularHomologyMap f 2) (SingularHomology.crossProductHomology_swap a b)
  rw [map_neg] at h
  have hc :=
    LinearMap.congr_fun (SingularHomology.singularHomologyMap_comp (ContinuousMap.prodSwap : C(X × X, X × X)) f 2)
      (SingularHomology.crossProductHomology X X 1 a b)
  rw [hf] at hc
  exact hc.trans h


/-! ### The mixed swap of the triangle and edge products -/

/-- Swapping factors turns a point cross product (2, 3) into a triangle cross product of the swapped chains. -/
theorem SingularHomology.formalMap_swap_pointCrossProduct_two {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (d : SingularMayerVietoris.FormalChains W 3) :
    SingularMayerVietoris.formalMap Prod.swap 3 (SingularHomology.formalPointCrossProduct 2 c d) =
      SingularHomology.formalTriangleCrossProduct 0 d c := by
  have heq :
    (SingularHomology.formalPointCrossProduct (V := V) (W := W) 2).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 3) =
      (SingularHomology.formalTriangleCrossProduct 0).flip := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 3
          (SingularHomology.formalPointCrossProduct 2 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        SingularHomology.formalTriangleCrossProduct 0 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 3
            (SingularMayerVietoris.formalMap (fun z => (v 0, z)) 3
              (SingularMayerVietoris.formalSimplex w)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 3)
          (SingularHomology.formalPointCrossProduct_simplex_left 2 v (SingularMayerVietoris.formalSimplex w))
      _ =
          SingularMayerVietoris.formalMap (fun z => (z, v 0)) 3
            (SingularMayerVietoris.formalSimplex w) := by
        rw [SingularHomology.formalMap_comp]
        rfl
      _ = _ :=
        (SingularHomology.formalTriangleCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w)
            v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d
/-- The mixed-swap defect between the (3, 2) and (2, 3) bracketings of the cross product: the failure of the triangle/edge cross products to commute with the factor swap. -/
def SingularHomology.formalMixedSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  SingularHomology.formalTriangleCrossProduct 1 -
    (SingularHomology.formalEdgeCrossProduct 2).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 4)
/-- Explicit form of the mixed swap defect: triangle cross product minus the swapped edge cross product. -/
@[simp]
theorem SingularHomology.formalMixedSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularHomology.formalMixedSwapDefect c d =
      SingularHomology.formalTriangleCrossProduct 1 c d -
        SingularMayerVietoris.formalMap Prod.swap 4 (SingularHomology.formalEdgeCrossProduct 2 d c) :=
  rfl
/-- The boundary of the mixed swap defect is the edge swap defect of the boundary: the defects compose coherently. -/
theorem SingularHomology.formalBoundary_mixedSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (SingularHomology.formalMixedSwapDefect c d) =
      SingularHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalBoundary 2 c) d := by
  rw [SingularHomology.formalMixedSwapDefect_apply, map_sub, SingularHomology.formalBoundary_triangleCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, SingularHomology.formalBoundary_edgeCrossProduct, map_sub,
    SingularHomology.formalMap_swap_pointCrossProduct_two, SingularHomology.formalEdgeSwapDefect_apply]
  abel
/-- The mixed swap defect is natural under maps of both factors. -/
theorem SingularHomology.formalMap_mixedSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (SingularHomology.formalMixedSwapDefect c d) =
      SingularHomology.formalMixedSwapDefect (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [SingularHomology.formalMixedSwapDefect_apply, map_sub, SingularHomology.formalMap_triangleCrossProduct, SingularHomology.formalMap_prod_swap,
    SingularHomology.formalMap_edgeCrossProduct, SingularHomology.formalMixedSwapDefect_apply]
/-- The chain homotopy witnessing that the mixed swap defect is a boundary. -/
def SingularHomology.formalMixedSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 5 :=
  SingularHomology.formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 4
      (SingularHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w) -
        SingularHomology.formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
          (SingularMayerVietoris.formalSimplex w))
/-- On simplices the mixed swap homotopy is the cone of the mixed swap defect. -/
@[simp]
theorem SingularHomology.formalMixedSwapHomotopy_simplex {V W : Type*} (v : Fin 3 → V)
    (w : Fin 2 → W) :
    SingularHomology.formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 4
        (SingularHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) -
          SingularHomology.formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w)) :=
  SingularHomology.formalBilinearLift_simplex _ _ _
/-- The boundary identity of the mixed swap homotopy, including the lower-order defect term. -/
theorem SingularHomology.formalMixedSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 4 (SingularHomology.formalMixedSwapHomotopy c d) +
        SingularHomology.formalEdgeSwapHomotopy (SingularMayerVietoris.formalBoundary 2 c) d =
      SingularHomology.formalMixedSwapDefect c d := by
  have heq :
    (SingularHomology.formalMixedSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 4) +
        (SingularHomology.formalEdgeSwapHomotopy).comp (SingularMayerVietoris.formalBoundary 2) =
      SingularHomology.formalMixedSwapDefect := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalBoundary 4
            (SingularHomology.formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) +
          SingularHomology.formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) =
        SingularHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)
    have hz :
      SingularMayerVietoris.formalBoundary 3
          (SingularHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) -
            SingularHomology.formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
              (SingularMayerVietoris.formalSimplex w)) =
        0 := by
      rw [map_sub, SingularHomology.formalBoundary_mixedSwapDefect, SingularHomology.formalEdgeSwapHomotopy_boundary, sub_self]
    rw [SingularHomology.formalMixedSwapHomotopy_simplex, SingularMayerVietoris.formalBoundary_cone, hz, map_zero,
      sub_zero, sub_add_cancel]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d
/-- The mixed swap homotopy is natural under maps of both factors. -/
theorem SingularHomology.formalMap_mixedSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 5 (SingularHomology.formalMixedSwapHomotopy c d) =
      SingularHomology.formalMixedSwapHomotopy (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have heq :
    (SingularHomology.formalMixedSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 5) =
      ((SingularHomology.formalMixedSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 3) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.formalMixedSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone]
    congr 1
    rw [map_sub, SingularHomology.formalMap_mixedSwapDefect, SingularHomology.formalMap_edgeSwapHomotopy,
      SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

/-! ### The mixed swap homotopy on singular chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The space-level chain homotopy for the mixed (2,1) swap of cross products on `X × Y`. -/
def SingularHomology.crossProductMixedSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ] SingularChains.Chains (X × Y) 4 :=
  SingularHomology.chainBilinearLift X Y 2 1 fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) 4
      (SingularHomology.productAffineChainMap 2 1 4
        (SingularHomology.formalMixedSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplices the mixed swap homotopy is induced by the explicit prism data. -/
@[simp]
theorem SingularHomology.crossProductMixedSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : SingularChains.SingularSimplex X 2)
    (τ : SingularChains.SingularSimplex Y 1) :
    SingularHomology.crossProductMixedSwapHomotopy X Y (SingularChains.simplexChain X 2 σ)
        (SingularChains.simplexChain Y 1 τ) =
      SingularChains.inducedChain (σ.prodMap τ) 4
        (SingularHomology.productAffineChainMap 2 1 4
          (SingularHomology.formalMixedSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  SingularHomology.chainBilinearLift_simplex X Y 2 1 _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The mixed swap homotopy is natural under maps of both factors. -/
theorem SingularHomology.crossProductMixedSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : SingularChains.Chains X 2) (b : SingularChains.Chains Y 1) :
    SingularChains.inducedChain (f.prodMap g) 4 (SingularHomology.crossProductMixedSwapHomotopy X Y a b) =
      SingularHomology.crossProductMixedSwapHomotopy X' Y' (SingularChains.inducedChain f 2 a)
        (SingularChains.inducedChain g 1 b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductMixedSwapHomotopy X Y)
        (SingularChains.inducedChain (f.prodMap g) 4) =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductMixedSwapHomotopy X' Y')
        (SingularChains.inducedChain f 2) (SingularChains.inducedChain g 1) := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 1
    intro σ τ
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, SingularHomology.crossProductMixedSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The mixed swap homotopy commutes with the affine chain maps on standard simplices. -/
theorem SingularHomology.crossProductMixedSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    SingularHomology.crossProductMixedSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      SingularHomology.productAffineChainMap p q 4 (SingularHomology.formalMixedSwapHomotopy a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductMixedSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q))
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q 1) =
      SingularHomology.integerBilinearPostcompose SingularHomology.formalMixedSwapHomotopy (SingularHomology.productAffineChainMap p q 4) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.crossProductMixedSwapHomotopy_simplex]
    rw [SingularHomology.inducedChain_productAffineChainMap]
    change
      SingularHomology.productAffineChainMap p q 4
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            5
            (SingularHomology.formalMixedSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [SingularHomology.formalMap_mixedSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Affine form of the mixed swap homotopy boundary identity. -/
theorem SingularHomology.crossProductMixedSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 4
              3).hom
          (SingularHomology.crossProductMixedSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
            (SingularMayerVietoris.affineChainMap p 2 a)
            (SingularMayerVietoris.affineChainMap q 1 b)) +
        SingularHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d 2 1).hom
            (SingularMayerVietoris.affineChainMap p 2 a))
          (SingularMayerVietoris.affineChainMap q 1 b) =
      SingularHomology.crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q 1 b) -
        SingularChains.inducedChain ContinuousMap.prodSwap 3
          (SingularHomology.crossProductEdge (SingularChains.Simplex q) (SingularChains.Simplex p) 2
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 2 a)) := by
  rw [SingularHomology.crossProductMixedSwapHomotopy_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, SingularHomology.crossProductSwapHomotopy_affineChainMap,
    SingularHomology.crossProductTriangle_affineChainMap, SingularHomology.crossProductEdge_affineChainMap,
    SingularHomology.inducedChain_swap_productAffineChainMap, ← map_add, SingularHomology.formalMixedSwapHomotopy_boundary,
    SingularHomology.formalMixedSwapDefect_apply, map_sub]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The defining boundary identity of the mixed swap homotopy, with the lower-order swap homotopy term. -/
theorem SingularHomology.crossProductMixedSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y 1) :
    ((SingularChains.singularComplex (X × Y)).d 4 3).hom (SingularHomology.crossProductMixedSwapHomotopy X Y a b) +
        SingularHomology.crossProductSwapHomotopy X Y (((SingularChains.singularComplex X).d 2 1).hom a) b =
      SingularHomology.crossProductTriangle X Y 1 a b -
        SingularChains.inducedChain ContinuousMap.prodSwap 3 (SingularHomology.crossProductEdge Y X 2 b a) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductMixedSwapHomotopy X Y)
          ((SingularChains.singularComplex (X × Y)).d 4 3).hom +
        SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductSwapHomotopy X Y)
          ((SingularChains.singularComplex X).d 2 1).hom LinearMap.id =
      SingularHomology.crossProductTriangle X Y 1 -
        SingularHomology.integerBilinearPostcompose (SingularHomology.integerBilinearFlip (SingularHomology.crossProductEdge Y X 2))
          (SingularChains.inducedChain ContinuousMap.prodSwap 3) := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 1
    intro σ τ
    have hstd :=
      SingularHomology.crossProductMixedSwapHomotopy_boundary_affine 2 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 3) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularHomology.integerBilinearFlip_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, SingularChains.inducedChain_boundary,
      SingularHomology.crossProductMixedSwapHomotopy_natural, SingularHomology.crossProductSwapHomotopy_natural,
      SingularHomology.inducedChain_prodMap_swap, SingularHomology.crossProductTriangle_natural, SingularHomology.crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If the 2-chain is a cycle, the mixed swap homotopy boundary reduces to the swap homotopy of the boundary data. -/
theorem SingularHomology.crossProductMixedSwapHomotopy_boundary_of_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 2)
    (ha : ((SingularChains.singularComplex X).d 2 1).hom a = 0) (b : SingularChains.Chains Y 1) :
    ((SingularChains.singularComplex (X × Y)).d 4 3).hom (SingularHomology.crossProductMixedSwapHomotopy X Y a b) =
      SingularHomology.crossProductTriangle X Y 1 a b -
        SingularChains.inducedChain ContinuousMap.prodSwap 3 (SingularHomology.crossProductEdge Y X 2 b a) := by
  simpa only [ha, map_zero, LinearMap.zero_apply, add_zero] using
    SingularHomology.crossProductMixedSwapHomotopy_boundary a b

/-! ### The cross product in left degree two on homology -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a 2-cycle of `X` with a 1-cycle of `Y`, a 3-cycle of `X × Y` — the degree-(2,1) instance of the cycle-level cross product. -/
def SingularHomology.crossProductTwoOneCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1 →ₗ[ℤ]
        SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (X × Y)) 3
    where
  toFun
    a :=
    { toFun
        b :=
        SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex (X × Y)) 3
          (SingularHomology.crossProductTriangle X Y 1 a.1 b.1)
          (by
            change
              ((SingularChains.singularComplex (X × Y)).d 3 2).hom
                  (SingularHomology.crossProductTriangle X Y 1 a.1 b.1) =
                0
            simp only [SingularHomology.crossProductTriangle_boundary,
              SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex X) 2 a,
              SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex Y) 1 b,
              map_zero, LinearMap.zero_apply, zero_add])
      map_add' b
        c := by
        apply Subtype.ext
        exact (SingularHomology.crossProductTriangle X Y 1 a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (SingularHomology.crossProductTriangle X Y 1 a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : SingularChains.Chains Y 1 →ₗ[ℤ] SingularChains.Chains (X × Y) 3 => f c.1)
        ((SingularHomology.crossProductTriangle X Y 1).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : SingularChains.Chains Y 1 →ₗ[ℤ] SingularChains.Chains (X × Y) 3 => f c.1)
        ((SingularHomology.crossProductTriangle X Y 1).map_smul r a.1)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The underlying chain of the (2,1) cycle cross product is the chain-level cross product of the underlying chains. -/
@[simp]
theorem SingularHomology.crossProductTwoOneCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1) :
    (SingularHomology.crossProductTwoOneCycles X Y a b).1 = SingularHomology.crossProductTriangle X Y 1 a.1 b.1 :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology cross product of a 2-class with a 1-class, valued in `H₃(X × Y)`, normalized through the factor swap. -/
def SingularHomology.crossProductHomologyTwoOne (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Y 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology (X × Y) 3 :=
  SingularHomology.integerBilinearPostcompose (SingularHomology.integerBilinearFlip (SingularHomology.crossProductHomology Y X 2))
    (SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Explicit evaluation of the (2,1) homology cross product through the swap pushforward. -/
@[simp]
theorem SingularHomology.crossProductHomologyTwoOne_apply (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 2)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    SingularHomology.crossProductHomologyTwoOne X Y a b =
      SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3
        (SingularHomology.crossProductHomology Y X 2 b a) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The (2,1) homology cross product is computed on cycle representatives. -/
@[simp]
theorem SingularHomology.crossProductHomologyTwoOne_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1) :
    SingularHomology.crossProductHomologyTwoOne X Y
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) 1 b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y)) 3
        (SingularHomology.crossProductTwoOneCycles X Y a b) := by
  rw [SingularHomology.crossProductHomologyTwoOne_apply, SingularHomology.crossProductHomology_cycleClass]
  change
    (HomologicalComplex.homologyMap (SingularChains.singularChainMap ContinuousMap.prodSwap) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (Y × X)) 3
          (SingularHomology.crossProductCycles Y X 2 b a)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply Eq.symm
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (SingularChains.singularComplex (X × Y)) 3 _ _).mpr
  refine ⟨SingularHomology.crossProductMixedSwapHomotopy X Y a.1 b.1, ?_⟩
  simp only [SingularHomology.crossProductTwoOneCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val,
    SingularHomology.crossProductCycles_val]
  exact
    SingularHomology.crossProductMixedSwapHomotopy_boundary_of_cycle a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 a)
      b.1
