/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.CrossInsert
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Multilinear
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Formal
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Affine

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# The chain-level cross product in left degrees `0`, `1` and `2`

The cross product of singular chains over `ℤ`, on generators `σ × τ ↦ (σ.prodMap τ)_#` of the
affine triangulation of the prism, for a left simplex of dimension `0`, `1` or `2`:

* `SingularHomology.crossProductZeroLeft X Y n : Chains X 0 →ₗ Chains Y n →ₗ Chains (X × Y) n`
  and `.crossProductZeroRight` (point insertion, via `SingularHomology.zeroSimplexValue`,
  `.crossInsertRight`),
* `SingularHomology.crossProductEdge X Y n : Chains X 1 →ₗ Chains Y n →ₗ Chains (X × Y) (n + 1)`,
* `SingularHomology.crossProductTriangle X Y n : Chains X 2 →ₗ Chains Y n →ₗ Chains (X × Y) (n + 2)`.

Each is natural in both spaces (`SingularHomology.crossProductEdge_natural`,
`.crossProductTriangle_natural`, `.crossProductZeroLeft_natural`), is computed on affine chains
of a product of standard simplices by the formal cross product
(`SingularHomology.crossProductEdge_affineChainMap`, `.crossProductTriangle_affineChainMap`,
`.crossProductZeroLeft_affineChainMap`), and satisfies the Leibniz rule
`∂(a × b) = ∂a × b + (-1)^p a × ∂b` (`SingularHomology.crossProductEdge_boundary`,
`.crossProductTriangle_boundary`, with the degree-zero cases and the cycle consequences
`SingularHomology.crossProductEdge_cycle`, `.crossProductEdge_boundary_of_left_cycle`,
`.crossProductTriangle_boundary_of_right_cycle`).

This is the boundary formula for the cross product of Hatcher, *Algebraic Topology*, §3.B, at
left degree `p ≤ 2`; the triangle product is the prism operator of homotopy-invariance arguments.
-/


@[expose] public noncomputable section


/-! ### Point insertions and the zero-degree cross product -/

/-- The point of `X` carried by a singular `0`-simplex: its value at the unique vertex. -/
def SingularHomology.zeroSimplexValue {X : Type} [TopologicalSpace X]
    (σ : SingularChains.SingularSimplex X 0) : X :=
  σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))

/-- `zeroSimplexValue` of a postcomposition is `f` applied to the zero-simplex value. -/
@[simp]
theorem SingularHomology.zeroSimplexValue_comp {X X' : Type} [TopologicalSpace X]
    [TopologicalSpace X'] (f : C(X, X')) (σ : SingularChains.SingularSimplex X 0) :
    SingularHomology.zeroSimplexValue (f.comp σ) = f (SingularHomology.zeroSimplexValue σ) :=
  rfl

/-- The map `x ↦ (x, y)` inserting a fixed right point `y`. -/
def SingularHomology.crossInsertRight {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (y : Y) : C(X, X × Y) :=
  ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degree-`0`-left cross product: `Chains X 0 →ₗ Chains Y n →ₗ Chains (X × Y) n`,
sending `(σ, τ)` to `τ` pushed along the insertion of `σ`'s point. -/
def SingularHomology.crossProductZeroLeft (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X 0 →ₗ[ℤ]
      SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) n :=
  SingularHomology.chainBilinearLift X Y 0 n fun σ τ =>
    SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertLeft (SingularHomology.zeroSimplexValue σ)).comp τ)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degree-`0`-right cross product: `Chains X n →ₗ Chains Y 0 →ₗ Chains (X × Y) n`,
sending `(σ, τ)` to `σ` pushed along the insertion of `τ`'s point. -/
def SingularHomology.crossProductZeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ]
      SingularChains.Chains Y 0 →ₗ[ℤ] SingularChains.Chains (X × Y) n :=
  chainBilinearLift X Y n 0 fun σ τ =>
    SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertRight (zeroSimplexValue τ)).comp σ)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a left `0`-simplex generator, `crossProductZeroLeft` inserts the point
`zeroSimplexValue σ`. -/
@[simp]
theorem SingularHomology.crossProductZeroLeft_simplex_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 0) :
    SingularHomology.crossProductZeroLeft X Y n (SingularChains.simplexChain X 0 σ) =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft (Y := Y) (SingularHomology.zeroSimplexValue σ)) n := by
  apply SingularChains.chainMap_ext Y n
  intro τ
  rw [SingularHomology.crossProductZeroLeft, SingularHomology.chainBilinearLift_simplex, SingularChains.inducedChain_simplex]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplex generators, `crossProductZeroLeft` sends `σ, τ` to the chain of
`τ` composed with `crossInsertLeft (zeroSimplexValue σ)`. -/
@[simp]
theorem SingularHomology.crossProductZeroLeft_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 0)
    (τ : SingularChains.SingularSimplex Y n) :
    SingularHomology.crossProductZeroLeft X Y n (SingularChains.simplexChain X 0 σ)
        (SingularChains.simplexChain Y n τ) =
      SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertLeft (SingularHomology.zeroSimplexValue σ)).comp τ) := by
  rw [SingularHomology.crossProductZeroLeft_simplex_left, SingularChains.inducedChain_simplex]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a right `0`-simplex generator, `crossProductZeroRight` inserts the point
`zeroSimplexValue τ`. -/
@[simp]
theorem SingularHomology.crossProductZeroRight_simplex_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (c : SingularChains.Chains X n)
    (τ : SingularChains.SingularSimplex Y 0) :
    crossProductZeroRight X Y n c (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (SingularHomology.crossInsertRight (zeroSimplexValue τ)) n c := by
  have h :
    integerBilinearRightApply (crossProductZeroRight X Y n) (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (SingularHomology.crossInsertRight (zeroSimplexValue τ)) n := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp only [SingularHomology.integerBilinearRightApply_apply, SingularHomology.crossProductZeroRight, SingularHomology.chainBilinearLift_simplex,
      SingularChains.inducedChain_simplex]
  exact LinearMap.congr_fun h c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplex generators, `crossProductZeroRight` sends `σ, τ` to the chain of
`σ` composed with `crossInsertRight (zeroSimplexValue τ)`. -/
@[simp]
theorem SingularHomology.crossProductZeroRight_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X n)
    (τ : SingularChains.SingularSimplex Y 0) :
    SingularHomology.crossProductZeroRight X Y n (SingularChains.simplexChain X n σ)
        (SingularChains.simplexChain Y 0 τ) =
      SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertRight (zeroSimplexValue τ)).comp σ) := by
  rw [crossProductZeroRight_simplex_right, SingularChains.inducedChain_simplex]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductZeroLeft` is natural in both space maps. -/
theorem SingularHomology.crossProductZeroLeft_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : SingularChains.Chains X 0)
    (b : SingularChains.Chains Y n) :
    SingularChains.inducedChain (f.prodMap g) n (SingularHomology.crossProductZeroLeft X Y n a b) =
      SingularHomology.crossProductZeroLeft X' Y' n (SingularChains.inducedChain f 0 a)
        (SingularChains.inducedChain g n b) := by
  have h :
    (SingularChains.inducedChain (f.prodMap g) n).comp
        (SingularHomology.integerBilinearRightApply (SingularHomology.crossProductZeroLeft X Y n) b) =
      (SingularHomology.integerBilinearRightApply (SingularHomology.crossProductZeroLeft X' Y' n)
            (SingularChains.inducedChain g n b)).comp
        (SingularChains.inducedChain f 0) := by
    apply SingularChains.chainMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, SingularHomology.integerBilinearRightApply_apply,
      SingularChains.inducedChain_simplex, SingularHomology.crossProductZeroLeft_simplex_left,
      SingularHomology.zeroSimplexValue_comp]
    exact SingularHomology.inducedChain_crossInsertLeft f g (SingularHomology.zeroSimplexValue σ) n b
  exact LinearMap.congr_fun h a


/-! ### The chain-level cross product in left degree one -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product `Chains X 1 →ₗ Chains Y n →ₗ Chains (X × Y) (n + 1)`: on
generators, the `σ × τ` image of the affine prism triangulation of
`Simplex 1 × Simplex n`. -/
def SingularHomology.crossProductEdge (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) :=
  SingularHomology.chainBilinearLift X Y 1 n fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) (n + 1)
      (SingularHomology.productAffineChainMap 1 n (n + 1)
        (SingularHomology.formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplex generators, `crossProductEdge` is the induced chain of the product
affine prism chain. -/
@[simp]
theorem SingularHomology.crossProductEdge_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 1)
    (τ : SingularChains.SingularSimplex Y n) :
    SingularHomology.crossProductEdge X Y n (SingularChains.simplexChain X 1 σ) (SingularChains.simplexChain Y n τ) =
      SingularChains.inducedChain (σ.prodMap τ) (n + 1)
        (SingularHomology.productAffineChainMap 1 n (n + 1)
          (SingularHomology.formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  SingularHomology.chainBilinearLift_simplex X Y 1 n _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductEdge` is natural in both space maps. -/
theorem SingularHomology.crossProductEdge_natural {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (n : ℕ) (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y n) :
    SingularChains.inducedChain (f.prodMap g) (n + 1) (SingularHomology.crossProductEdge X Y n a b) =
      SingularHomology.crossProductEdge X' Y' n (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g n b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductEdge X Y n)
        (SingularChains.inducedChain (f.prodMap g) (n + 1)) =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductEdge X' Y' n) (SingularChains.inducedChain f 1)
        (SingularChains.inducedChain g n) := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 n
    intro σ τ
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, SingularHomology.crossProductEdge_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The affine simplex on the standard vertices is the identity inclusion of the
simplex into its affine span image. -/
theorem SingularHomology.affineSimplex_stdVertices_image {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    SingularMayerVietoris.affineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact SingularMayerVietoris.affineSimplex_vertex v i

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If all left vertices of `v` are the same point `a`, the product affine simplex is
constant in the left factor. -/
theorem SingularHomology.productAffineSimplex_point_left {n p q : ℕ}
    (a : SingularChains.Simplex p) (v : Fin (n + 1) → SingularChains.Simplex q) :
    SingularHomology.productAffineSimplex (fun i => (a, v i)) =
      (SingularHomology.crossInsertLeft a).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [SingularHomology.productAffineSimplex, SingularHomology.affineSimplex_constant]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If all right vertices of `v` are the same point `b`, the product affine simplex is
constant in the right factor. -/
theorem SingularHomology.productAffineSimplex_point_right {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (b : SingularChains.Simplex q) :
    productAffineSimplex (fun i => (v i, b)) =
      (SingularHomology.crossInsertRight b).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductZeroLeft` computed on a left `0`-chain and a formal affine chain `b`
is the induced chain of the point-insertion affine chain map. -/
theorem SingularHomology.crossProductZeroLeft_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 1)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 1)) :
    SingularHomology.crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 0 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      SingularHomology.productAffineChainMap p q n (SingularHomology.formalPointCrossProduct n a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 0) (SingularMayerVietoris.affineChainMap q n) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalPointCrossProduct n) (SingularHomology.productAffineChainMap p q n) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.crossProductZeroLeft_simplex]
    have hv : SingularHomology.zeroSimplexValue (SingularMayerVietoris.affineSimplex v) = v 0 :=
      SingularMayerVietoris.affineSimplex_vertex v 0
    rw [hv]
    calc
      _ =
          SingularHomology.productAffineChainMap p q n
            (SingularMayerVietoris.formalSimplex (fun i => (v 0, w i))) := by
        rw [SingularHomology.productAffineChainMap_simplex, SingularHomology.productAffineSimplex_point_left]
      _ = _ := congrArg (SingularHomology.productAffineChainMap p q n) (SingularHomology.formalPointCrossProduct_simplex n v w).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductEdge` computed on an edge chain `a` and a formal chain `b` equals the
induced chain of the edge cross product on formal chains. -/
theorem SingularHomology.crossProductEdge_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 1)) :
    SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      SingularHomology.productAffineChainMap p q (n + 1) (SingularHomology.formalEdgeCrossProduct n a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q n) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalEdgeCrossProduct n) (SingularHomology.productAffineChainMap p q (n + 1)) :=
    by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.crossProductEdge_simplex]
    rw [SingularHomology.inducedChain_productAffineChainMap]
    change
      SingularHomology.productAffineChainMap p q (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            (n + 2)
            (SingularHomology.formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b


/-! ### The chain-level cross product in left degree two -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product `Chains X 2 →ₗ Chains Y n →ₗ Chains (X × Y) (n + 2)`: on
generators, the `σ × τ` image of the affine prism triangulation of
`Simplex 2 × Simplex n`. -/
def SingularHomology.crossProductTriangle (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 2) :=
  SingularHomology.chainBilinearLift X Y 2 n fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) (n + 2)
      (SingularHomology.productAffineChainMap 2 n (n + 2)
        (SingularHomology.formalTriangleCrossProduct n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplex generators, `crossProductTriangle` is the induced chain of the product
affine prism chain. -/
@[simp]
theorem SingularHomology.crossProductTriangle_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 2)
    (τ : SingularChains.SingularSimplex Y n) :
    SingularHomology.crossProductTriangle X Y n (SingularChains.simplexChain X 2 σ)
        (SingularChains.simplexChain Y n τ) =
      SingularChains.inducedChain (σ.prodMap τ) (n + 2)
        (SingularHomology.productAffineChainMap 2 n (n + 2)
          (SingularHomology.formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  SingularHomology.chainBilinearLift_simplex X Y 2 n _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductTriangle` is natural in both space maps. -/
theorem SingularHomology.crossProductTriangle_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y n) :
    SingularChains.inducedChain (f.prodMap g) (n + 2) (SingularHomology.crossProductTriangle X Y n a b) =
      SingularHomology.crossProductTriangle X' Y' n (SingularChains.inducedChain f 2 a)
        (SingularChains.inducedChain g n b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductTriangle X Y n)
        (SingularChains.inducedChain (f.prodMap g) (n + 2)) =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductTriangle X' Y' n) (SingularChains.inducedChain f 2)
        (SingularChains.inducedChain g n) := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 n
    intro σ τ
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, SingularHomology.crossProductTriangle_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductTriangle` computed on a triangle chain `a` and formal chain `b`
equals the induced chain of the formal triangle cross product. -/
theorem SingularHomology.crossProductTriangle_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 1)) :
    SingularHomology.crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      SingularHomology.productAffineChainMap p q (n + 2) (SingularHomology.formalTriangleCrossProduct n a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q n) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalTriangleCrossProduct n)
        (SingularHomology.productAffineChainMap p q (n + 2)) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.crossProductTriangle_simplex]
    rw [SingularHomology.inducedChain_productAffineChainMap]
    change
      SingularHomology.productAffineChainMap p q (n + 2)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            (n + 3)
            (SingularHomology.formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.formalMap_triangleCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-! ### The Leibniz rule -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductTriangle a b` at right degree `0` on formal chains is
`crossProductEdge` of `∂a` and `b`. -/
theorem SingularHomology.crossProductTriangle_boundary_zero_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 1) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 2
            1).hom
        (SingularHomology.crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) 0
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q 0 b)) =
      SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) 0
        (((SingularChains.singularComplex (SingularChains.Simplex p)).d 2 1).hom
          (SingularMayerVietoris.affineChainMap p 2 a))
        (SingularMayerVietoris.affineChainMap q 0 b) := by
  rw [SingularHomology.crossProductTriangle_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularHomology.formalBoundary_triangleCrossProduct_zero, SingularMayerVietoris.affineChainMap_boundary,
    SingularHomology.crossProductEdge_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On formal chains, the boundary of the triangle cross product satisfies
`∂(a × b) = ∂a × b + a × ∂b`. -/
theorem SingularHomology.crossProductTriangle_boundary_affine (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 3)
            (n + 2)).hom
        (SingularHomology.crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q (n + 1) b)) =
      SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d 2 1).hom
            (SingularMayerVietoris.affineChainMap p 2 a))
          (SingularMayerVietoris.affineChainMap q (n + 1) b) +
        SingularHomology.crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) n
          (SingularMayerVietoris.affineChainMap p 2 a)
          (((SingularChains.singularComplex (SingularChains.Simplex q)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap q (n + 1) b)) := by
  rw [SingularHomology.crossProductTriangle_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularHomology.formalBoundary_triangleCrossProduct, map_add, SingularMayerVietoris.affineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, SingularHomology.crossProductEdge_affineChainMap,
    SingularHomology.crossProductTriangle_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductTriangle a b` when `b` is a `0`-chain is
`crossProductEdge` of `∂a` and `b`. -/
theorem SingularHomology.crossProductTriangle_boundary_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y 0) :
    ((SingularChains.singularComplex (X × Y)).d 2 1).hom (SingularHomology.crossProductTriangle X Y 0 a b) =
      SingularHomology.crossProductEdge X Y 0 (((SingularChains.singularComplex X).d 2 1).hom a) b := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductTriangle X Y 0)
        ((SingularChains.singularComplex (X × Y)).d 2 1).hom =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductEdge X Y 0)
        ((SingularChains.singularComplex X).d 2 1).hom LinearMap.id := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 0
    intro σ τ
    have hstd :=
      SingularHomology.crossProductTriangle_boundary_zero_affine 2 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 1) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      LinearMap.id_apply, SingularChains.inducedChain_boundary, SingularHomology.crossProductTriangle_natural,
      SingularHomology.crossProductEdge_natural, SingularMayerVietoris.affineChainMap_stdVertices,
      SingularChains.inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary law for `crossProductTriangle`: `∂(a × b) = ∂a × b + a × ∂b`,
where the `∂a`-term uses `crossProductEdge` (the left degree drops) and the `∂b`-term
uses `crossProductTriangle` at degree `n - 1`. -/
theorem SingularHomology.crossProductTriangle_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y (n + 1)) :
    ((SingularChains.singularComplex (X × Y)).d (n + 3) (n + 2)).hom
        (SingularHomology.crossProductTriangle X Y (n + 1) a b) =
      SingularHomology.crossProductEdge X Y (n + 1) (((SingularChains.singularComplex X).d 2 1).hom a) b +
        SingularHomology.crossProductTriangle X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductTriangle X Y (n + 1))
        ((SingularChains.singularComplex (X × Y)).d (n + 3) (n + 2)).hom =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductEdge X Y (n + 1))
          ((SingularChains.singularComplex X).d 2 1).hom LinearMap.id +
        SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductTriangle X Y n) LinearMap.id
          ((SingularChains.singularComplex Y).d (n + 1) n).hom := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 (n + 1)
    intro σ τ
    have hstd :=
      SingularHomology.crossProductTriangle_boundary_affine 2 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) (n + 2)) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, SingularChains.inducedChain_boundary,
      SingularHomology.crossProductTriangle_natural, SingularHomology.crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If `b` is a cycle, `∂(a × b) = ∂a × b` for the triangle cross product. -/
theorem SingularHomology.crossProductTriangle_boundary_of_right_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y n)
    (hb : ((SingularChains.singularComplex Y).d n (n - 1)).hom b = 0) :
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (SingularHomology.crossProductTriangle X Y n a b) =
      SingularHomology.crossProductEdge X Y n (((SingularChains.singularComplex X).d 2 1).hom a) b := by
  cases n with
  | zero => exact SingularHomology.crossProductTriangle_boundary_zero a b
  | succ
    n =>
    have hb' : ((SingularChains.singularComplex Y).d (n + 1) n).hom b = 0 := by
      simpa only [Nat.succ_sub_one] using hb
    simp only [SingularHomology.crossProductTriangle_boundary, hb', map_zero, add_zero]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductEdge a b` at right degree `0` on formal chains is the
point cross product of `∂a`. -/
theorem SingularHomology.crossProductEdge_boundary_zero_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 1) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 1
            0).hom
        (SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) 0
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 0 b)) =
      SingularHomology.crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) 0
        (((SingularChains.singularComplex (SingularChains.Simplex p)).d 1 0).hom
          (SingularMayerVietoris.affineChainMap p 1 a))
        (SingularMayerVietoris.affineChainMap q 0 b) := by
  rw [SingularHomology.crossProductEdge_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularHomology.formalBoundary_edgeCrossProduct_zero, SingularMayerVietoris.affineChainMap_boundary,
    SingularHomology.crossProductZeroLeft_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On formal chains, the boundary of the edge cross product satisfies
`∂(a × b) = ∂a × b - a × ∂b`. -/
theorem SingularHomology.crossProductEdge_boundary_affine (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 2)
            (n + 1)).hom
        (SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q (n + 1) b)) =
      SingularHomology.crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d 1 0).hom
            (SingularMayerVietoris.affineChainMap p 1 a))
          (SingularMayerVietoris.affineChainMap q (n + 1) b) -
        SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) n
          (SingularMayerVietoris.affineChainMap p 1 a)
          (((SingularChains.singularComplex (SingularChains.Simplex q)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap q (n + 1) b)) := by
  rw [SingularHomology.crossProductEdge_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularHomology.formalBoundary_edgeCrossProduct, map_sub, SingularMayerVietoris.affineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, SingularHomology.crossProductZeroLeft_affineChainMap,
    SingularHomology.crossProductEdge_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductEdge a b` when `b` is a `0`-chain is
`crossProductZeroLeft` of `∂a` and `b`. -/
theorem SingularHomology.crossProductEdge_boundary_zero {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 0) :
    ((SingularChains.singularComplex (X × Y)).d 1 0).hom (SingularHomology.crossProductEdge X Y 0 a b) =
      SingularHomology.crossProductZeroLeft X Y 0 (((SingularChains.singularComplex X).d 1 0).hom a) b := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductEdge X Y 0)
        ((SingularChains.singularComplex (X × Y)).d 1 0).hom =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductZeroLeft X Y 0)
        ((SingularChains.singularComplex X).d 1 0).hom LinearMap.id := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 0
    intro σ τ
    have hstd :=
      SingularHomology.crossProductEdge_boundary_zero_affine 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 0) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      LinearMap.id_apply, SingularChains.inducedChain_boundary, SingularHomology.crossProductEdge_natural,
      SingularHomology.crossProductZeroLeft_natural, SingularMayerVietoris.affineChainMap_stdVertices,
      SingularChains.inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary law for `crossProductEdge`: `∂(a × b) = ∂a × b - a × ∂b`, where the
`∂a`-term uses `crossProductZeroLeft` (the left degree drops to `0`) and the `∂b`-term
uses `crossProductEdge` at degree `n - 1`. -/
theorem SingularHomology.crossProductEdge_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y (n + 1)) :
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (SingularHomology.crossProductEdge X Y (n + 1) a b) =
      SingularHomology.crossProductZeroLeft X Y (n + 1) (((SingularChains.singularComplex X).d 1 0).hom a) b -
        SingularHomology.crossProductEdge X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductEdge X Y (n + 1))
        ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom =
      SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductZeroLeft X Y (n + 1))
          ((SingularChains.singularComplex X).d 1 0).hom LinearMap.id -
        SingularHomology.integerBilinearPrecompose (SingularHomology.crossProductEdge X Y n) LinearMap.id
          ((SingularChains.singularComplex Y).d (n + 1) n).hom := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 (n + 1)
    intro σ τ
    have hstd :=
      SingularHomology.crossProductEdge_boundary_affine 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) (n + 1)) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_sub, SingularChains.inducedChain_boundary,
      SingularHomology.crossProductEdge_natural, SingularHomology.crossProductZeroLeft_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If `b` is a cycle, `∂(a × b) = ∂a × b` for the edge cross product. -/
theorem SingularHomology.crossProductEdge_cycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y n)
    (ha : ((SingularChains.singularComplex X).d 1 0).hom a = 0)
    (hb : ((SingularChains.singularComplex Y).d n (n - 1)).hom b = 0) :
    ((SingularChains.singularComplex (X × Y)).d (n + 1) n).hom (SingularHomology.crossProductEdge X Y n a b) = 0 := by
  cases n with
  | zero =>
    have h := SingularHomology.crossProductEdge_boundary_zero a b
    rw [ha, map_zero, LinearMap.zero_apply] at h
    exact h
  | succ
    n =>
    have hb' : ((SingularChains.singularComplex Y).d (n + 1) n).hom b = 0 := by
      simpa only [Nat.succ_sub_one] using hb
    simp only [SingularHomology.crossProductEdge_boundary, ha, hb', map_zero, LinearMap.zero_apply, sub_self]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If `a` is a `1`-cycle, `∂(a × b) = -a × ∂b` for the edge cross product. -/
theorem SingularHomology.crossProductEdge_boundary_of_left_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1)
    (ha : ((SingularChains.singularComplex X).d 1 0).hom a = 0)
    (b : SingularChains.Chains Y (n + 1)) :
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (SingularHomology.crossProductEdge X Y (n + 1) a b) =
      -SingularHomology.crossProductEdge X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  simp only [SingularHomology.crossProductEdge_boundary, ha, map_zero, LinearMap.zero_apply, zero_sub]
