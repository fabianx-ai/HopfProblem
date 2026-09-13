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

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# The singular cross product

For topological spaces `X` and `Y`, the cross product of singular chains over `ℤ` and the
induced bilinear map on homology:

* `SingularHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
  [TopologicalSpace Y] (n : ℕ) :
  (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
  (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
  (SingularChains.singularComplex (X × Y)).homology (n + 1)`.

(The cross-product declarations use the general `SingularHomology` namespace. Historical
`PeriodTorusHigherHomology` names are available only through the project compatibility shims.)

## Outline of the construction

This is Hatcher's §3.B construction, specialized to left degree one (with left degree two for
the prism side condition), in five steps.

1. *Bilinear plumbing.* `SingularHomology.integerBilinearRightApply`, `SingularHomology.integerBilinearFlip`,
   `SingularHomology.integerBilinearPostcompose`, `SingularHomology.integerBilinearPrecompose` package currying and composition
   of bilinear maps over `ℤ`; `SingularHomology.chainBilinearLift` extends a simplex-wise bilinear assignment
   to the free abelian chain groups (`SingularHomology.chainBilinearMap_ext` for uniqueness).
2. *The formal product.* `SingularHomology.formalEdgeCrossProduct` triangulates the prism `Δ¹ × Δⁿ` (and
   `SingularHomology.formalTriangleCrossProduct` the product `Δ² × Δⁿ`) into affine simplices, with the Leibniz
   boundary identities `SingularHomology.formalBoundary_edgeCrossProduct`,
   `SingularHomology.formalBoundary_triangleCrossProduct`; `SingularHomology.formalPointCrossProduct` is the degree-zero
   companion.
3. *The chain-level product.* `SingularHomology.crossProductEdge` sends a singular edge and a singular
   `n`-simplex to the product chain pushed forward along `σ.prodMap τ`
   (`SingularHomology.crossProductEdge_simplex`); it is natural (`SingularHomology.crossProductEdge_natural`) and satisfies the
   Leibniz rule `SingularHomology.crossProductEdge_boundary`; likewise `SingularHomology.crossProductTriangle` in left degree
   two, which is the prism operator for the homotopy-invariance arguments of the Hurewicz
   lane.
4. *Descent to homology.* A cycle times a cycle is a cycle (`SingularHomology.crossProductCycles`); a boundary
   times a cycle is a boundary (`SingularHomology.crossProductCycleClasses_boundary_right`,
   `SingularHomology.crossProductHomologyCycles_boundary_left`), so the product descends twice
   (`SingularHomology.crossProductHomologyFixed`, `SingularHomology.crossProductHomologyCycles`, then `SingularHomology.homologyDesc`) to
   `SingularHomology.crossProductHomology`, with `SingularHomology.crossProductHomology_cycleClass` computing it on classes.
5. *Degenerations at `n = 0`.* `SingularHomology.crossProductEdge_zero_eq_zeroRight` identifies the
   degree-zero product with point insertion, and
   `SingularHomology.crossProductHomology_pointClass_right` computes it on point classes.

## Main definitions and results

* `SingularHomology.crossProductEdge`, `.crossProductTriangle` : the chain-level
  cross products in left degrees 1 and 2.
* `SingularHomology.crossProductHomology` : the homology-level cross product
  `H₁(X) →ₗ[ℤ] Hₙ(Y) →ₗ[ℤ] H_{n+1}(X × Y)`.
* `SingularHomology.integerLinearMapModule`, `.integerTensorModule` :
  `@[instance_reducible]` `Module ℤ` instances on `A →ₗ[ℤ] B` and `A ⊗[ℤ] B`, used as local
  instances throughout this file: they pin the diamond between Mathlib's two instances and
  the one the product constructions elaborate against. A disposable removal of the local instance wrappers fails at scalar-action
  elaboration in `integerBilinearRightApply`, `integerBilinearFlip`,
  `integerBilinearPostcompose` and `crossProductHomologyCycles`; the instances are
  retained.
* Consumers: the Hurewicz lane (the fundamental cube chain by recursion on degree), the torus
  lane (the section of the circle-splitting sequence), the Pontryagin product (the addition
  pushforward of this product).

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.B

## Tags

singular homology, cross product, Künneth
-/


@[expose] public noncomputable section

namespace Mathoverflow1973

/-! ### ℤ-module instances on linear maps and tensor products -/

/-- The `ℤ`-module structure on `A →ₗ[ℤ] B` used in this file, pinning the elaboration
diamond between Mathlib's instances and the one the product constructions need. -/
@[instance_reducible]
def SingularHomology.integerLinearMapModule {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A →ₗ[ℤ] B) :=
  @LinearMap.module ℤ ℤ ℤ A B _ _ _ _ modA modB (RingHom.id ℤ) _ modB
    (@smulCommClass_self ℤ B _ modB.toMulAction)

attribute [local instance] SingularHomology.integerLinearMapModule in
/-- The `ℤ`-module structure on `A ⊗[ℤ] B` used in this file, pinning the elaboration
diamond against Mathlib's instances. -/
@[instance_reducible]
def SingularHomology.integerTensorModule {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A ⊗[ℤ] B) :=
  @TensorProduct.instModule ℤ _ A B _ _ modA modB

/-! ### Bilinear plumbing -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Evaluation of a bilinear map `F : A →ₗ[ℤ] B →ₗ[ℤ] C` at a right argument `b`, as a
linear map `A →ₗ[ℤ] C`. -/
def SingularHomology.integerBilinearRightApply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) : A →ₗ[ℤ] C
    where
  toFun a := F a b
  map_add' a a' := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_add a a')
  map_smul' r a := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_smul r a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `integerBilinearRightApply F b` applied to `a` is `F a b`. -/
@[simp]
theorem SingularHomology.integerBilinearRightApply_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : SingularHomology.integerBilinearRightApply F b a = F a b :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The flip of a bilinear map: `integerBilinearFlip F b a = F a b`, as a bilinear map
`B →ₗ[ℤ] A →ₗ[ℤ] C`. -/
def SingularHomology.integerBilinearFlip {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) : B →ₗ[ℤ] A →ₗ[ℤ] C
    where
  toFun := SingularHomology.integerBilinearRightApply F
  map_add' b
    b' := by
    apply LinearMap.ext
    intro a
    exact (F a).map_add b b'
  map_smul' r
    b := by
    apply LinearMap.ext
    intro a
    exact (F a).map_smul r b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `integerBilinearFlip F b a = F a b`. -/
@[simp]
theorem SingularHomology.integerBilinearFlip_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : SingularHomology.integerBilinearFlip F b a = F a b :=
  rfl

/-! ### Extending simplex-wise bilinear maps to chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The bilinear lift of a simplex-wise function `f σ τ` to a bilinear map on chain
groups `Chains X p →ₗ[ℤ] Chains Y q →ₗ[ℤ] M`. -/
def SingularHomology.chainBilinearLift (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : SingularChains.SingularSimplex X p → SingularChains.SingularSimplex Y q → M) :
    SingularChains.Chains X p →ₗ[ℤ] SingularChains.Chains Y q →ₗ[ℤ] M :=
  SingularChains.chainLift X p fun σ => SingularChains.chainLift Y q (f σ)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a left generator simplex, `chainBilinearLift f` applied to `simplexChain σ` is
the chain lift of `f σ`. -/
@[simp]
theorem SingularHomology.chainBilinearLift_simplex_left (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : SingularChains.SingularSimplex X p → SingularChains.SingularSimplex Y q → M)
    (σ : SingularChains.SingularSimplex X p) :
    SingularHomology.chainBilinearLift X Y p q f (SingularChains.simplexChain X p σ) =
      SingularChains.chainLift Y q (f σ) :=
  SingularChains.chainLift_simplex X p _ σ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On generator simplices, `chainBilinearLift f (simplexChain σ) (simplexChain τ) =
f σ τ`. -/
@[simp]
theorem SingularHomology.chainBilinearLift_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : SingularChains.SingularSimplex X p → SingularChains.SingularSimplex Y q → M)
    (σ : SingularChains.SingularSimplex X p) (τ : SingularChains.SingularSimplex Y q) :
    SingularHomology.chainBilinearLift X Y p q f (SingularChains.simplexChain X p σ)
        (SingularChains.simplexChain Y q τ) =
      f σ τ := by rw [SingularHomology.chainBilinearLift_simplex_left, SingularChains.chainLift_simplex]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Two bilinear maps on singular chains that agree on all generator simplex pairs are
equal. -/
theorem SingularHomology.chainBilinearMap_ext (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    {F G : SingularChains.Chains X p →ₗ[ℤ] SingularChains.Chains Y q →ₗ[ℤ] M}
    (h :
      ∀ σ τ,
        F (SingularChains.simplexChain X p σ) (SingularChains.simplexChain Y q τ) =
          G (SingularChains.simplexChain X p σ) (SingularChains.simplexChain Y q τ)) :
    F = G := by
  apply SingularChains.chainMap_ext X p
  intro σ
  apply SingularChains.chainMap_ext Y q
  intro τ
  exact h σ τ

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

/-! ### Composition of bilinear maps -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Postcomposition of a bilinear map `F : A →ₗ B →ₗ C` with a linear map `C →ₗ D`. -/
def SingularHomology.integerBilinearPostcompose {A B C D : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ D] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) : A →ₗ[ℤ] B →ₗ[ℤ] D
    where
  toFun a := g.comp (F a)
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    exact
      (congrArg (fun l : B →ₗ[ℤ] C => g (l b)) (F.map_add a a')).trans
        (g.map_add (F a b) (F a' b))
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    exact (congrArg (fun l : B →ₗ[ℤ] C => g (l b)) (F.map_smul r a)).trans (g.map_smul r (F a b))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `integerBilinearPostcompose F g a b = g (F a b)`. -/
@[simp]
theorem SingularHomology.integerBilinearPostcompose_apply {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) (a : A) (b : B) :
    SingularHomology.integerBilinearPostcompose F g a b = g (F a b) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Precomposition of a bilinear map `F : A →ₗ B →ₗ C` with linear maps `A' →ₗ A` and
`B' →ₗ B`. -/
def SingularHomology.integerBilinearPrecompose {A B C A' B' : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B'] [Module ℤ A]
    [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) : A' →ₗ[ℤ] B' →ₗ[ℤ] C
    where
  toFun a := (F (f a)).comp g
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    exact
      (congrArg (fun x => F x (g b)) (f.map_add a a')).trans
        (congrArg (fun l : B →ₗ[ℤ] C => l (g b)) (F.map_add (f a) (f a')))
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    exact
      (congrArg (fun x => F x (g b)) (f.map_smul r a)).trans
        (congrArg (fun l : B →ₗ[ℤ] C => l (g b)) (F.map_smul r (f a)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `integerBilinearPrecompose F f g a' b' = F (f a') (g b')`. -/
@[simp]
theorem SingularHomology.integerBilinearPrecompose_apply {A B C A' B' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B']
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) (a : A') (b : B') :
    SingularHomology.integerBilinearPrecompose F f g a b = F (f a) (g b) :=
  rfl

/-! ### The bilinear lift on formal chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Two bilinear maps on formal chains that agree on generator pairs are equal. -/
theorem SingularHomology.integerFormalBilinearMap_ext (V W : Type*) (p q : ℕ) {M : Type*}
    [AddCommGroup M] [Module ℤ M]
    {F G :
      SingularMayerVietoris.FormalChains V p →ₗ[ℤ] SingularMayerVietoris.FormalChains W q →ₗ[ℤ] M}
    (h :
      ∀ v w,
        F (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w) =
          G (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)) :
    F = G := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply SingularMayerVietoris.formalChains_ext
  intro w
  exact h v w

/-- Extensionality for bilinear maps out of `FormalChains V n` and
`FormalChains W m`: equality on simplex generators suffices. -/
theorem SingularHomology.formalChains_bilinear_ext {V W M : Type*} {n m : ℕ}
    [AddCommGroup M] [Module ℤ M]
    {f g :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ] SingularMayerVietoris.FormalChains W m →ₗ[ℤ] M}
    (h :
      ∀ v w,
        f (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w) =
          g (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)) :
    f = g := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply SingularMayerVietoris.formalChains_ext
  exact h v

/-- The bilinear lift of a generator-wise map to formal chains in both arguments. -/
def SingularHomology.formalBilinearLift {V W M : Type*} {n m : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ] SingularMayerVietoris.FormalChains W m →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => SingularMayerVietoris.formalLift (f v)

/-- `formalBilinearLift` evaluated on simplex generators returns the defining value. -/
@[simp]
theorem SingularHomology.formalBilinearLift_simplex {V W M : Type*} {n m : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → M) (v : Fin n → V)
    (w : Fin m → W) :
    SingularHomology.formalBilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      f v w := by simp [SingularHomology.formalBilinearLift]

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

/-! ### Affine simplices in a product -/

/-- The affine simplex on a constant vertex list is the constant map. -/
@[simp]
theorem SingularHomology.affineSimplex_constant {n p : ℕ} (a : SingularChains.Simplex p) :
    SingularMayerVietoris.affineSimplex (fun _ : Fin (n + 1) => a) =
      ContinuousMap.const (SingularChains.Simplex n) a := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (∑ i, t i • (a : Fin (p + 1) → ℝ)) = (a : Fin (p + 1) → ℝ)
  rw [← Finset.sum_smul, stdSimplex.sum_eq_one t, one_smul]

/-- The affine simplex in `Simplex p × Simplex q` with vertex pairs `v`, formed
componentwise. -/
def SingularHomology.productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    C(SingularChains.Simplex n, SingularChains.Simplex p × SingularChains.Simplex q) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (SingularMayerVietoris.affineSimplex (fun i => (v i).2))

/-- The `j`-th vertex of `productAffineSimplex v` is the pair `v j`. -/
@[simp]
theorem SingularHomology.productAffineSimplex_vertex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) (i : Fin (n + 1)) :
    SingularHomology.productAffineSimplex v (SingularMayerVietoris.stdVertices n i) = v i := by
  apply Prod.ext <;> simp [SingularHomology.productAffineSimplex, SingularMayerVietoris.stdVertices]

/-- The `i`-th face of `productAffineSimplex v` is the product affine simplex of the
vertex pairs with `v i` dropped. -/
theorem SingularHomology.productAffineSimplex_face {n p q : ℕ}
    (v : Fin (n + 2) → SingularChains.Simplex p × SingularChains.Simplex q) (i : Fin (n + 2)) :
    (SingularHomology.productAffineSimplex v).comp (SingularChains.simplexFace n i) =
      SingularHomology.productAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex q) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).2) i)

/-- Postcomposing `productAffineSimplex v` with a product map gives the product affine
simplex of the mapped vertex pairs. -/
theorem SingularHomology.prodMap_productAffineSimplex {m p q r s : ℕ}
    (v : Fin (p + 1) → SingularChains.Simplex r) (w : Fin (q + 1) → SingularChains.Simplex s)
    (z : Fin (m + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    ((SingularMayerVietoris.affineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w)).comp
        (SingularHomology.productAffineSimplex z) =
      SingularHomology.productAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (z j).1,
            SingularMayerVietoris.affineSimplex w (z j).2)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex s) => f t)
        (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))

/-- The formal-chain map sending a vertex-pair list to the chain of its product affine
simplex. -/
def SingularHomology.productAffineChainMap (p q n : ℕ) :
    SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 1) →ₗ[ℤ]
      SingularChains.Chains (SingularChains.Simplex p × SingularChains.Simplex q) n :=
  SingularMayerVietoris.formalLift fun v =>
    SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
      (SingularHomology.productAffineSimplex v)

/-- `productAffineChainMap` on a generator `v` is the chain of `productAffineSimplex v`. -/
@[simp]
theorem SingularHomology.productAffineChainMap_simplex (p q n : ℕ)
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    SingularHomology.productAffineChainMap p q n (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
        (SingularHomology.productAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

/-- The product affine chain map commutes with the formal boundary: `∂` of the affine
chain is the alternating sum of the face affine simplices. -/
theorem SingularHomology.productAffineChainMap_boundary (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 1)
            n).hom
        (SingularHomology.productAffineChainMap p q (n + 1) c) =
      SingularHomology.productAffineChainMap p q n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d
              (n + 1) n).hom).comp
        (SingularHomology.productAffineChainMap p q (n + 1)) =
      (SingularHomology.productAffineChainMap p q n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d
              (n + 1) n).hom
          (SingularHomology.productAffineChainMap p q (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [SingularHomology.productAffineChainMap_simplex, SingularChains.boundary_simplex]
    change
      _ =
        SingularHomology.productAffineChainMap p q n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, SingularHomology.productAffineChainMap_simplex, SingularHomology.productAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- Postcomposing the product affine chain map with the map induced by a product of
continuous maps gives the product affine chain map of the mapped vertices. -/
theorem SingularHomology.inducedChain_productAffineChainMap {m p q r s : ℕ}
    (v : Fin (p + 1) → SingularChains.Simplex r) (w : Fin (q + 1) → SingularChains.Simplex s)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (m + 1)) :
    SingularChains.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))
        m (SingularHomology.productAffineChainMap p q m c) =
      SingularHomology.productAffineChainMap r s m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1) c) := by
  have h :
    (SingularChains.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              (SingularMayerVietoris.affineSimplex w))
            m).comp
        (SingularHomology.productAffineChainMap p q m) =
      (SingularHomology.productAffineChainMap r s m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      SingularHomology.prodMap_productAffineSimplex]
    rfl
  exact LinearMap.congr_fun h c

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

/-! ### Descent to homology -/

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- The submodule of degree-`n` cycles of `K` consisting of boundaries, as a submodule
of the cycle module. -/
abbrev SingularHomology.homologyBoundaries (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) : Submodule ℤ (SingularMayerVietoris.ModuleHomology.Cycle K n) :=
  SingularChains.ChainHomology.ShortBoundaries (K.sc n)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- Two linear maps out of `K.homology n` agreeing on all cycle classes are equal. -/
theorem SingularHomology.homologyLinearMap_ext (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M] {f g : K.homology n →ₗ[ℤ] M}
    (h :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
        f (SingularMayerVietoris.ModuleHomology.cycleClass K n c) =
          g (SingularMayerVietoris.ModuleHomology.cycleClass K n c)) :
    f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n x
  exact h c

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- If `f` vanishes on every boundary cycle, the boundary submodule is contained in
the kernel of `f`. -/
theorem SingularHomology.homologyBoundaries_le_ker (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    SingularHomology.homologyBoundaries K n ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : SingularMayerVietoris.ModuleHomology.cycleClass K n c = 0 :=
    (SingularChains.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).mpr
      ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff K n c).mp hc
  have he : SingularMayerVietoris.ModuleHomology.boundaryCycle K n b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- A linear map on degree-`n` cycles of `K` vanishing on boundaries descends to a
linear map on `K.homology n`. -/
def SingularHomology.homologyDesc (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    K.homology n →ₗ[ℤ] M :=
  ((SingularHomology.homologyBoundaries K n).liftQ f (SingularHomology.homologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- `homologyDesc f hf` sends the class of a cycle `c` to `f c`. -/
@[simp]
theorem SingularHomology.homologyDesc_cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    SingularHomology.homologyDesc K n f hf (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = f c := by
  have h :=
    congrArg (fun q => q.hom (Submodule.Quotient.mk c)) (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((SingularHomology.homologyBoundaries K n).liftQ f (SingularHomology.homologyBoundaries_le_ker K n f hf)) h

/-! ### The cross product on cycles -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a `1`-cycle in `X` and a cycle in `Y`, landing in cycles of
`X × Y` via `crossProductEdge` (linear in the right argument). -/
def SingularHomology.crossProductCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
        SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (X × Y)) (n + 1)
    where
  toFun
    a :=
    { toFun
        b :=
        SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex (X × Y))
          (n + 1) (SingularHomology.crossProductEdge X Y n a.1 b.1)
          (by
            rw [Nat.add_sub_cancel]
            exact
              SingularHomology.crossProductEdge_cycle n a.1 b.1
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex X) 1 a)
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex Y) n b))
      map_add' b
        c := by
        apply Subtype.ext
        exact (SingularHomology.crossProductEdge X Y n a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (SingularHomology.crossProductEdge X Y n a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) => f c.1)
        ((SingularHomology.crossProductEdge X Y n).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) => f c.1)
        ((SingularHomology.crossProductEdge X Y n).map_smul r a.1)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The underlying chain of `crossProductCycles a b` is `crossProductEdge a.1 b.1`. -/
@[simp]
theorem SingularHomology.crossProductCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    (SingularHomology.crossProductCycles X Y n a b).1 = SingularHomology.crossProductEdge X Y n a.1 b.1 :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a `1`-cycle and a cycle as a map to homology classes of
`X × Y`, linear in the right argument. -/
def SingularHomology.crossProductCycleClasses (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductCycles X Y n)
    (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
      (n + 1))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class-valued edge cross product vanishes when the right chain is a boundary. -/
theorem SingularHomology.crossProductCycleClasses_boundary_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularChains.Chains Y (n + 1)) :
    SingularHomology.crossProductCycleClasses X Y n a
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex Y) n
          b) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨-SingularHomology.crossProductEdge X Y (n + 1) a.1 b, ?_⟩
  change
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (-SingularHomology.crossProductEdge X Y (n + 1) a.1 b) =
      SingularHomology.crossProductEdge X Y n a.1 (((SingularChains.singularComplex Y).d (n + 1) n).hom b)
  rw [map_neg,
    SingularHomology.crossProductEdge_boundary_of_left_cycle n a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 1
        a),
    neg_neg]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a fixed left `1`-cycle `a` with `Y`-homology classes,
descended in the right argument. -/
def SingularHomology.crossProductHomologyFixed {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1) :
    (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
      (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  SingularHomology.homologyDesc (SingularChains.singularComplex Y) n (SingularHomology.crossProductCycleClasses X Y n a)
    (SingularHomology.crossProductCycleClasses_boundary_right n a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductHomologyFixed a` sends the class of a cycle `b` to the class of
`crossProductCycles` on representatives. -/
@[simp]
theorem SingularHomology.crossProductHomologyFixed_cycleClass {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularHomology.crossProductHomologyFixed n a
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (SingularHomology.crossProductCycles X Y n a b) :=
  SingularHomology.homologyDesc_cycleClass _ _ _ _ b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a `1`-cycle in `X` with a cycle in `Y` as a map into
`n + 1`-homology of `X × Y` (descended in the right argument). -/
def SingularHomology.crossProductHomologyCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      ((SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1))
    where
  toFun a := SingularHomology.crossProductHomologyFixed n a
  map_add' a
    b := by
    apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex Y) n
    intro c
    change
      SingularHomology.crossProductHomologyFixed n (a + b)
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
            c) =
        SingularHomology.crossProductHomologyFixed n a
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
              c) +
          SingularHomology.crossProductHomologyFixed n b
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
              c)
    simp only [SingularHomology.crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
              (SingularChains.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((SingularHomology.crossProductCycleClasses X Y n).map_add a b)
  map_smul' r
    a := by
    apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex Y) n
    intro c
    simp only [LinearMap.smul_apply, RingHom.id_apply, SingularHomology.crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
              (SingularChains.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((SingularHomology.crossProductCycleClasses X Y n).map_smul r a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class-valued edge cross product vanishes when the left chain is a boundary. -/
theorem SingularHomology.crossProductCycleClasses_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularHomology.crossProductCycleClasses X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1 a)
        b =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨SingularHomology.crossProductTriangle X Y n a b.1, ?_⟩
  exact
    SingularHomology.crossProductTriangle_boundary_of_right_cycle n a b.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Y) n b)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology-valued edge cross product vanishes when the left `1`-chain is a
boundary. -/
theorem SingularHomology.crossProductHomologyCycles_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2) :
    SingularHomology.crossProductHomologyCycles X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1
          a) =
      0 := by
  apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex Y) n
  intro b
  change
    SingularHomology.crossProductHomologyFixed n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      0
  rw [SingularHomology.crossProductHomologyFixed_cycleClass]
  exact SingularHomology.crossProductCycleClasses_boundary_left n a b

/-! ### The cross product on homology -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology cross product `H_1(X) →ₗ[ℤ] H_n(Y) →ₗ[ℤ] H_{n+1}(X × Y)`. -/
def SingularHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
      (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  SingularHomology.homologyDesc (SingularChains.singularComplex X) 1 (SingularHomology.crossProductHomologyCycles X Y n)
    (SingularHomology.crossProductHomologyCycles_boundary_left n)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductHomology` on cycle classes `⟦a⟧`, `⟦b⟧` is the class of the edge
cross product `a × b`. -/
@[simp]
theorem SingularHomology.crossProductHomology_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularHomology.crossProductHomology X Y n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (SingularHomology.crossProductCycles X Y n a b) := by
  rw [SingularHomology.crossProductHomology, SingularHomology.homologyDesc_cycleClass]
  exact SingularHomology.crossProductHomologyFixed_cycleClass n a b

/-! ### Degenerations at degree zero -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- In right degree `0`, `crossProductEdge` coincides with `crossProductZeroRight`
(up to the degree identification). -/
theorem SingularHomology.crossProductEdge_zero_eq_zeroRight (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    SingularHomology.crossProductEdge X Y 0 = SingularHomology.crossProductZeroRight X Y 1 := by
  apply SingularHomology.chainBilinearMap_ext X Y 1 0
  intro σ τ
  rw [SingularHomology.crossProductEdge_simplex, SingularHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularHomology.productAffineChainMap_simplex,
    SingularChains.inducedChain_simplex, SingularHomology.crossProductZeroRight_simplex]
  apply congrArg (SingularChains.simplexChain (X × Y) 1)
  change
    (σ.prodMap τ).comp
        (SingularHomology.productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 1 i, SingularMayerVietoris.stdVertices 0 0))) =
      (SingularHomology.crossInsertRight (zeroSimplexValue τ)).comp σ
  rw [productAffineSimplex_point_right, SingularMayerVietoris.affineSimplex_stdVertices,
    ContinuousMap.comp_id]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a `0`-simplex right generator, `crossProductEdge` at degree `0` sends
`(σ, τ)` to `σ` composed with the point insertion. -/
theorem SingularHomology.crossProductEdge_zero_simplex_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1)
    (τ : SingularChains.SingularSimplex Y 0) :
    crossProductEdge X Y 0 a (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (SingularHomology.crossInsertRight (zeroSimplexValue τ)) 1 a := by
  rw [crossProductEdge_zero_eq_zeroRight, crossProductZeroRight_simplex_right]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a point `0`-cycle `y`, `crossProductEdge a` agrees with the point-insertion
pushforward of `a`. -/
@[simp]
theorem SingularHomology.crossProductEdge_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1) (y : Y) :
    crossProductEdge X Y 0 a (SingularHomology.pointCycle y).1 =
      SingularChains.inducedChain (SingularHomology.crossInsertRight y) 1 a := by
  rw [SingularHomology.pointCycle_val, crossProductEdge_zero_simplex_right]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a point `0`-cycle, `crossProductCycles a` is the pushforward of `a` along the
point insertion. -/
@[simp]
theorem SingularHomology.crossProductCycles_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1) (y : Y) :
    SingularHomology.crossProductCycles X Y 0 a (SingularHomology.pointCycle y) =
      SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (SingularHomology.crossInsertRight y)) 1 a := by
  apply Subtype.ext
  rw [SingularHomology.crossProductCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact SingularHomology.crossProductEdge_pointCycle_right X Y a.1 y

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On the homology class of a point `0`-cycle, `crossProductHomology a` is the
point-insertion pushforward on homology. -/
@[simp]
theorem SingularHomology.crossProductHomology_pointClass_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (y : Y) :
    crossProductHomology X Y 0 a (SingularHomology.pointClass y) =
      SingularMayerVietoris.singularHomologyMap (SingularHomology.crossInsertRight y) 1 a := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  change
    SingularHomology.crossProductHomology X Y 0
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 1 c)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) 0
          (SingularHomology.pointCycle y)) =
      _
  rw [SingularHomology.crossProductHomology_cycleClass, SingularHomology.crossProductCycles_pointCycle_right]
  exact
    (SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass
        (SingularChains.singularChainMap (SingularHomology.crossInsertRight y)) 1 c).symm


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

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.formalMap_comp {V W Z : Type*} (f : W → Z) (g : V → W) (n : ℕ)
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

theorem PeriodTorusHigherHomology.formalMap_prod_swap {V W V' W' : Type*} (f : V → V')
    (g : W → W') (n : ℕ) (c : SingularMayerVietoris.FormalChains (W × V) n) :
    SingularMayerVietoris.formalMap (Prod.map f g) n
        (SingularMayerVietoris.formalMap Prod.swap n c) =
      SingularMayerVietoris.formalMap Prod.swap n
        (SingularMayerVietoris.formalMap (Prod.map g f) n c) := by
  rw [PeriodTorusHigherHomology.formalMap_comp, PeriodTorusHigherHomology.formalMap_comp]
  rfl

theorem PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_one {V W : Type*}
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
        rw [PeriodTorusHigherHomology.formalMap_comp]
        rfl
      _ = _ :=
        (SingularHomology.formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w) v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

theorem PeriodTorusHigherHomology.formalMap_swap_edgeCrossProduct_zero {V W : Type*}
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
        rw [PeriodTorusHigherHomology.formalMap_comp]
        rfl
      _ = _ :=
        (SingularHomology.formalPointCrossProduct_simplex_left 1 w (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

def PeriodTorusHigherHomology.formalEdgeSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 3 :=
  SingularHomology.formalEdgeCrossProduct 1 +
    (SingularHomology.formalEdgeCrossProduct 1).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 3)

@[simp]

theorem PeriodTorusHigherHomology.formalEdgeSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    PeriodTorusHigherHomology.formalEdgeSwapDefect c d =
      SingularHomology.formalEdgeCrossProduct 1 c d +
        SingularMayerVietoris.formalMap Prod.swap 3 (SingularHomology.formalEdgeCrossProduct 1 d c) :=
  rfl

theorem PeriodTorusHigherHomology.formalBoundary_edgeSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 2 (PeriodTorusHigherHomology.formalEdgeSwapDefect c d) = 0 := by
  rw [PeriodTorusHigherHomology.formalEdgeSwapDefect_apply, map_add, SingularHomology.formalBoundary_edgeCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, SingularHomology.formalBoundary_edgeCrossProduct, map_sub,
    PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_one, PeriodTorusHigherHomology.formalMap_swap_edgeCrossProduct_zero]
  abel

theorem PeriodTorusHigherHomology.formalMap_edgeSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 3 (PeriodTorusHigherHomology.formalEdgeSwapDefect c d) =
      PeriodTorusHigherHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [PeriodTorusHigherHomology.formalEdgeSwapDefect_apply, map_add, SingularHomology.formalMap_edgeCrossProduct, PeriodTorusHigherHomology.formalMap_prod_swap,
    SingularHomology.formalMap_edgeCrossProduct, PeriodTorusHigherHomology.formalEdgeSwapDefect_apply]

def PeriodTorusHigherHomology.formalEdgeSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  SingularHomology.formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 3
      (PeriodTorusHigherHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w))

@[simp]

theorem PeriodTorusHigherHomology.formalEdgeSwapHomotopy_simplex {V W : Type*} (v : Fin 2 → V)
    (w : Fin 2 → W) :
    PeriodTorusHigherHomology.formalEdgeSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 3
        (PeriodTorusHigherHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)) :=
  SingularHomology.formalBilinearLift_simplex _ _ _

theorem PeriodTorusHigherHomology.formalEdgeSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (PeriodTorusHigherHomology.formalEdgeSwapHomotopy c d) =
      PeriodTorusHigherHomology.formalEdgeSwapDefect c d := by
  have h :
    (PeriodTorusHigherHomology.formalEdgeSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 3) =
      PeriodTorusHigherHomology.formalEdgeSwapDefect := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, PeriodTorusHigherHomology.formalEdgeSwapHomotopy_simplex,
      SingularMayerVietoris.formalBoundary_cone, PeriodTorusHigherHomology.formalBoundary_edgeSwapDefect, map_zero,
      sub_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

theorem PeriodTorusHigherHomology.formalMap_edgeSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (PeriodTorusHigherHomology.formalEdgeSwapHomotopy c d) =
      PeriodTorusHigherHomology.formalEdgeSwapHomotopy (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have h :
    (PeriodTorusHigherHomology.formalEdgeSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 4) =
      ((PeriodTorusHigherHomology.formalEdgeSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 2) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, PeriodTorusHigherHomology.formalEdgeSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone, PeriodTorusHigherHomology.formalMap_edgeSwapDefect,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.prodSwap_productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    (ContinuousMap.prodSwap :
            C(SingularChains.Simplex p × SingularChains.Simplex q,
              SingularChains.Simplex q × SingularChains.Simplex p)).comp
        (SingularHomology.productAffineSimplex v) =
      SingularHomology.productAffineSimplex (Prod.swap ∘ v) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.inducedChain_swap_productAffineChainMap (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 1)) :
    SingularChains.inducedChain
        (ContinuousMap.prodSwap :
          C(SingularChains.Simplex p × SingularChains.Simplex q,
            SingularChains.Simplex q × SingularChains.Simplex p))
        n (SingularHomology.productAffineChainMap p q n c) =
      SingularHomology.productAffineChainMap q p n (SingularMayerVietoris.formalMap Prod.swap (n + 1) c) := by
  have h :
    (SingularChains.inducedChain
            (ContinuousMap.prodSwap :
              C(SingularChains.Simplex p × SingularChains.Simplex q,
                SingularChains.Simplex q × SingularChains.Simplex p))
            n).comp
        (SingularHomology.productAffineChainMap p q n) =
      (SingularHomology.productAffineChainMap q p n).comp (SingularMayerVietoris.formalMap Prod.swap (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.prodSwap_productAffineSimplex]
  exact LinearMap.congr_fun h c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.inducedChain_prodMap_swap {X Y X' Y' : Type}
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

def PeriodTorusHigherHomology.crossProductSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ] SingularChains.Chains (X × Y) 3 :=
  SingularHomology.chainBilinearLift X Y 1 1 fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) 3
      (SingularHomology.productAffineChainMap 1 1 3
        (PeriodTorusHigherHomology.formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : SingularChains.SingularSimplex X 1)
    (τ : SingularChains.SingularSimplex Y 1) :
    PeriodTorusHigherHomology.crossProductSwapHomotopy X Y (SingularChains.simplexChain X 1 σ)
        (SingularChains.simplexChain Y 1 τ) =
      SingularChains.inducedChain (σ.prodMap τ) 3
        (SingularHomology.productAffineChainMap 1 1 3
          (PeriodTorusHigherHomology.formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  SingularHomology.chainBilinearLift_simplex X Y 1 1 _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1) :
    SingularChains.inducedChain (f.prodMap g) 3 (PeriodTorusHigherHomology.crossProductSwapHomotopy X Y a b) =
      PeriodTorusHigherHomology.crossProductSwapHomotopy X' Y' (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g 1 b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (PeriodTorusHigherHomology.crossProductSwapHomotopy X Y)
        (SingularChains.inducedChain (f.prodMap g) 3) =
      SingularHomology.integerBilinearPrecompose (PeriodTorusHigherHomology.crossProductSwapHomotopy X' Y') (SingularChains.inducedChain f 1)
        (SingularChains.inducedChain g 1) := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 1
    intro σ τ
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, PeriodTorusHigherHomology.crossProductSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    PeriodTorusHigherHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      SingularHomology.productAffineChainMap p q 3 (PeriodTorusHigherHomology.formalEdgeSwapHomotopy a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (PeriodTorusHigherHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q))
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1) =
      SingularHomology.integerBilinearPostcompose PeriodTorusHigherHomology.formalEdgeSwapHomotopy (SingularHomology.productAffineChainMap p q 3) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, PeriodTorusHigherHomology.crossProductSwapHomotopy_simplex]
    rw [SingularHomology.inducedChain_productAffineChainMap]
    change
      SingularHomology.productAffineChainMap p q 3
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            4
            (PeriodTorusHigherHomology.formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [PeriodTorusHigherHomology.formalMap_edgeSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 3
            2).hom
        (PeriodTorusHigherHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)) =
      SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b) +
        SingularChains.inducedChain ContinuousMap.prodSwap 2
          (SingularHomology.crossProductEdge (SingularChains.Simplex q) (SingularChains.Simplex p) 1
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 1 a)) := by
  rw [PeriodTorusHigherHomology.crossProductSwapHomotopy_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    PeriodTorusHigherHomology.formalEdgeSwapHomotopy_boundary, PeriodTorusHigherHomology.formalEdgeSwapDefect_apply, map_add,
    SingularHomology.crossProductEdge_affineChainMap, SingularHomology.crossProductEdge_affineChainMap,
    PeriodTorusHigherHomology.inducedChain_swap_productAffineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) :
    ((SingularChains.singularComplex (X × Y)).d 3 2).hom (PeriodTorusHigherHomology.crossProductSwapHomotopy X Y a b) =
      SingularHomology.crossProductEdge X Y 1 a b +
        SingularChains.inducedChain ContinuousMap.prodSwap 2 (SingularHomology.crossProductEdge Y X 1 b a) := by
  have h :
    SingularHomology.integerBilinearPostcompose (PeriodTorusHigherHomology.crossProductSwapHomotopy X Y)
        ((SingularChains.singularComplex (X × Y)).d 3 2).hom =
      SingularHomology.crossProductEdge X Y 1 +
        SingularHomology.integerBilinearPostcompose (SingularHomology.integerBilinearFlip (SingularHomology.crossProductEdge Y X 1))
          (SingularChains.inducedChain ContinuousMap.prodSwap 2) := by
    apply SingularHomology.chainBilinearMap_ext X Y 1 1
    intro σ τ
    have hstd :=
      PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary_affine 1 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 2) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearFlip_apply, LinearMap.add_apply,
      map_add, SingularChains.inducedChain_boundary, PeriodTorusHigherHomology.crossProductSwapHomotopy_natural,
      PeriodTorusHigherHomology.inducedChain_prodMap_swap, SingularHomology.crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductCycleClasses_add_swap_eq_zero {X Y : Type}
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
  refine ⟨PeriodTorusHigherHomology.crossProductSwapHomotopy X Y a.1 b.1, ?_⟩
  rw [Submodule.coe_add, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary a.1 b.1

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductHomology_add_swap_eq_zero {X Y : Type}
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
  exact PeriodTorusHigherHomology.crossProductCycleClasses_add_swap_eq_zero a b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductHomology_swap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
        (SingularHomology.crossProductHomology X Y 1 a b) =
      -SingularHomology.crossProductHomology Y X 1 b a := by
  have h := PeriodTorusHigherHomology.crossProductHomology_add_swap_eq_zero b a
  exact eq_neg_of_add_eq_zero_right h

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute {X Z : Type}
    [TopologicalSpace X] [TopologicalSpace Z] (f : C(X × X, Z))
    (hf : f.comp ContinuousMap.prodSwap = f) (a b : SingularMayerVietoris.SingularHomology X 1) :
    SingularMayerVietoris.singularHomologyMap f 2 (SingularHomology.crossProductHomology X X 1 a b) =
      -SingularMayerVietoris.singularHomologyMap f 2 (SingularHomology.crossProductHomology X X 1 b a) := by
  have h :=
    congrArg (SingularMayerVietoris.singularHomologyMap f 2) (PeriodTorusHigherHomology.crossProductHomology_swap a b)
  rw [map_neg] at h
  have hc :=
    LinearMap.congr_fun (SingularHomology.singularHomologyMap_comp (ContinuousMap.prodSwap : C(X × X, X × X)) f 2)
      (SingularHomology.crossProductHomology X X 1 a b)
  rw [hf] at hc
  exact hc.trans h

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.integerTrilinearPostcompose {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := SingularHomology.integerBilinearPostcompose (F a) g
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [SingularHomology.integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => g (l b c)) (F.map_smul r a)).trans
        (g.map_smul r (F a b c))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.integerTrilinearPostcompose_apply {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) (a : A) (b : B) (c : C) :
    PeriodTorusHigherHomology.integerTrilinearPostcompose F g a b c = g (F a b c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.integerTrilinearPrecompose {A B C D A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    [Module ℤ A'] [Module ℤ B'] [Module ℤ C'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) : A' →ₗ[ℤ] B' →ₗ[ℤ] C' →ₗ[ℤ] D
    where
  toFun a := SingularHomology.integerBilinearPrecompose (F (f a)) g h
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [SingularHomology.integerBilinearPrecompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun x => F x (g b) (h c)) (f.map_smul r a)).trans
        (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => l (g b) (h c)) (F.map_smul r (f a)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.integerTrilinearPrecompose_apply {A B C D A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    [Module ℤ A'] [Module ℤ B'] [Module ℤ C'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) (a : A') (b : B') (c : C') :
    PeriodTorusHigherHomology.integerTrilinearPrecompose F f g h a b c = F (f a) (g b) (h c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.integerTrilinearLeftAssociated {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] B →ₗ[ℤ] D) (G : D →ₗ[ℤ] C →ₗ[ℤ] E) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := SingularHomology.integerBilinearPrecompose G (F a) LinearMap.id
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [SingularHomology.integerBilinearPrecompose_apply, LinearMap.id_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun l : B →ₗ[ℤ] D => G (l b) c) (F.map_smul r a)).trans
        (congrArg (fun l : C →ₗ[ℤ] E => l c) (G.map_smul r (F a b)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.integerTrilinearRightAssociated {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] D →ₗ[ℤ] E) (G : B →ₗ[ℤ] C →ₗ[ℤ] D) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := SingularHomology.integerBilinearPostcompose G (F a)
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [SingularHomology.integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact congrArg (fun l : D →ₗ[ℤ] E => l (G b c)) (F.map_smul r a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.chainTrilinearLift (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f :
      SingularChains.SingularSimplex X p →
        SingularChains.SingularSimplex Y q → SingularChains.SingularSimplex Z r → M) :
    SingularChains.Chains X p →ₗ[ℤ]
      SingularChains.Chains Y q →ₗ[ℤ] SingularChains.Chains Z r →ₗ[ℤ] M :=
  SingularChains.chainLift X p fun σ => SingularHomology.chainBilinearLift Y Z q r (f σ)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.chainTrilinearLift_simplex (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f :
      SingularChains.SingularSimplex X p →
        SingularChains.SingularSimplex Y q → SingularChains.SingularSimplex Z r → M)
    (σ : SingularChains.SingularSimplex X p) (τ : SingularChains.SingularSimplex Y q)
    (υ : SingularChains.SingularSimplex Z r) :
    PeriodTorusHigherHomology.chainTrilinearLift X Y Z p q r f (SingularChains.simplexChain X p σ)
        (SingularChains.simplexChain Y q τ) (SingularChains.simplexChain Z r υ) =
      f σ τ υ := by
  rw [PeriodTorusHigherHomology.chainTrilinearLift, SingularChains.chainLift_simplex, SingularHomology.chainBilinearLift_simplex]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.chainTrilinearMap_ext (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    {F G :
      SingularChains.Chains X p →ₗ[ℤ]
        SingularChains.Chains Y q →ₗ[ℤ] SingularChains.Chains Z r →ₗ[ℤ] M}
    (h :
      ∀ σ τ υ,
        F (SingularChains.simplexChain X p σ) (SingularChains.simplexChain Y q τ)
            (SingularChains.simplexChain Z r υ) =
          G (SingularChains.simplexChain X p σ) (SingularChains.simplexChain Y q τ)
            (SingularChains.simplexChain Z r υ)) :
    F = G := by
  apply SingularChains.chainMap_ext X p
  intro σ
  apply SingularHomology.chainBilinearMap_ext Y Z q r
  exact h σ

theorem PeriodTorusHigherHomology.formalMap_comp_apply {V W Z : Type*} (f : W → Z) (g : V → W)
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

theorem PeriodTorusHigherHomology.formalMap_id_apply {V : Type*} (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap (id : V → V) n c = c := by
  have h : SingularMayerVietoris.formalMap (id : V → V) n = LinearMap.id := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [SingularMayerVietoris.formalMap_simplex, LinearMap.id_apply]
    rfl
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_point_left {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 1) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (SingularHomology.formalEdgeCrossProduct q (SingularHomology.formalPointCrossProduct 1 a b) c) =
      SingularHomology.formalPointCrossProduct (q + 1) a (SingularHomology.formalEdgeCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((SingularHomology.formalEdgeCrossProduct q).flip c).comp ((SingularHomology.formalPointCrossProduct 1).flip b)) =
      (SingularHomology.formalPointCrossProduct (q + 1)).flip (SingularHomology.formalEdgeCrossProduct q b c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, SingularHomology.formalPointCrossProduct_simplex_left]
    have hn := SingularHomology.formalMap_edgeCrossProduct (fun w : W => (v 0, w)) (id : Z → Z) q b c
    rw [PeriodTorusHigherHomology.formalMap_id_apply] at hn
    rw [← hn, PeriodTorusHigherHomology.formalMap_comp_apply]
    rfl
  exact LinearMap.congr_fun h a

theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_point_middle {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 1)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (SingularHomology.formalEdgeCrossProduct q (SingularHomology.formalEdgeCrossProduct 0 a b) c) =
      SingularHomology.formalEdgeCrossProduct q a (SingularHomology.formalPointCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((SingularHomology.formalEdgeCrossProduct q).flip c).comp (SingularHomology.formalEdgeCrossProduct 0 a)) =
      (SingularHomology.formalEdgeCrossProduct q a).comp ((SingularHomology.formalPointCrossProduct q).flip c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [SingularHomology.formalEdgeCrossProduct_zero_simplex_right, SingularHomology.formalPointCrossProduct_simplex_left]
    have hl := SingularHomology.formalMap_edgeCrossProduct (fun v : V => (v, w 0)) (id : Z → Z) q a c
    have hr := SingularHomology.formalMap_edgeCrossProduct (id : V → V) (fun z : Z => (w 0, z)) q a c
    rw [PeriodTorusHigherHomology.formalMap_id_apply] at hl hr
    rw [← hl, PeriodTorusHigherHomology.formalMap_comp_apply, ← hr]
    rfl
  exact LinearMap.congr_fun h b

theorem PeriodTorusHigherHomology.formalTriangleCrossProduct_point_right {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3
        (SingularHomology.formalTriangleCrossProduct 0 (SingularHomology.formalEdgeCrossProduct 1 a b) c) =
      SingularHomology.formalEdgeCrossProduct 1 a (SingularHomology.formalEdgeCrossProduct 0 b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3).comp
        (SingularHomology.formalTriangleCrossProduct 0 (SingularHomology.formalEdgeCrossProduct 1 a b)) =
      (SingularHomology.formalEdgeCrossProduct 1 a).comp (SingularHomology.formalEdgeCrossProduct 0 b) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.formalTriangleCrossProduct_zero_simplex_right,
      SingularHomology.formalEdgeCrossProduct_zero_simplex_right, PeriodTorusHigherHomology.formalMap_comp_apply]
    have hn := SingularHomology.formalMap_edgeCrossProduct (id : V → V) (fun w : W => (w, z 0)) 1 a b
    rw [PeriodTorusHigherHomology.formalMap_id_apply] at hn
    exact hn
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.formalChains_trilinear_ext {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M]
    {f g :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M}
    (h :
      ∀ v w z,
        f (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalSimplex z) =
          g (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalSimplex z)) :
    f = g := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply SingularHomology.formalChains_bilinear_ext
  exact h v

def PeriodTorusHigherHomology.formalTrilinearLift {V W Z M : Type*} {n m l : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => SingularHomology.formalBilinearLift (f v)

@[simp]

theorem PeriodTorusHigherHomology.formalTrilinearLift_simplex {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M)
    (v : Fin n → V) (w : Fin m → W) (z : Fin l → Z) :
    PeriodTorusHigherHomology.formalTrilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      f v w z := by simp [PeriodTorusHigherHomology.formalTrilinearLift]

def PeriodTorusHigherHomology.formalAssociatorDefect {V W Z : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3) :=
  (SingularHomology.formalEdgeCrossProduct 1).compr₂
      ((SingularHomology.formalTriangleCrossProduct q).compr₂
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
          (q + 3))) -
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z (q + 1))
              (SingularMayerVietoris.FormalChains (W × Z) (q + 2))
              (SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3))).compl₂
          (SingularHomology.formalEdgeCrossProduct q)).comp
      (SingularHomology.formalEdgeCrossProduct (q + 1))

@[simp]

theorem PeriodTorusHigherHomology.formalAssociatorDefect_apply {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    PeriodTorusHigherHomology.formalAssociatorDefect q a b c =
      SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 3)
          (SingularHomology.formalTriangleCrossProduct q (SingularHomology.formalEdgeCrossProduct 1 a b) c) -
        SingularHomology.formalEdgeCrossProduct (q + 1) a (SingularHomology.formalEdgeCrossProduct q b c) :=
  rfl

@[simp]

theorem PeriodTorusHigherHomology.formalAssociatorDefect_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : PeriodTorusHigherHomology.formalAssociatorDefect 0 a b c = 0 := by
  rw [PeriodTorusHigherHomology.formalAssociatorDefect_apply, PeriodTorusHigherHomology.formalTriangleCrossProduct_point_right, sub_self]

theorem PeriodTorusHigherHomology.formalBoundary_associatorDefect {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 2)) :
    SingularMayerVietoris.formalBoundary (q + 3) (PeriodTorusHigherHomology.formalAssociatorDefect (q + 1) a b c) =
      PeriodTorusHigherHomology.formalAssociatorDefect q a b (SingularMayerVietoris.formalBoundary (q + 1) c) := by
  simp only [PeriodTorusHigherHomology.formalAssociatorDefect_apply, map_sub, ← SingularMayerVietoris.formalMap_boundary,
    SingularHomology.formalBoundary_triangleCrossProduct, SingularHomology.formalBoundary_edgeCrossProduct, map_add,
    LinearMap.sub_apply, PeriodTorusHigherHomology.formalEdgeCrossProduct_point_middle]
  rw [PeriodTorusHigherHomology.formalEdgeCrossProduct_point_left (q + 1) (SingularMayerVietoris.formalBoundary 1 a) b c]
  abel

theorem PeriodTorusHigherHomology.formalMap_prodAssoc_naturality {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') (n : ℕ)
    (c : SingularMayerVietoris.FormalChains ((V × W) × Z) n) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n c) =
      SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n c) := by
  have heq :
    (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n).comp
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n) =
      (SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n).comp
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun heq c

theorem PeriodTorusHigherHomology.formalMap_associatorDefect {V W Z V' W' Z' : Type*} (f : V → V')
    (g : W → W') (h : Z → Z') (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
    (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 3)
        (PeriodTorusHigherHomology.formalAssociatorDefect q a b c) =
      PeriodTorusHigherHomology.formalAssociatorDefect q (SingularMayerVietoris.formalMap f 2 a)
        (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) := by
  rw [PeriodTorusHigherHomology.formalAssociatorDefect_apply, map_sub, PeriodTorusHigherHomology.formalMap_prodAssoc_naturality,
    SingularHomology.formalMap_triangleCrossProduct, SingularHomology.formalMap_edgeCrossProduct, SingularHomology.formalMap_edgeCrossProduct,
    SingularHomology.formalMap_edgeCrossProduct]
  rfl

private def PeriodTorusHigherHomology.triplePostcomp_mo1973_13949 {V W Z U U' : Type*}
    {n m l r s : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains U r →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s :=
  F.compr₂
    (LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z l)
      (SingularMayerVietoris.FormalChains U r) (SingularMayerVietoris.FormalChains U' s) f)

private def PeriodTorusHigherHomology.triplePrecompLast_mo1973_13950 {V W Z Z' U : Type*}
    {n m l l' r : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains Z l) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains U r :=
  F.compr₂
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z' l')
          (SingularMayerVietoris.FormalChains Z l) (SingularMayerVietoris.FormalChains U r)).flip
      f)

def PeriodTorusHigherHomology.formalAssociatorHomotopy {V W Z : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
            SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 4)
  | 0 => 0
  | q + 1 =>
    PeriodTorusHigherHomology.formalTrilinearLift fun v w z =>
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (PeriodTorusHigherHomology.formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          PeriodTorusHigherHomology.formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z)))

@[simp]

theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : PeriodTorusHigherHomology.formalAssociatorHomotopy 0 a b c = 0 :=
  rfl

@[simp]

theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_simplex_succ {V W Z : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin 2 → W) (z : Fin (q + 2) → Z) :
    PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (PeriodTorusHigherHomology.formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          PeriodTorusHigherHomology.formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z))) :=
  PeriodTorusHigherHomology.formalTrilinearLift_simplex _ _ _ _

theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalBoundary 3 (PeriodTorusHigherHomology.formalAssociatorHomotopy 0 a b c) =
      PeriodTorusHigherHomology.formalAssociatorDefect 0 a b c := by
  rw [PeriodTorusHigherHomology.formalAssociatorHomotopy_zero, map_zero, PeriodTorusHigherHomology.formalAssociatorDefect_zero]

theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary {V W Z : Type*} :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 4) (PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1) a b c) +
          PeriodTorusHigherHomology.formalAssociatorHomotopy q a b (SingularMayerVietoris.formalBoundary (q + 1) c) =
        PeriodTorusHigherHomology.formalAssociatorDefect (q + 1) a b c := by
  intro q
  induction q with
  | zero =>
    intro a b c
    have heq :
      PeriodTorusHigherHomology.triplePostcomp_mo1973_13949 (PeriodTorusHigherHomology.formalAssociatorHomotopy (V := V) (W := W) (Z := Z) 1)
            (SingularMayerVietoris.formalBoundary 4) +
          PeriodTorusHigherHomology.triplePrecompLast_mo1973_13950 (PeriodTorusHigherHomology.formalAssociatorHomotopy 0)
            (SingularMayerVietoris.formalBoundary 1) =
        PeriodTorusHigherHomology.formalAssociatorDefect 1 := by
      apply PeriodTorusHigherHomology.formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary 4
              (PeriodTorusHigherHomology.formalAssociatorHomotopy 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            PeriodTorusHigherHomology.formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex z)) =
          PeriodTorusHigherHomology.formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hz :
        SingularMayerVietoris.formalBoundary 3
            (PeriodTorusHigherHomology.formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              PeriodTorusHigherHomology.formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by
        rw [map_sub, PeriodTorusHigherHomology.formalBoundary_associatorDefect, PeriodTorusHigherHomology.formalAssociatorDefect_zero,
          PeriodTorusHigherHomology.formalAssociatorHomotopy_zero, map_zero, sub_self]
      rw [PeriodTorusHigherHomology.formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c
  | succ q ih =>
    intro a b c
    have heq :
      PeriodTorusHigherHomology.triplePostcomp_mo1973_13949 (PeriodTorusHigherHomology.formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 2))
            (SingularMayerVietoris.formalBoundary (q + 5)) +
          PeriodTorusHigherHomology.triplePrecompLast_mo1973_13950 (PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1))
            (SingularMayerVietoris.formalBoundary (q + 2)) =
        PeriodTorusHigherHomology.formalAssociatorDefect (q + 2) := by
      apply PeriodTorusHigherHomology.formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary (q + 5)
              (PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z)) =
          PeriodTorusHigherHomology.formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hp :
        SingularMayerVietoris.formalBoundary (q + 4)
            (PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z))) =
          PeriodTorusHigherHomology.formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2)
              (SingularMayerVietoris.formalSimplex z)) := by
        simpa only [SingularMayerVietoris.formalBoundary_boundary, map_zero, add_zero] using
          ih (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2) (SingularMayerVietoris.formalSimplex z))
      have hz :
        SingularMayerVietoris.formalBoundary (q + 4)
            (PeriodTorusHigherHomology.formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by rw [map_sub, PeriodTorusHigherHomology.formalBoundary_associatorDefect, hp, sub_self]
      rw [PeriodTorusHigherHomology.formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

theorem PeriodTorusHigherHomology.formalMap_associatorHomotopy {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 4)
          (PeriodTorusHigherHomology.formalAssociatorHomotopy q a b c) =
        PeriodTorusHigherHomology.formalAssociatorHomotopy q (SingularMayerVietoris.formalMap f 2 a)
          (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) :=
  by
  intro q
  induction q with
  | zero =>
    intro a b c
    simp only [PeriodTorusHigherHomology.formalAssociatorHomotopy_zero, map_zero]
  | succ q ih =>
    intro a b c
    have heq :
      PeriodTorusHigherHomology.triplePostcomp_mo1973_13949 (PeriodTorusHigherHomology.formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 1))
          (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)) =
        ((PeriodTorusHigherHomology.triplePrecompLast_mo1973_13950 (PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1))
                  (SingularMayerVietoris.formalMap h (q + 2))).compl₂
              (SingularMayerVietoris.formalMap g 2)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply PeriodTorusHigherHomology.formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)
            (PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) =
          PeriodTorusHigherHomology.formalAssociatorHomotopy (q + 1)
            (SingularMayerVietoris.formalMap f 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalMap g 2 (SingularMayerVietoris.formalSimplex w))
            (SingularMayerVietoris.formalMap h (q + 2) (SingularMayerVietoris.formalSimplex z))
      simp only [SingularMayerVietoris.formalMap_simplex, PeriodTorusHigherHomology.formalAssociatorHomotopy_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, PeriodTorusHigherHomology.formalMap_associatorDefect, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

def PeriodTorusHigherHomology.tripleAffineSimplex {n p q r : ℕ}
    (v :
      Fin (n + 1) →
        SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :
    C(SingularChains.Simplex n,
      SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (SingularHomology.productAffineSimplex (fun i => (v i).2))

theorem PeriodTorusHigherHomology.tripleAffineSimplex_face {n p q r : ℕ}
    (v :
      Fin (n + 2) → SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))
    (i : Fin (n + 2)) :
    (PeriodTorusHigherHomology.tripleAffineSimplex v).comp (SingularChains.simplexFace n i) =
      PeriodTorusHigherHomology.tripleAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg
        (fun f : C(SingularChains.Simplex n, SingularChains.Simplex q × SingularChains.Simplex r) =>
          f t)
        (SingularHomology.productAffineSimplex_face (fun j => (v j).2) i)

def PeriodTorusHigherHomology.tripleAffineChainMap (p q r n : ℕ) :
    SingularMayerVietoris.FormalChains
        (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))
        (n + 1) →ₗ[ℤ]
      SingularChains.Chains
        (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) n :=
  SingularMayerVietoris.formalLift fun v => SingularChains.simplexChain _ n (PeriodTorusHigherHomology.tripleAffineSimplex v)

@[simp]

theorem PeriodTorusHigherHomology.tripleAffineChainMap_simplex (p q r n : ℕ)
    (v :
      Fin (n + 1) →
        SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :
    PeriodTorusHigherHomology.tripleAffineChainMap p q r n (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain _ n (PeriodTorusHigherHomology.tripleAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

theorem PeriodTorusHigherHomology.tripleAffineChainMap_boundary (p q r n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains
        (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) (n + 2)) :
    ((SingularChains.singularComplex
                (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))).d
            (n + 1) n).hom
        (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1) c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex
                  (SingularChains.Simplex p ×
                    (SingularChains.Simplex q × SingularChains.Simplex r))).d
              (n + 1) n).hom).comp
        (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1)) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex
                  (SingularChains.Simplex p ×
                    (SingularChains.Simplex q × SingularChains.Simplex r))).d
              (n + 1) n).hom
          (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [PeriodTorusHigherHomology.tripleAffineChainMap_simplex, SingularChains.boundary_simplex]
    change
      _ =
        PeriodTorusHigherHomology.tripleAffineChainMap p q r n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, PeriodTorusHigherHomology.tripleAffineChainMap_simplex, PeriodTorusHigherHomology.tripleAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

def PeriodTorusHigherHomology.affineProductLeft {a b p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p × SingularChains.Simplex q)
    (w : Fin (b + 1) → SingularChains.Simplex r) :
    C(SingularChains.Simplex a × SingularChains.Simplex b,
      SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :=
  (Homeomorph.prodAssoc (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) :
        C(_, _)).comp
    ((SingularHomology.productAffineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))

def PeriodTorusHigherHomology.affineProductRight {a b p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p)
    (w : Fin (b + 1) → SingularChains.Simplex q × SingularChains.Simplex r) :
    C(SingularChains.Simplex a × SingularChains.Simplex b,
      SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex v).prodMap (SingularHomology.productAffineSimplex w)

theorem PeriodTorusHigherHomology.affineProductLeft_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p × SingularChains.Simplex q)
    (w : Fin (b + 1) → SingularChains.Simplex r)
    (z : Fin (m + 1) → SingularChains.Simplex a × SingularChains.Simplex b) :
    (PeriodTorusHigherHomology.affineProductLeft v w).comp (SingularHomology.productAffineSimplex z) =
      PeriodTorusHigherHomology.tripleAffineSimplex (fun j => PeriodTorusHigherHomology.affineProductLeft v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).1) (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).2) (fun j => (z j).1))
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))

theorem PeriodTorusHigherHomology.affineProductRight_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p)
    (w : Fin (b + 1) → SingularChains.Simplex q × SingularChains.Simplex r)
    (z : Fin (m + 1) → SingularChains.Simplex a × SingularChains.Simplex b) :
    (PeriodTorusHigherHomology.affineProductRight v w).comp (SingularHomology.productAffineSimplex z) =
      PeriodTorusHigherHomology.tripleAffineSimplex (fun j => PeriodTorusHigherHomology.affineProductRight v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).1) (fun j => (z j).2))
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).2) (fun j => (z j).2))

theorem PeriodTorusHigherHomology.inducedChain_affineProductLeft {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p × SingularChains.Simplex q)
    (w : Fin (b + 1) → SingularChains.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex a × SingularChains.Simplex b)
        (m + 1)) :
    SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductLeft v w) m (SingularHomology.productAffineChainMap a b m c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductLeft v w) (m + 1) c) := by
  have h :
    (SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductLeft v w) m).comp (SingularHomology.productAffineChainMap a b m) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductLeft v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.tripleAffineChainMap_simplex, PeriodTorusHigherHomology.affineProductLeft_comp]
    rfl
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.inducedChain_affineProductRight {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p)
    (w : Fin (b + 1) → SingularChains.Simplex q × SingularChains.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex a × SingularChains.Simplex b)
        (m + 1)) :
    SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductRight v w) m (SingularHomology.productAffineChainMap a b m c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductRight v w) (m + 1) c) := by
  have h :
    (SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductRight v w) m).comp (SingularHomology.productAffineChainMap a b m) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductRight v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.tripleAffineChainMap_simplex, PeriodTorusHigherHomology.affineProductRight_comp]
    rfl
  exact LinearMap.congr_fun h c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.crossProductAssociatorDefect (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ]
        SingularChains.Chains Z n →ₗ[ℤ] SingularChains.Chains (X × (Y × Z)) (n + 2) :=
  PeriodTorusHigherHomology.integerTrilinearPostcompose
      (PeriodTorusHigherHomology.integerTrilinearLeftAssociated (SingularHomology.crossProductEdge X Y 1) (SingularHomology.crossProductTriangle (X × Y) Z n))
      (SingularChains.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)) -
    PeriodTorusHigherHomology.integerTrilinearRightAssociated (SingularHomology.crossProductEdge X (Y × Z) (n + 1)) (SingularHomology.crossProductEdge Y Z n)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_apply (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n) :
    PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z n a b c =
      SingularChains.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)
          (SingularHomology.crossProductTriangle (X × Y) Z n (SingularHomology.crossProductEdge X Y 1 a b) c) -
        SingularHomology.crossProductEdge X (Y × Z) (n + 1) a (SingularHomology.crossProductEdge Y Z n b c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.crossProductAssociatorHomotopy (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ]
        SingularChains.Chains Z n →ₗ[ℤ] SingularChains.Chains (X × (Y × Z)) (n + 3) :=
  PeriodTorusHigherHomology.chainTrilinearLift X Y Z 1 1 n fun σ τ υ =>
    SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
      (PeriodTorusHigherHomology.tripleAffineChainMap 1 1 n (n + 3)
        (PeriodTorusHigherHomology.formalAssociatorHomotopy n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_simplex (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (σ : SingularChains.SingularSimplex X 1) (τ : SingularChains.SingularSimplex Y 1)
    (υ : SingularChains.SingularSimplex Z n) :
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z n (SingularChains.simplexChain X 1 σ)
        (SingularChains.simplexChain Y 1 τ) (SingularChains.simplexChain Z n υ) =
      SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
        (PeriodTorusHigherHomology.tripleAffineChainMap 1 1 n (n + 3)
          (PeriodTorusHigherHomology.formalAssociatorHomotopy n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  PeriodTorusHigherHomology.chainTrilinearLift_simplex X Y Z 1 1 n _ σ τ υ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n) :
    SingularChains.inducedChain (f.prodMap (g.prodMap h)) (n + 3)
        (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z n a b c) =
      PeriodTorusHigherHomology.crossProductAssociatorHomotopy X' Y' Z' n (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g 1 b) (SingularChains.inducedChain h n c) := by
  have heq :
    PeriodTorusHigherHomology.integerTrilinearPostcompose (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z n)
        (SingularChains.inducedChain (f.prodMap (g.prodMap h)) (n + 3)) =
      PeriodTorusHigherHomology.integerTrilinearPrecompose (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X' Y' Z' n)
        (SingularChains.inducedChain f 1) (SingularChains.inducedChain g 1)
        (SingularChains.inducedChain h n) := by
    apply PeriodTorusHigherHomology.chainTrilinearMap_ext X Y Z 1 1 n
    intro σ τ υ
    simp only [PeriodTorusHigherHomology.integerTrilinearPostcompose_apply, PeriodTorusHigherHomology.integerTrilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, PeriodTorusHigherHomology.crossProductAssociatorHomotopy_simplex]
    have hc :
      (f.comp σ).prodMap ((g.comp τ).prodMap (h.comp υ)) =
        (f.prodMap (g.prodMap h)).comp (σ.prodMap (τ.prodMap υ)) :=
      rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.inducedChain_prodAssoc_natural {X : Type} {Y : Type} {Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (c : SingularChains.Chains ((X × Y) × Z) n) :
    SingularChains.inducedChain (f.prodMap (g.prodMap h)) n
        (SingularChains.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) n c) =
      SingularChains.inducedChain (Homeomorph.prodAssoc X' Y' Z' : C(_, _)) n
        (SingularChains.inducedChain ((f.prodMap g).prodMap h) n c) := by
  have hc :
    (f.prodMap (g.prodMap h)).comp (Homeomorph.prodAssoc X Y Z : C(_, _)) =
      (Homeomorph.prodAssoc X' Y' Z' : C(_, _)).comp ((f.prodMap g).prodMap h) :=
    rfl
  have heq := congrArg (fun k => SingularChains.inducedChain k n c) hc
  simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using heq

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n) :
    SingularChains.inducedChain (f.prodMap (g.prodMap h)) (n + 2)
        (PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z n a b c) =
      PeriodTorusHigherHomology.crossProductAssociatorDefect X' Y' Z' n (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g 1 b) (SingularChains.inducedChain h n c) := by
  simp only [PeriodTorusHigherHomology.crossProductAssociatorDefect_apply, map_sub, PeriodTorusHigherHomology.inducedChain_prodAssoc_natural,
    SingularHomology.crossProductTriangle_natural, SingularHomology.crossProductEdge_natural]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.productAffineSimplex_stdVertices_image {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    SingularHomology.productAffineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact SingularHomology.productAffineSimplex_vertex v i

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.prodMap_tripleAffineSimplex {a b c m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p) (w : Fin (b + 1) → SingularChains.Simplex q)
    (z : Fin (c + 1) → SingularChains.Simplex r)
    (t :
      Fin (m + 1) →
        SingularChains.Simplex a × (SingularChains.Simplex b × SingularChains.Simplex c)) :
    ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z))).comp
        (PeriodTorusHigherHomology.tripleAffineSimplex t) =
      PeriodTorusHigherHomology.tripleAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (t j).1,
            (SingularMayerVietoris.affineSimplex w (t j).2.1,
              SingularMayerVietoris.affineSimplex z (t j).2.2))) := by
  apply ContinuousMap.ext
  intro s
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex p) => f s)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (t j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex q) => f s)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (t j).2.1))
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f s)
          (SingularMayerVietoris.affineSimplex_comp z (fun j => (t j).2.2))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.inducedChain_tripleAffineChainMap {a b c m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p) (w : Fin (b + 1) → SingularChains.Simplex q)
    (z : Fin (c + 1) → SingularChains.Simplex r)
    (t :
      SingularMayerVietoris.FormalChains
        (SingularChains.Simplex a × (SingularChains.Simplex b × SingularChains.Simplex c)) (m + 1)) :
    SingularChains.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap
          ((SingularMayerVietoris.affineSimplex w).prodMap
            (SingularMayerVietoris.affineSimplex z)))
        m (PeriodTorusHigherHomology.tripleAffineChainMap a b c m t) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1) t) := by
  have h :
    (SingularChains.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              ((SingularMayerVietoris.affineSimplex w).prodMap
                (SingularMayerVietoris.affineSimplex z)))
            m).comp
        (PeriodTorusHigherHomology.tripleAffineChainMap a b c m) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro s
    simp only [LinearMap.comp_apply, PeriodTorusHigherHomology.tripleAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.prodMap_tripleAffineSimplex]
    rfl
  exact LinearMap.congr_fun h t

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductTriangle_productAffineChainMap_left (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 1)) :
    SingularChains.inducedChain
        (Homeomorph.prodAssoc (SingularChains.Simplex p) (SingularChains.Simplex q)
            (SingularChains.Simplex r) :
          C(_, _))
        (n + 2)
        (SingularHomology.crossProductTriangle (SingularChains.Simplex p × SingularChains.Simplex q)
          (SingularChains.Simplex r) n (SingularHomology.productAffineChainMap p q 2 a)
          (SingularMayerVietoris.affineChainMap r n b)) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 2)
        (SingularMayerVietoris.formalMap
          (fun x :
              (SingularChains.Simplex p × SingularChains.Simplex q) × SingularChains.Simplex r =>
            (x.1.1, (x.1.2, x.2)))
          (n + 3) (SingularHomology.formalTriangleCrossProduct n a b)) := by
  have h :
    SingularHomology.integerBilinearPostcompose
        (SingularHomology.integerBilinearPrecompose
          (SingularHomology.crossProductTriangle (SingularChains.Simplex p × SingularChains.Simplex q)
            (SingularChains.Simplex r) n)
          (SingularHomology.productAffineChainMap p q 2) (SingularMayerVietoris.affineChainMap r n))
        (SingularChains.inducedChain
          (Homeomorph.prodAssoc (SingularChains.Simplex p) (SingularChains.Simplex q)
              (SingularChains.Simplex r) :
            C(_, _))
          (n + 2)) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalTriangleCrossProduct n)
        ((PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 2)).comp
          (SingularMayerVietoris.formalMap
            (fun x :
                (SingularChains.Simplex p × SingularChains.Simplex q) × SingularChains.Simplex r =>
              (x.1.1, (x.1.2, x.2)))
            (n + 3))) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularHomology.productAffineChainMap_simplex, SingularMayerVietoris.affineChainMap_simplex,
      SingularHomology.crossProductTriangle_simplex, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
    change
      SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductLeft v w) (n + 2)
          (SingularHomology.productAffineChainMap 2 n (n + 2)
            (SingularHomology.formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [PeriodTorusHigherHomology.inducedChain_affineProductLeft]
    apply congrArg (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 2))
    change
      SingularMayerVietoris.formalMap
          ((fun x :
                (SingularChains.Simplex p × SingularChains.Simplex q) × SingularChains.Simplex r =>
              (x.1.1, (x.1.2, x.2))) ∘
            Prod.map (SingularHomology.productAffineSimplex v) (SingularMayerVietoris.affineSimplex w))
          (n + 3)
          (SingularHomology.formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))) =
        _
    rw [← PeriodTorusHigherHomology.formalMap_comp_apply, SingularHomology.formalMap_triangleCrossProduct,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.productAffineSimplex_stdVertices_image, SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductEdge_productAffineChainMap_right (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex q × SingularChains.Simplex r)
        (n + 1)) :
    SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q × SingularChains.Simplex r)
        n (SingularMayerVietoris.affineChainMap p 1 a) (SingularHomology.productAffineChainMap q r n b) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1) (SingularHomology.formalEdgeCrossProduct n a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductEdge (SingularChains.Simplex p)
          (SingularChains.Simplex q × SingularChains.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularHomology.productAffineChainMap q r n) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalEdgeCrossProduct n)
        (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1)) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.productAffineChainMap_simplex,
      SingularHomology.crossProductEdge_simplex]
    change
      SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductRight v w) (n + 1)
          (SingularHomology.productAffineChainMap 1 n (n + 1)
            (SingularHomology.formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [PeriodTorusHigherHomology.inducedChain_affineProductRight]
    change
      PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v) (SingularHomology.productAffineSimplex w)) (n + 2)
            (SingularHomology.formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      PeriodTorusHigherHomology.productAffineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 1)) :
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 3) (PeriodTorusHigherHomology.formalAssociatorHomotopy n a b c) := by
  have heq :
    PeriodTorusHigherHomology.integerTrilinearPrecompose
        (PeriodTorusHigherHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1)
        (SingularMayerVietoris.affineChainMap r n) =
      PeriodTorusHigherHomology.integerTrilinearPostcompose (PeriodTorusHigherHomology.formalAssociatorHomotopy n)
        (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 3)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    apply SingularMayerVietoris.formalChains_ext
    intro w
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [PeriodTorusHigherHomology.integerTrilinearPrecompose_apply, PeriodTorusHigherHomology.integerTrilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, PeriodTorusHigherHomology.crossProductAssociatorHomotopy_simplex]
    rw [PeriodTorusHigherHomology.inducedChain_tripleAffineChainMap]
    change
      PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 3)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (Prod.map (SingularMayerVietoris.affineSimplex w)
                (SingularMayerVietoris.affineSimplex z)))
            (n + 4)
            (PeriodTorusHigherHomology.formalAssociatorHomotopy n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [PeriodTorusHigherHomology.formalMap_associatorHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      SingularHomology.affineSimplex_stdVertices_image, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 1)) :
    PeriodTorusHigherHomology.crossProductAssociatorDefect (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 2) (PeriodTorusHigherHomology.formalAssociatorDefect n a b c) := by
  simp only [PeriodTorusHigherHomology.crossProductAssociatorDefect_apply, SingularHomology.crossProductEdge_affineChainMap, Nat.reduceAdd,
    PeriodTorusHigherHomology.crossProductTriangle_productAffineChainMap_left, PeriodTorusHigherHomology.crossProductEdge_productAffineChainMap_right,
    PeriodTorusHigherHomology.formalAssociatorDefect_apply, map_sub]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero_affine (p q r : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) 1) :
    ((SingularChains.singularComplex
                (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))).d
            3 2).hom
        (PeriodTorusHigherHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (SingularMayerVietoris.affineChainMap r 0 c)) =
      PeriodTorusHigherHomology.crossProductAssociatorDefect (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r 0 c) := by
  rw [PeriodTorusHigherHomology.crossProductAssociatorHomotopy_affineChainMap, PeriodTorusHigherHomology.tripleAffineChainMap_boundary,
    PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary_zero, PeriodTorusHigherHomology.crossProductAssociatorDefect_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_affine (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 2)) :
    ((SingularChains.singularComplex
                  (SingularChains.Simplex p ×
                    (SingularChains.Simplex q × SingularChains.Simplex r))).d
              (n + 4) (n + 3)).hom
          (PeriodTorusHigherHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
            (SingularChains.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) +
        PeriodTorusHigherHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (((SingularChains.singularComplex (SingularChains.Simplex r)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) =
      PeriodTorusHigherHomology.crossProductAssociatorDefect (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r (n + 1) c) := by
  rw [PeriodTorusHigherHomology.crossProductAssociatorHomotopy_affineChainMap, PeriodTorusHigherHomology.tripleAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, PeriodTorusHigherHomology.crossProductAssociatorHomotopy_affineChainMap,
    ← map_add, PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary, PeriodTorusHigherHomology.crossProductAssociatorDefect_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z 0) :
    ((SingularChains.singularComplex (X × (Y × Z))).d 3 2).hom
        (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z 0 a b c) =
      PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z 0 a b c := by
  have heq :
    PeriodTorusHigherHomology.integerTrilinearPostcompose (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z 0)
        ((SingularChains.singularComplex (X × (Y × Z))).d 3 2).hom =
      PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z 0 := by
    apply PeriodTorusHigherHomology.chainTrilinearMap_ext X Y Z 1 1 0
    intro σ τ υ
    have hstd :=
      PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero_affine 1 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστυ := congrArg (SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) 2) hstd
    simpa only [PeriodTorusHigherHomology.integerTrilinearPostcompose_apply, SingularChains.inducedChain_boundary,
      PeriodTorusHigherHomology.crossProductAssociatorHomotopy_natural, PeriodTorusHigherHomology.crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1)
    (c : SingularChains.Chains Z (n + 1)) :
    ((SingularChains.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom
          (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z (n + 1) a b c) +
        PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z n a b
          (((SingularChains.singularComplex Z).d (n + 1) n).hom c) =
      PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z (n + 1) a b c := by
  have heq :
    PeriodTorusHigherHomology.integerTrilinearPostcompose (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z (n + 1))
          ((SingularChains.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom +
        PeriodTorusHigherHomology.integerTrilinearPrecompose (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z n) LinearMap.id
          LinearMap.id ((SingularChains.singularComplex Z).d (n + 1) n).hom =
      PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z (n + 1) := by
    apply PeriodTorusHigherHomology.chainTrilinearMap_ext X Y Z 1 1 (n + 1)
    intro σ τ υ
    have hstd :=
      PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_affine 1 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστυ := congrArg (SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)) hstd
    simpa only [PeriodTorusHigherHomology.integerTrilinearPostcompose_apply, PeriodTorusHigherHomology.integerTrilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, SingularChains.inducedChain_boundary,
      PeriodTorusHigherHomology.crossProductAssociatorHomotopy_natural, PeriodTorusHigherHomology.crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_of_cycle {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n)
    (hc : ((SingularChains.singularComplex Z).d n (n - 1)).hom c = 0) :
    ((SingularChains.singularComplex (X × (Y × Z))).d (n + 3) (n + 2)).hom
        (PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z n a b c) =
      PeriodTorusHigherHomology.crossProductAssociatorDefect X Y Z n a b c := by
  cases n with
  | zero => exact PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero a b c
  | succ
    n =>
    have hc' : ((SingularChains.singularComplex Z).d (n + 1) n).hom c = 0 := by
      simpa only [Nat.succ_sub_one] using hc
    simpa only [hc', map_zero, add_zero] using PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary n a b c

theorem PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_two {V W : Type*}
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
        rw [PeriodTorusHigherHomology.formalMap_comp]
        rfl
      _ = _ :=
        (SingularHomology.formalTriangleCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w)
            v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

def PeriodTorusHigherHomology.formalMixedSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  SingularHomology.formalTriangleCrossProduct 1 -
    (SingularHomology.formalEdgeCrossProduct 2).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 4)

@[simp]

theorem PeriodTorusHigherHomology.formalMixedSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    PeriodTorusHigherHomology.formalMixedSwapDefect c d =
      SingularHomology.formalTriangleCrossProduct 1 c d -
        SingularMayerVietoris.formalMap Prod.swap 4 (SingularHomology.formalEdgeCrossProduct 2 d c) :=
  rfl

theorem PeriodTorusHigherHomology.formalBoundary_mixedSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (PeriodTorusHigherHomology.formalMixedSwapDefect c d) =
      PeriodTorusHigherHomology.formalEdgeSwapDefect (SingularMayerVietoris.formalBoundary 2 c) d := by
  rw [PeriodTorusHigherHomology.formalMixedSwapDefect_apply, map_sub, SingularHomology.formalBoundary_triangleCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, SingularHomology.formalBoundary_edgeCrossProduct, map_sub,
    PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_two, PeriodTorusHigherHomology.formalEdgeSwapDefect_apply]
  abel

theorem PeriodTorusHigherHomology.formalMap_mixedSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (PeriodTorusHigherHomology.formalMixedSwapDefect c d) =
      PeriodTorusHigherHomology.formalMixedSwapDefect (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [PeriodTorusHigherHomology.formalMixedSwapDefect_apply, map_sub, SingularHomology.formalMap_triangleCrossProduct, PeriodTorusHigherHomology.formalMap_prod_swap,
    SingularHomology.formalMap_edgeCrossProduct, PeriodTorusHigherHomology.formalMixedSwapDefect_apply]

def PeriodTorusHigherHomology.formalMixedSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 5 :=
  SingularHomology.formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 4
      (PeriodTorusHigherHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w) -
        PeriodTorusHigherHomology.formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
          (SingularMayerVietoris.formalSimplex w))

@[simp]

theorem PeriodTorusHigherHomology.formalMixedSwapHomotopy_simplex {V W : Type*} (v : Fin 3 → V)
    (w : Fin 2 → W) :
    PeriodTorusHigherHomology.formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 4
        (PeriodTorusHigherHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) -
          PeriodTorusHigherHomology.formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w)) :=
  SingularHomology.formalBilinearLift_simplex _ _ _

theorem PeriodTorusHigherHomology.formalMixedSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 4 (PeriodTorusHigherHomology.formalMixedSwapHomotopy c d) +
        PeriodTorusHigherHomology.formalEdgeSwapHomotopy (SingularMayerVietoris.formalBoundary 2 c) d =
      PeriodTorusHigherHomology.formalMixedSwapDefect c d := by
  have heq :
    (PeriodTorusHigherHomology.formalMixedSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 4) +
        (PeriodTorusHigherHomology.formalEdgeSwapHomotopy).comp (SingularMayerVietoris.formalBoundary 2) =
      PeriodTorusHigherHomology.formalMixedSwapDefect := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalBoundary 4
            (PeriodTorusHigherHomology.formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) +
          PeriodTorusHigherHomology.formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) =
        PeriodTorusHigherHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)
    have hz :
      SingularMayerVietoris.formalBoundary 3
          (PeriodTorusHigherHomology.formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) -
            PeriodTorusHigherHomology.formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
              (SingularMayerVietoris.formalSimplex w)) =
        0 := by
      rw [map_sub, PeriodTorusHigherHomology.formalBoundary_mixedSwapDefect, PeriodTorusHigherHomology.formalEdgeSwapHomotopy_boundary, sub_self]
    rw [PeriodTorusHigherHomology.formalMixedSwapHomotopy_simplex, SingularMayerVietoris.formalBoundary_cone, hz, map_zero,
      sub_zero, sub_add_cancel]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

theorem PeriodTorusHigherHomology.formalMap_mixedSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 5 (PeriodTorusHigherHomology.formalMixedSwapHomotopy c d) =
      PeriodTorusHigherHomology.formalMixedSwapHomotopy (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have heq :
    (PeriodTorusHigherHomology.formalMixedSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 5) =
      ((PeriodTorusHigherHomology.formalMixedSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 3) := by
    apply SingularHomology.formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, PeriodTorusHigherHomology.formalMixedSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone]
    congr 1
    rw [map_sub, PeriodTorusHigherHomology.formalMap_mixedSwapDefect, PeriodTorusHigherHomology.formalMap_edgeSwapHomotopy,
      SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.crossProductMixedSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ] SingularChains.Chains (X × Y) 4 :=
  SingularHomology.chainBilinearLift X Y 2 1 fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) 4
      (SingularHomology.productAffineChainMap 2 1 4
        (PeriodTorusHigherHomology.formalMixedSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : SingularChains.SingularSimplex X 2)
    (τ : SingularChains.SingularSimplex Y 1) :
    PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y (SingularChains.simplexChain X 2 σ)
        (SingularChains.simplexChain Y 1 τ) =
      SingularChains.inducedChain (σ.prodMap τ) 4
        (SingularHomology.productAffineChainMap 2 1 4
          (PeriodTorusHigherHomology.formalMixedSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  SingularHomology.chainBilinearLift_simplex X Y 2 1 _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : SingularChains.Chains X 2) (b : SingularChains.Chains Y 1) :
    SingularChains.inducedChain (f.prodMap g) 4 (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y a b) =
      PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X' Y' (SingularChains.inducedChain f 2 a)
        (SingularChains.inducedChain g 1 b) := by
  have h :
    SingularHomology.integerBilinearPostcompose (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y)
        (SingularChains.inducedChain (f.prodMap g) 4) =
      SingularHomology.integerBilinearPrecompose (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X' Y')
        (SingularChains.inducedChain f 2) (SingularChains.inducedChain g 1) := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 1
    intro σ τ
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    PeriodTorusHigherHomology.crossProductMixedSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      SingularHomology.productAffineChainMap p q 4 (PeriodTorusHigherHomology.formalMixedSwapHomotopy a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q))
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q 1) =
      SingularHomology.integerBilinearPostcompose PeriodTorusHigherHomology.formalMixedSwapHomotopy (SingularHomology.productAffineChainMap p q 4) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_simplex]
    rw [SingularHomology.inducedChain_productAffineChainMap]
    change
      SingularHomology.productAffineChainMap p q 4
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            5
            (PeriodTorusHigherHomology.formalMixedSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [PeriodTorusHigherHomology.formalMap_mixedSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 4
              3).hom
          (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
            (SingularMayerVietoris.affineChainMap p 2 a)
            (SingularMayerVietoris.affineChainMap q 1 b)) +
        PeriodTorusHigherHomology.crossProductSwapHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
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
  rw [PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_affineChainMap, SingularHomology.productAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, PeriodTorusHigherHomology.crossProductSwapHomotopy_affineChainMap,
    SingularHomology.crossProductTriangle_affineChainMap, SingularHomology.crossProductEdge_affineChainMap,
    PeriodTorusHigherHomology.inducedChain_swap_productAffineChainMap, ← map_add, PeriodTorusHigherHomology.formalMixedSwapHomotopy_boundary,
    PeriodTorusHigherHomology.formalMixedSwapDefect_apply, map_sub]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y 1) :
    ((SingularChains.singularComplex (X × Y)).d 4 3).hom (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y a b) +
        PeriodTorusHigherHomology.crossProductSwapHomotopy X Y (((SingularChains.singularComplex X).d 2 1).hom a) b =
      SingularHomology.crossProductTriangle X Y 1 a b -
        SingularChains.inducedChain ContinuousMap.prodSwap 3 (SingularHomology.crossProductEdge Y X 2 b a) := by
  have h :
    SingularHomology.integerBilinearPostcompose (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y)
          ((SingularChains.singularComplex (X × Y)).d 4 3).hom +
        SingularHomology.integerBilinearPrecompose (PeriodTorusHigherHomology.crossProductSwapHomotopy X Y)
          ((SingularChains.singularComplex X).d 2 1).hom LinearMap.id =
      SingularHomology.crossProductTriangle X Y 1 -
        SingularHomology.integerBilinearPostcompose (SingularHomology.integerBilinearFlip (SingularHomology.crossProductEdge Y X 2))
          (SingularChains.inducedChain ContinuousMap.prodSwap 3) := by
    apply SingularHomology.chainBilinearMap_ext X Y 2 1
    intro σ τ
    have hstd :=
      PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_affine 2 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 3) hstd
    simpa only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularHomology.integerBilinearFlip_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, SingularChains.inducedChain_boundary,
      PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_natural, PeriodTorusHigherHomology.crossProductSwapHomotopy_natural,
      PeriodTorusHigherHomology.inducedChain_prodMap_swap, SingularHomology.crossProductTriangle_natural, SingularHomology.crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_of_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 2)
    (ha : ((SingularChains.singularComplex X).d 2 1).hom a = 0) (b : SingularChains.Chains Y 1) :
    ((SingularChains.singularComplex (X × Y)).d 4 3).hom (PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y a b) =
      SingularHomology.crossProductTriangle X Y 1 a b -
        SingularChains.inducedChain ContinuousMap.prodSwap 3 (SingularHomology.crossProductEdge Y X 2 b a) := by
  simpa only [ha, map_zero, LinearMap.zero_apply, add_zero] using
    PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary a b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.crossProductTwoOneCycles (X Y : Type) [TopologicalSpace X]
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
@[simp]

theorem PeriodTorusHigherHomology.crossProductTwoOneCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1) :
    (PeriodTorusHigherHomology.crossProductTwoOneCycles X Y a b).1 = SingularHomology.crossProductTriangle X Y 1 a.1 b.1 :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.crossProductHomologyTwoOne (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Y 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology (X × Y) 3 :=
  SingularHomology.integerBilinearPostcompose (SingularHomology.integerBilinearFlip (SingularHomology.crossProductHomology Y X 2))
    (SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.crossProductHomologyTwoOne_apply (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 2)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    PeriodTorusHigherHomology.crossProductHomologyTwoOne X Y a b =
      SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3
        (SingularHomology.crossProductHomology Y X 2 b a) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
@[simp]

theorem PeriodTorusHigherHomology.crossProductHomologyTwoOne_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1) :
    PeriodTorusHigherHomology.crossProductHomologyTwoOne X Y
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) 1 b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y)) 3
        (PeriodTorusHigherHomology.crossProductTwoOneCycles X Y a b) := by
  rw [PeriodTorusHigherHomology.crossProductHomologyTwoOne_apply, SingularHomology.crossProductHomology_cycleClass]
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
  refine ⟨PeriodTorusHigherHomology.crossProductMixedSwapHomotopy X Y a.1 b.1, ?_⟩
  simp only [PeriodTorusHigherHomology.crossProductTwoOneCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val,
    SingularHomology.crossProductCycles_val]
  exact
    PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_of_cycle a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 a)
      b.1

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductCycleClasses_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Z) 1) :
    (HomologicalComplex.homologyMap
            (SingularChains.singularChainMap (Homeomorph.prodAssoc X Y Z : C(_, _))) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex ((X × Y) × Z)) 3
          (PeriodTorusHigherHomology.crossProductTwoOneCycles (X × Y) Z (SingularHomology.crossProductCycles X Y 1 a b) c)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (X × (Y × Z))) 3
        (SingularHomology.crossProductCycles X (Y × Z) 2 a (SingularHomology.crossProductCycles Y Z 1 b c)) := by
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (SingularChains.singularComplex (X × (Y × Z))) 3 _ _).mpr
  refine ⟨PeriodTorusHigherHomology.crossProductAssociatorHomotopy X Y Z 1 a.1 b.1 c.1, ?_⟩
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, PeriodTorusHigherHomology.crossProductTwoOneCycles_val,
    SingularHomology.crossProductCycles_val]
  exact
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_of_cycle 1 a.1 b.1 c.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Z) 1 c)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductHomology_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc X Y Z : C(_, _)) 3
        (PeriodTorusHigherHomology.crossProductHomologyTwoOne (X × Y) Z (SingularHomology.crossProductHomology X Y 1 a b) c) =
      SingularHomology.crossProductHomology X (Y × Z) 2 a (SingularHomology.crossProductHomology Y Z 1 b c) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Y) 1
      b
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Z) 1
      c
  rw [SingularHomology.crossProductHomology_cycleClass, PeriodTorusHigherHomology.crossProductHomologyTwoOne_cycleClass,
    SingularHomology.crossProductHomology_cycleClass, SingularHomology.crossProductHomology_cycleClass]
  exact PeriodTorusHigherHomology.crossProductCycleClasses_associative a b c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

def PeriodTorusHigherHomology.crossProductCyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z)) :=
  ContinuousMap.prodSwap.comp ((Homeomorph.prodAssoc Y Z X).symm : C(_, _))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductCyclicMap_assoc_swap {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    (PeriodTorusHigherHomology.crossProductCyclicMap X Y Z).comp
        ((Homeomorph.prodAssoc Y Z X : C(_, _)).comp ContinuousMap.prodSwap) =
      ContinuousMap.id (X × (Y × Z)) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

theorem PeriodTorusHigherHomology.crossProductHomology_cyclic {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    SingularHomology.crossProductHomology X (Y × Z) 2 a (SingularHomology.crossProductHomology Y Z 1 b c) =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.crossProductCyclicMap X Y Z) 3
        (SingularHomology.crossProductHomology Y (Z × X) 2 b (SingularHomology.crossProductHomology Z X 1 c a)) := by
  have h := PeriodTorusHigherHomology.crossProductHomology_associative b c a
  rw [PeriodTorusHigherHomology.crossProductHomologyTwoOne_apply] at h
  have h' :=
    congrArg (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.crossProductCyclicMap X Y Z) 3) h
  have hmap :
    (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.crossProductCyclicMap X Y Z) 3).comp
        ((SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc Y Z X : C(_, _)) 3).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.prodSwap : C(X × (Y × Z), (Y × Z) × X)) 3)) =
      LinearMap.id := by
    rw [← SingularHomology.singularHomologyMap_comp, ← SingularHomology.singularHomologyMap_comp, PeriodTorusHigherHomology.crossProductCyclicMap_assoc_swap,
      SingularHomology.singularHomologyMap_id]
  exact
    (LinearMap.congr_fun hmap
          (SingularHomology.crossProductHomology X (Y × Z) 2 a (SingularHomology.crossProductHomology Y Z 1 b c))).symm.trans
      h'


section

open SingularHomology


attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCycles_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap (f.prodMap g))
        (n + 1) (crossProductCycles X Y n a b) =
      crossProductCycles X' Y' n
        (SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap f) 1 a)
        (SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap g) n b) :=
  by
  apply Subtype.ext
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, crossProductCycles_val]
  exact crossProductEdge_natural f g n a.1 b.1

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : (SingularChains.singularComplex X).homology 1)
    (b : (SingularChains.singularComplex Y).homology n) :
    (HomologicalComplex.homologyMap (SingularChains.singularChainMap (f.prodMap g)) (n + 1)).hom
        (crossProductHomology X Y n a b) =
      crossProductHomology X' Y' n
        ((HomologicalComplex.homologyMap (SingularChains.singularChainMap f) 1).hom a)
        ((HomologicalComplex.homologyMap (SingularChains.singularChainMap g) n).hom b) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Y) n
      b
  rw [crossProductHomology_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, crossProductHomology_cycleClass,
    crossProductCycles_natural]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_snd {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(X × Y, Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      0 := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology Unit 1) :=
    point_homology_subsingleton 1 (by decide)
  let f : C(X, Unit) := ContinuousMap.const X ()
  have hz : SingularMayerVietoris.singularHomologyMap f 1 a = 0 := Subsingleton.elim _ _
  have hn := crossProductHomology_natural f (ContinuousMap.id Y) n a b
  change
    SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      crossProductHomology Unit Y n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id Y) n b) at hn
  rw [hz, map_zero, LinearMap.zero_apply] at hn
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1)
          (SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
            (crossProductHomology X Y n a b)) := by
      exact
        LinearMap.congr_fun
          (singularHomologyMap_comp (f.prodMap (ContinuousMap.id Y))
            (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1))
          (crossProductHomology X Y n a b)
    _ = 0 := by rw [hn, map_zero]

end

end Mathoverflow1973
