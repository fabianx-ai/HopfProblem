/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
import Lib.AlgebraicTopology.SingularHomology.CircleProduct

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

1. *Bilinear plumbing.* `integerBilinearRightApply`, `integerBilinearFlip`,
   `integerBilinearPostcompose`, `integerBilinearPrecompose` package currying and composition
   of bilinear maps over `ℤ`; `chainBilinearLift` extends a simplex-wise bilinear assignment
   to the free abelian chain groups (`chainBilinearMap_ext` for uniqueness).
2. *The formal product.* `formalEdgeCrossProduct` triangulates the prism `Δ¹ × Δⁿ` (and
   `formalTriangleCrossProduct` the product `Δ² × Δⁿ`) into affine simplices, with the Leibniz
   boundary identities `formalBoundary_edgeCrossProduct`,
   `formalBoundary_triangleCrossProduct`; `formalPointCrossProduct` is the degree-zero
   companion.
3. *The chain-level product.* `crossProductEdge` sends a singular edge and a singular
   `n`-simplex to the product chain pushed forward along `σ.prodMap τ`
   (`crossProductEdge_simplex`); it is natural (`crossProductEdge_natural`) and satisfies the
   Leibniz rule `crossProductEdge_boundary`; likewise `crossProductTriangle` in left degree
   two, which is the prism operator for the homotopy-invariance arguments of the Hurewicz
   lane.
4. *Descent to homology.* A cycle times a cycle is a cycle (`crossProductCycles`); a boundary
   times a cycle is a boundary (`crossProductCycleClasses_boundary_right`,
   `crossProductHomologyCycles_boundary_left`), so the product descends twice
   (`crossProductHomologyFixed`, `crossProductHomologyCycles`, then `homologyDesc`) to
   `crossProductHomology`, with `crossProductHomology_cycleClass` computing it on classes.
5. *Degenerations at `n = 0`.* `crossProductEdge_zero_eq_zeroRight` identifies the
   degree-zero product with point insertion, and
   `crossProductHomology_pointClass_right` computes it on point classes.

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


noncomputable section

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
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : integerBilinearRightApply F b a = F a b :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The flip of a bilinear map: `integerBilinearFlip F b a = F a b`, as a bilinear map
`B →ₗ[ℤ] A →ₗ[ℤ] C`. -/
def SingularHomology.integerBilinearFlip {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) : B →ₗ[ℤ] A →ₗ[ℤ] C
    where
  toFun := integerBilinearRightApply F
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
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : integerBilinearFlip F b a = F a b :=
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
    chainBilinearLift X Y p q f (SingularChains.simplexChain X p σ) =
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
    chainBilinearLift X Y p q f (SingularChains.simplexChain X p σ)
        (SingularChains.simplexChain Y q τ) =
      f σ τ := by rw [chainBilinearLift_simplex_left, SingularChains.chainLift_simplex]

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
    zeroSimplexValue (f.comp σ) = f (zeroSimplexValue σ) :=
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
  chainBilinearLift X Y 0 n fun σ τ =>
    SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertLeft (zeroSimplexValue σ)).comp τ)

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
    crossProductZeroLeft X Y n (SingularChains.simplexChain X 0 σ) =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft (Y := Y) (zeroSimplexValue σ)) n := by
  apply SingularChains.chainMap_ext Y n
  intro τ
  rw [crossProductZeroLeft, chainBilinearLift_simplex, SingularChains.inducedChain_simplex]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplex generators, `crossProductZeroLeft` sends `σ, τ` to the chain of
`τ` composed with `crossInsertLeft (zeroSimplexValue σ)`. -/
@[simp]
theorem SingularHomology.crossProductZeroLeft_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 0)
    (τ : SingularChains.SingularSimplex Y n) :
    crossProductZeroLeft X Y n (SingularChains.simplexChain X 0 σ)
        (SingularChains.simplexChain Y n τ) =
      SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertLeft (zeroSimplexValue σ)).comp τ) := by
  rw [crossProductZeroLeft_simplex_left, SingularChains.inducedChain_simplex]

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
    simp only [integerBilinearRightApply_apply, crossProductZeroRight, chainBilinearLift_simplex,
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
    crossProductZeroRight X Y n (SingularChains.simplexChain X n σ)
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
    SingularChains.inducedChain (f.prodMap g) n (crossProductZeroLeft X Y n a b) =
      crossProductZeroLeft X' Y' n (SingularChains.inducedChain f 0 a)
        (SingularChains.inducedChain g n b) := by
  have h :
    (SingularChains.inducedChain (f.prodMap g) n).comp
        (integerBilinearRightApply (crossProductZeroLeft X Y n) b) =
      (integerBilinearRightApply (crossProductZeroLeft X' Y' n)
            (SingularChains.inducedChain g n b)).comp
        (SingularChains.inducedChain f 0) := by
    apply SingularChains.chainMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, integerBilinearRightApply_apply,
      SingularChains.inducedChain_simplex, crossProductZeroLeft_simplex_left,
      zeroSimplexValue_comp]
    exact SingularHomology.inducedChain_crossInsertLeft f g (zeroSimplexValue σ) n b
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
    integerBilinearPostcompose F g a b = g (F a b) :=
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
    integerBilinearPrecompose F f g a b = F (f a) (g b) :=
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
    formalBilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      f v w := by simp [formalBilinearLift]

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
    formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d =
      SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) d

/-- `formalPointCrossProduct` on generators `v, w` is the formal map of `w ↦ (v 0, w)`. -/
@[simp]
theorem SingularHomology.formalPointCrossProduct_simplex {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (w : Fin (q + 1) → W) :
    formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (fun i => (v 0, w i)) := by
  rw [formalPointCrossProduct_simplex_left, SingularMayerVietoris.formalMap_simplex]
  rfl

/-- The formal point cross product at a `0`-simplex `w` in the right argument is the
formal chain of the constant pair map. -/
@[simp]
theorem SingularHomology.formalPointCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (w : Fin 1 → W) :
    formalPointCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 1 c := by
  have h :
    (formalPointCrossProduct (V := V) 0).flip (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 1 := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.flip_apply, formalPointCrossProduct_simplex,
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
    SingularMayerVietoris.formalBoundary (q + 1) (formalPointCrossProduct (q + 1) c d) =
      formalPointCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  have h :
    (formalPointCrossProduct (V := V) (W := W) (q + 1)).compr₂
        (SingularMayerVietoris.formalBoundary (q + 1)) =
      (formalPointCrossProduct q).compl₂ (SingularMayerVietoris.formalBoundary (q + 1)) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      formalPointCrossProduct_simplex_left]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (v 0, z)) (q + 1)
          (SingularMayerVietoris.formalSimplex w)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Naturality of the formal point cross product under maps `f : V → V'`, `g : W → W'`. -/
theorem SingularHomology.formalMap_pointCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (c : SingularMayerVietoris.FormalChains V 1)
    (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 1) (formalPointCrossProduct q c d) =
      formalPointCrossProduct q (SingularMayerVietoris.formalMap f 1 c)
        (SingularMayerVietoris.formalMap g (q + 1) d) := by
  have h :
    (formalPointCrossProduct (V := V) (W := W) q).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) (q + 1)) =
      ((formalPointCrossProduct q).compl₂ (SingularMayerVietoris.formalMap g (q + 1))).comp
        (SingularMayerVietoris.formalMap f 1) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      formalPointCrossProduct_simplex, SingularMayerVietoris.formalMap_simplex]
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
    formalBilinearLift fun v w =>
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (formalPointCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) -
          formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w)))

/-- The formal edge cross product at a `0`-simplex right argument `w` is
`formalMap (v ↦ (v, w 0))` applied to `c`. -/
@[simp]
theorem SingularHomology.formalEdgeCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (w : Fin 1 → W) :
    formalEdgeCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 2 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

/-- On an edge generator `v` and a `(q+1)`-simplex `w`, the formal edge cross product
is the sum of the two prism terms of the edge. -/
@[simp]
theorem SingularHomology.formalEdgeCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (formalPointCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) -
          formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w))) :=
  formalBilinearLift_simplex _ _ _

/-- The boundary of the formal edge cross product at right degree `0` is the point
cross product of the edge's boundary. -/
theorem SingularHomology.formalBoundary_edgeCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalBoundary 1 (formalEdgeCrossProduct 0 c d) =
      formalPointCrossProduct 0 (SingularMayerVietoris.formalBoundary 1 c) d := by
  have h :
    (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂ (SingularMayerVietoris.formalBoundary 1) =
      (formalPointCrossProduct 0).comp (SingularMayerVietoris.formalBoundary 1) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      formalEdgeCrossProduct_zero_simplex_right, formalPointCrossProduct_zero_simplex_right]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (z, w 0)) 1
          (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The boundary law for the formal edge cross product: `∂(e × c) = ∂e × c - e × ∂c`
at the formal-chain level. -/
theorem SingularHomology.formalBoundary_edgeCrossProduct {V W : Type*} :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 2)
      (d : SingularMayerVietoris.FormalChains W (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) c d) =
        formalPointCrossProduct (q + 1) (SingularMayerVietoris.formalBoundary 1 c) d -
          formalEdgeCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) 1).compr₂
          (SingularMayerVietoris.formalBoundary 2) =
        (formalPointCrossProduct 1).comp (SingularMayerVietoris.formalBoundary 1) -
          (formalEdgeCrossProduct 0).compl₂ (SingularMayerVietoris.formalBoundary 1) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary 2
            (formalEdgeCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalEdgeCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary 1
            (formalPointCrossProduct 1
                (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) -
              formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_sub, formalBoundary_pointCrossProduct, formalBoundary_edgeCrossProduct_zero,
          sub_self]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) (q + 2)).compr₂
          (SingularMayerVietoris.formalBoundary (q + 3)) =
        (formalPointCrossProduct (q + 2)).comp (SingularMayerVietoris.formalBoundary 1) -
          (formalEdgeCrossProduct (q + 1)).compl₂
            (SingularMayerVietoris.formalBoundary (q + 2)) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary (q + 3)
            (formalEdgeCrossProduct (q + 2) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalEdgeCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary (q + 2)
            (formalPointCrossProduct (q + 2)
                (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) -
              formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_sub, formalBoundary_pointCrossProduct, ih,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, sub_zero, sub_self]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Naturality of the formal edge cross product under maps `f : V → V'`, `g : W → W'`. -/
theorem SingularHomology.formalMap_edgeCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 2)
      (d : SingularMayerVietoris.FormalChains W (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (formalEdgeCrossProduct q c d) =
        formalEdgeCrossProduct q (SingularMayerVietoris.formalMap f 2 c)
          (SingularMayerVietoris.formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) 2) =
        ((formalEdgeCrossProduct 0).compl₂ (SingularMayerVietoris.formalMap g 1)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        formalEdgeCrossProduct_zero_simplex_right, SingularMayerVietoris.formalMap_simplex]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) (q + 1)).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) (q + 3)) =
        ((formalEdgeCrossProduct (q + 1)).compl₂ (SingularMayerVietoris.formalMap g (q + 2))).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularMayerVietoris.formalMap_simplex, formalEdgeCrossProduct_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, formalMap_pointCrossProduct, ih, SingularMayerVietoris.formalMap_boundary,
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
    productAffineSimplex v (SingularMayerVietoris.stdVertices n i) = v i := by
  apply Prod.ext <;> simp [productAffineSimplex, SingularMayerVietoris.stdVertices]

/-- The `i`-th face of `productAffineSimplex v` is the product affine simplex of the
vertex pairs with `v i` dropped. -/
theorem SingularHomology.productAffineSimplex_face {n p q : ℕ}
    (v : Fin (n + 2) → SingularChains.Simplex p × SingularChains.Simplex q) (i : Fin (n + 2)) :
    (productAffineSimplex v).comp (SingularChains.simplexFace n i) =
      productAffineSimplex (fun j => v (i.succAbove j)) := by
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
        (productAffineSimplex z) =
      productAffineSimplex
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
      (productAffineSimplex v)

/-- `productAffineChainMap` on a generator `v` is the chain of `productAffineSimplex v`. -/
@[simp]
theorem SingularHomology.productAffineChainMap_simplex (p q n : ℕ)
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    productAffineChainMap p q n (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
        (productAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

/-- The product affine chain map commutes with the formal boundary: `∂` of the affine
chain is the alternating sum of the face affine simplices. -/
theorem SingularHomology.productAffineChainMap_boundary (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 1)
            n).hom
        (productAffineChainMap p q (n + 1) c) =
      productAffineChainMap p q n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d
              (n + 1) n).hom).comp
        (productAffineChainMap p q (n + 1)) =
      (productAffineChainMap p q n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d
              (n + 1) n).hom
          (productAffineChainMap p q (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [productAffineChainMap_simplex, SingularChains.boundary_simplex]
    change
      _ =
        productAffineChainMap p q n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, productAffineChainMap_simplex, productAffineSimplex_face]
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
        m (productAffineChainMap p q m c) =
      productAffineChainMap r s m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1) c) := by
  have h :
    (SingularChains.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              (SingularMayerVietoris.affineSimplex w))
            m).comp
        (productAffineChainMap p q m) =
      (productAffineChainMap r s m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      prodMap_productAffineSimplex]
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
  chainBilinearLift X Y 1 n fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) (n + 1)
      (productAffineChainMap 1 n (n + 1)
        (formalEdgeCrossProduct n
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
    crossProductEdge X Y n (SingularChains.simplexChain X 1 σ) (SingularChains.simplexChain Y n τ) =
      SingularChains.inducedChain (σ.prodMap τ) (n + 1)
        (productAffineChainMap 1 n (n + 1)
          (formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainBilinearLift_simplex X Y 1 n _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductEdge` is natural in both space maps. -/
theorem SingularHomology.crossProductEdge_natural {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (n : ℕ) (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y n) :
    SingularChains.inducedChain (f.prodMap g) (n + 1) (crossProductEdge X Y n a b) =
      crossProductEdge X' Y' n (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g n b) := by
  have h :
    integerBilinearPostcompose (crossProductEdge X Y n)
        (SingularChains.inducedChain (f.prodMap g) (n + 1)) =
      integerBilinearPrecompose (crossProductEdge X' Y' n) (SingularChains.inducedChain f 1)
        (SingularChains.inducedChain g n) := by
    apply chainBilinearMap_ext X Y 1 n
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, crossProductEdge_simplex]
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
    productAffineSimplex (fun i => (a, v i)) =
      (SingularHomology.crossInsertLeft a).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
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
    crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 0 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      productAffineChainMap p q n (formalPointCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 0) (SingularMayerVietoris.affineChainMap q n) =
      integerBilinearPostcompose (formalPointCrossProduct n) (productAffineChainMap p q n) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductZeroLeft_simplex]
    have hv : zeroSimplexValue (SingularMayerVietoris.affineSimplex v) = v 0 :=
      SingularMayerVietoris.affineSimplex_vertex v 0
    rw [hv]
    calc
      _ =
          productAffineChainMap p q n
            (SingularMayerVietoris.formalSimplex (fun i => (v 0, w i))) := by
        rw [productAffineChainMap_simplex, productAffineSimplex_point_left]
      _ = _ := congrArg (productAffineChainMap p q n) (formalPointCrossProduct_simplex n v w).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductEdge` computed on an edge chain `a` and a formal chain `b` equals the
induced chain of the edge cross product on formal chains. -/
theorem SingularHomology.crossProductEdge_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 1)) :
    crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      productAffineChainMap p q (n + 1) (formalEdgeCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q n) =
      integerBilinearPostcompose (formalEdgeCrossProduct n) (productAffineChainMap p q (n + 1)) :=
    by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductEdge_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            (n + 2)
            (formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
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
    formalBilinearLift fun v w =>
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 3)
        (formalEdgeCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) +
          formalTriangleCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w)))

/-- The formal triangle cross product at a `0`-simplex right argument `w` is
`formalMap (v ↦ (v, w 0))` applied to `c`. -/
@[simp]
theorem SingularHomology.formalTriangleCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (w : Fin 1 → W) :
    formalTriangleCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 3 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

/-- On a triangle generator `v` and a `(q+1)`-simplex `w`, the formal triangle cross
product is the signed sum of the three prism terms. -/
@[simp]
theorem SingularHomology.formalTriangleCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
    (v : Fin 3 → V) (w : Fin (q + 2) → W) :
    formalTriangleCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 3)
        (formalEdgeCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) +
          formalTriangleCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w))) :=
  formalBilinearLift_simplex _ _ _

/-- The boundary of the formal triangle cross product at right degree `0` is the point
cross product of the triangle's boundary. -/
theorem SingularHomology.formalBoundary_triangleCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalBoundary 2 (formalTriangleCrossProduct 0 c d) =
      formalEdgeCrossProduct 0 (SingularMayerVietoris.formalBoundary 2 c) d := by
  have h :
    (formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
        (SingularMayerVietoris.formalBoundary 2) =
      (formalEdgeCrossProduct 0).comp (SingularMayerVietoris.formalBoundary 2) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      formalTriangleCrossProduct_zero_simplex_right, formalEdgeCrossProduct_zero_simplex_right]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (z, w 0)) 2
          (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The boundary law for the formal triangle cross product:
`∂(t × c) = ∂t × c + t × ∂c` (sign by left degree `2`) at the formal-chain level. -/
theorem SingularHomology.formalBoundary_triangleCrossProduct {V W : Type*} :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 3)
      (d : SingularMayerVietoris.FormalChains W (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 3) (formalTriangleCrossProduct (q + 1) c d) =
        formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalBoundary 2 c) d +
          formalTriangleCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) 1).compr₂
          (SingularMayerVietoris.formalBoundary 3) =
        (formalEdgeCrossProduct 1).comp (SingularMayerVietoris.formalBoundary 2) +
          (formalTriangleCrossProduct 0).compl₂ (SingularMayerVietoris.formalBoundary 1) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary 3
            (formalTriangleCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalTriangleCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary 2
            (formalEdgeCrossProduct 1
                (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) +
              formalTriangleCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_add, formalBoundary_edgeCrossProduct,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
          formalBoundary_triangleCrossProduct_zero, neg_add_cancel]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) (q + 2)).compr₂
          (SingularMayerVietoris.formalBoundary (q + 4)) =
        (formalEdgeCrossProduct (q + 2)).comp (SingularMayerVietoris.formalBoundary 2) +
          (formalTriangleCrossProduct (q + 1)).compl₂
            (SingularMayerVietoris.formalBoundary (q + 2)) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary (q + 4)
            (formalTriangleCrossProduct (q + 2) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalTriangleCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary (q + 3)
            (formalEdgeCrossProduct (q + 2)
                (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) +
              formalTriangleCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_add, formalBoundary_edgeCrossProduct,
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
      SingularMayerVietoris.formalMap (Prod.map f g) (q + 3) (formalTriangleCrossProduct q c d) =
        formalTriangleCrossProduct q (SingularMayerVietoris.formalMap f 3 c)
          (SingularMayerVietoris.formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) 3) =
        ((formalTriangleCrossProduct 0).compl₂ (SingularMayerVietoris.formalMap g 1)).comp
          (SingularMayerVietoris.formalMap f 3) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        formalTriangleCrossProduct_zero_simplex_right, SingularMayerVietoris.formalMap_simplex]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) (q + 1)).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) (q + 4)) =
        ((formalTriangleCrossProduct (q + 1)).compl₂
              (SingularMayerVietoris.formalMap g (q + 2))).comp
          (SingularMayerVietoris.formalMap f 3) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularMayerVietoris.formalMap_simplex, formalTriangleCrossProduct_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_add, formalMap_edgeCrossProduct, ih, SingularMayerVietoris.formalMap_boundary,
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
  chainBilinearLift X Y 2 n fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) (n + 2)
      (productAffineChainMap 2 n (n + 2)
        (formalTriangleCrossProduct n
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
    crossProductTriangle X Y n (SingularChains.simplexChain X 2 σ)
        (SingularChains.simplexChain Y n τ) =
      SingularChains.inducedChain (σ.prodMap τ) (n + 2)
        (productAffineChainMap 2 n (n + 2)
          (formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainBilinearLift_simplex X Y 2 n _ σ τ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductTriangle` is natural in both space maps. -/
theorem SingularHomology.crossProductTriangle_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y n) :
    SingularChains.inducedChain (f.prodMap g) (n + 2) (crossProductTriangle X Y n a b) =
      crossProductTriangle X' Y' n (SingularChains.inducedChain f 2 a)
        (SingularChains.inducedChain g n b) := by
  have h :
    integerBilinearPostcompose (crossProductTriangle X Y n)
        (SingularChains.inducedChain (f.prodMap g) (n + 2)) =
      integerBilinearPrecompose (crossProductTriangle X' Y' n) (SingularChains.inducedChain f 2)
        (SingularChains.inducedChain g n) := by
    apply chainBilinearMap_ext X Y 2 n
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, crossProductTriangle_simplex]
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
    crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      productAffineChainMap p q (n + 2) (formalTriangleCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q n) =
      integerBilinearPostcompose (formalTriangleCrossProduct n)
        (productAffineChainMap p q (n + 2)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductTriangle_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q (n + 2)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            (n + 3)
            (formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_triangleCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
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
        (crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) 0
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q 0 b)) =
      crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) 0
        (((SingularChains.singularComplex (SingularChains.Simplex p)).d 2 1).hom
          (SingularMayerVietoris.affineChainMap p 2 a))
        (SingularMayerVietoris.affineChainMap q 0 b) := by
  rw [crossProductTriangle_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_triangleCrossProduct_zero, SingularMayerVietoris.affineChainMap_boundary,
    crossProductEdge_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On formal chains, the boundary of the triangle cross product satisfies
`∂(a × b) = ∂a × b + a × ∂b`. -/
theorem SingularHomology.crossProductTriangle_boundary_affine (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 3)
            (n + 2)).hom
        (crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q (n + 1) b)) =
      crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d 2 1).hom
            (SingularMayerVietoris.affineChainMap p 2 a))
          (SingularMayerVietoris.affineChainMap q (n + 1) b) +
        crossProductTriangle (SingularChains.Simplex p) (SingularChains.Simplex q) n
          (SingularMayerVietoris.affineChainMap p 2 a)
          (((SingularChains.singularComplex (SingularChains.Simplex q)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap q (n + 1) b)) := by
  rw [crossProductTriangle_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_triangleCrossProduct, map_add, SingularMayerVietoris.affineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductEdge_affineChainMap,
    crossProductTriangle_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductTriangle a b` when `b` is a `0`-chain is
`crossProductEdge` of `∂a` and `b`. -/
theorem SingularHomology.crossProductTriangle_boundary_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 2)
    (b : SingularChains.Chains Y 0) :
    ((SingularChains.singularComplex (X × Y)).d 2 1).hom (crossProductTriangle X Y 0 a b) =
      crossProductEdge X Y 0 (((SingularChains.singularComplex X).d 2 1).hom a) b := by
  have h :
    integerBilinearPostcompose (crossProductTriangle X Y 0)
        ((SingularChains.singularComplex (X × Y)).d 2 1).hom =
      integerBilinearPrecompose (crossProductEdge X Y 0)
        ((SingularChains.singularComplex X).d 2 1).hom LinearMap.id := by
    apply chainBilinearMap_ext X Y 2 0
    intro σ τ
    have hstd :=
      crossProductTriangle_boundary_zero_affine 2 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 1) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.id_apply, SingularChains.inducedChain_boundary, crossProductTriangle_natural,
      crossProductEdge_natural, SingularMayerVietoris.affineChainMap_stdVertices,
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
        (crossProductTriangle X Y (n + 1) a b) =
      crossProductEdge X Y (n + 1) (((SingularChains.singularComplex X).d 2 1).hom a) b +
        crossProductTriangle X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  have h :
    integerBilinearPostcompose (crossProductTriangle X Y (n + 1))
        ((SingularChains.singularComplex (X × Y)).d (n + 3) (n + 2)).hom =
      integerBilinearPrecompose (crossProductEdge X Y (n + 1))
          ((SingularChains.singularComplex X).d 2 1).hom LinearMap.id +
        integerBilinearPrecompose (crossProductTriangle X Y n) LinearMap.id
          ((SingularChains.singularComplex Y).d (n + 1) n).hom := by
    apply chainBilinearMap_ext X Y 2 (n + 1)
    intro σ τ
    have hstd :=
      crossProductTriangle_boundary_affine 2 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) (n + 2)) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, SingularChains.inducedChain_boundary,
      crossProductTriangle_natural, crossProductEdge_natural,
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
        (crossProductTriangle X Y n a b) =
      crossProductEdge X Y n (((SingularChains.singularComplex X).d 2 1).hom a) b := by
  cases n with
  | zero => exact crossProductTriangle_boundary_zero a b
  | succ
    n =>
    have hb' : ((SingularChains.singularComplex Y).d (n + 1) n).hom b = 0 := by
      simpa only [Nat.succ_sub_one] using hb
    simp only [crossProductTriangle_boundary, hb', map_zero, add_zero]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductEdge a b` at right degree `0` on formal chains is the
point cross product of `∂a`. -/
theorem SingularHomology.crossProductEdge_boundary_zero_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 1) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d 1
            0).hom
        (crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) 0
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 0 b)) =
      crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) 0
        (((SingularChains.singularComplex (SingularChains.Simplex p)).d 1 0).hom
          (SingularMayerVietoris.affineChainMap p 1 a))
        (SingularMayerVietoris.affineChainMap q 0 b) := by
  rw [crossProductEdge_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_edgeCrossProduct_zero, SingularMayerVietoris.affineChainMap_boundary,
    crossProductZeroLeft_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On formal chains, the boundary of the edge cross product satisfies
`∂(a × b) = ∂a × b - a × ∂b`. -/
theorem SingularHomology.crossProductEdge_boundary_affine (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 2)
            (n + 1)).hom
        (crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q (n + 1) b)) =
      crossProductZeroLeft (SingularChains.Simplex p) (SingularChains.Simplex q) (n + 1)
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d 1 0).hom
            (SingularMayerVietoris.affineChainMap p 1 a))
          (SingularMayerVietoris.affineChainMap q (n + 1) b) -
        crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q) n
          (SingularMayerVietoris.affineChainMap p 1 a)
          (((SingularChains.singularComplex (SingularChains.Simplex q)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap q (n + 1) b)) := by
  rw [crossProductEdge_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_edgeCrossProduct, map_sub, SingularMayerVietoris.affineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductZeroLeft_affineChainMap,
    crossProductEdge_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `crossProductEdge a b` when `b` is a `0`-chain is
`crossProductZeroLeft` of `∂a` and `b`. -/
theorem SingularHomology.crossProductEdge_boundary_zero {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 0) :
    ((SingularChains.singularComplex (X × Y)).d 1 0).hom (crossProductEdge X Y 0 a b) =
      crossProductZeroLeft X Y 0 (((SingularChains.singularComplex X).d 1 0).hom a) b := by
  have h :
    integerBilinearPostcompose (crossProductEdge X Y 0)
        ((SingularChains.singularComplex (X × Y)).d 1 0).hom =
      integerBilinearPrecompose (crossProductZeroLeft X Y 0)
        ((SingularChains.singularComplex X).d 1 0).hom LinearMap.id := by
    apply chainBilinearMap_ext X Y 1 0
    intro σ τ
    have hstd :=
      crossProductEdge_boundary_zero_affine 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) 0) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.id_apply, SingularChains.inducedChain_boundary, crossProductEdge_natural,
      crossProductZeroLeft_natural, SingularMayerVietoris.affineChainMap_stdVertices,
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
        (crossProductEdge X Y (n + 1) a b) =
      crossProductZeroLeft X Y (n + 1) (((SingularChains.singularComplex X).d 1 0).hom a) b -
        crossProductEdge X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  have h :
    integerBilinearPostcompose (crossProductEdge X Y (n + 1))
        ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom =
      integerBilinearPrecompose (crossProductZeroLeft X Y (n + 1))
          ((SingularChains.singularComplex X).d 1 0).hom LinearMap.id -
        integerBilinearPrecompose (crossProductEdge X Y n) LinearMap.id
          ((SingularChains.singularComplex Y).d (n + 1) n).hom := by
    apply chainBilinearMap_ext X Y 1 (n + 1)
    intro σ τ
    have hstd :=
      crossProductEdge_boundary_affine 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστ := congrArg (SingularChains.inducedChain (σ.prodMap τ) (n + 1)) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_sub, SingularChains.inducedChain_boundary,
      crossProductEdge_natural, crossProductZeroLeft_natural,
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
    ((SingularChains.singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b) = 0 := by
  cases n with
  | zero =>
    have h := crossProductEdge_boundary_zero a b
    rw [ha, map_zero, LinearMap.zero_apply] at h
    exact h
  | succ
    n =>
    have hb' : ((SingularChains.singularComplex Y).d (n + 1) n).hom b = 0 := by
      simpa only [Nat.succ_sub_one] using hb
    simp only [crossProductEdge_boundary, ha, hb', map_zero, LinearMap.zero_apply, sub_self]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If `a` is a `1`-cycle, `∂(a × b) = -a × ∂b` for the edge cross product. -/
theorem SingularHomology.crossProductEdge_boundary_of_left_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1)
    (ha : ((SingularChains.singularComplex X).d 1 0).hom a = 0)
    (b : SingularChains.Chains Y (n + 1)) :
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductEdge X Y (n + 1) a b) =
      -crossProductEdge X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  simp only [crossProductEdge_boundary, ha, map_zero, LinearMap.zero_apply, zero_sub]

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
    homologyBoundaries K n ≤ LinearMap.ker f := by
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
  ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- `homologyDesc f hf` sends the class of a cycle `c` to `f c`. -/
@[simp]
theorem SingularHomology.homologyDesc_cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    homologyDesc K n f hf (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = f c := by
  have h :=
    congrArg (fun q => q.hom (Submodule.Quotient.mk c)) (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)) h

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
          (n + 1) (crossProductEdge X Y n a.1 b.1)
          (by
            rw [Nat.add_sub_cancel]
            exact
              crossProductEdge_cycle n a.1 b.1
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex X) 1 a)
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex Y) n b))
      map_add' b
        c := by
        apply Subtype.ext
        exact (crossProductEdge X Y n a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (crossProductEdge X Y n a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) => f c.1)
        ((crossProductEdge X Y n).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) => f c.1)
        ((crossProductEdge X Y n).map_smul r a.1)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The underlying chain of `crossProductCycles a b` is `crossProductEdge a.1 b.1`. -/
@[simp]
theorem SingularHomology.crossProductCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    (crossProductCycles X Y n a b).1 = crossProductEdge X Y n a.1 b.1 :=
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
  integerBilinearPostcompose (crossProductCycles X Y n)
    (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
      (n + 1))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class-valued edge cross product vanishes when the right chain is a boundary. -/
theorem SingularHomology.crossProductCycleClasses_boundary_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularChains.Chains Y (n + 1)) :
    crossProductCycleClasses X Y n a
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex Y) n
          b) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨-crossProductEdge X Y (n + 1) a.1 b, ?_⟩
  change
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (-crossProductEdge X Y (n + 1) a.1 b) =
      crossProductEdge X Y n a.1 (((SingularChains.singularComplex Y).d (n + 1) n).hom b)
  rw [map_neg,
    crossProductEdge_boundary_of_left_cycle n a.1
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
  homologyDesc (SingularChains.singularComplex Y) n (crossProductCycleClasses X Y n a)
    (crossProductCycleClasses_boundary_right n a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductHomologyFixed a` sends the class of a cycle `b` to the class of
`crossProductCycles` on representatives. -/
@[simp]
theorem SingularHomology.crossProductHomologyFixed_cycleClass {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    crossProductHomologyFixed n a
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (crossProductCycles X Y n a b) :=
  homologyDesc_cycleClass _ _ _ _ b

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
  toFun a := crossProductHomologyFixed n a
  map_add' a
    b := by
    apply homologyLinearMap_ext (SingularChains.singularComplex Y) n
    intro c
    change
      crossProductHomologyFixed n (a + b)
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
            c) =
        crossProductHomologyFixed n a
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
              c) +
          crossProductHomologyFixed n b
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
              c)
    simp only [crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
              (SingularChains.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((crossProductCycleClasses X Y n).map_add a b)
  map_smul' r
    a := by
    apply homologyLinearMap_ext (SingularChains.singularComplex Y) n
    intro c
    simp only [LinearMap.smul_apply, RingHom.id_apply, crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
              (SingularChains.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((crossProductCycleClasses X Y n).map_smul r a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class-valued edge cross product vanishes when the left chain is a boundary. -/
theorem SingularHomology.crossProductCycleClasses_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    crossProductCycleClasses X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1 a)
        b =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨crossProductTriangle X Y n a b.1, ?_⟩
  exact
    crossProductTriangle_boundary_of_right_cycle n a b.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Y) n b)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology-valued edge cross product vanishes when the left `1`-chain is a
boundary. -/
theorem SingularHomology.crossProductHomologyCycles_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2) :
    crossProductHomologyCycles X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1
          a) =
      0 := by
  apply homologyLinearMap_ext (SingularChains.singularComplex Y) n
  intro b
  change
    crossProductHomologyFixed n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      0
  rw [crossProductHomologyFixed_cycleClass]
  exact crossProductCycleClasses_boundary_left n a b

/-! ### The cross product on homology -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology cross product `H_1(X) →ₗ[ℤ] H_n(Y) →ₗ[ℤ] H_{n+1}(X × Y)`. -/
def SingularHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
      (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (SingularChains.singularComplex X) 1 (crossProductHomologyCycles X Y n)
    (crossProductHomologyCycles_boundary_left n)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductHomology` on cycle classes `⟦a⟧`, `⟦b⟧` is the class of the edge
cross product `a × b`. -/
@[simp]
theorem SingularHomology.crossProductHomology_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    crossProductHomology X Y n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (crossProductCycles X Y n a b) := by
  rw [crossProductHomology, homologyDesc_cycleClass]
  exact crossProductHomologyFixed_cycleClass n a b

/-! ### Degenerations at degree zero -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- In right degree `0`, `crossProductEdge` coincides with `crossProductZeroRight`
(up to the degree identification). -/
theorem SingularHomology.crossProductEdge_zero_eq_zeroRight (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    crossProductEdge X Y 0 = crossProductZeroRight X Y 1 := by
  apply chainBilinearMap_ext X Y 1 0
  intro σ τ
  rw [crossProductEdge_simplex, formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, productAffineChainMap_simplex,
    SingularChains.inducedChain_simplex, crossProductZeroRight_simplex]
  apply congrArg (SingularChains.simplexChain (X × Y) 1)
  change
    (σ.prodMap τ).comp
        (productAffineSimplex
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
    crossProductCycles X Y 0 a (SingularHomology.pointCycle y) =
      SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (SingularHomology.crossInsertRight y)) 1 a := by
  apply Subtype.ext
  rw [crossProductCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact crossProductEdge_pointCycle_right X Y a.1 y

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
    crossProductHomology X Y 0
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 1 c)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) 0
          (SingularHomology.pointCycle y)) =
      _
  rw [crossProductHomology_cycleClass, crossProductCycles_pointCycle_right]
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
    formalPointCrossProduct q
        (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v)) d =
      SingularMayerVietoris.formalMap (fun w => (v 1, w)) (q + 1) d -
        SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  rw [formalBoundary_edge_simplex, map_sub, LinearMap.sub_apply,
    formalPointCrossProduct_simplex_left, formalPointCrossProduct_simplex_left]


/-- If `c` is supported on `T` and `v 0 ∈ S`, the formal point cross product of `v`
and `c` is supported on `S × T`. -/
theorem SingularHomology.formalPointCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} (q : ℕ) {c : SingularMayerVietoris.FormalChains V 1}
    {d : SingularMayerVietoris.FormalChains W (q + 1)}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported S 1)
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1)) :
    formalPointCrossProduct q c d ∈
      SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1) := by
  apply
    SingularMayerVietoris.formalLinearMap_mem_of_supported ((formalPointCrossProduct q).flip d)
      (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1)) hc
  intro v hv
  change formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d ∈ _
  rw [formalPointCrossProduct_simplex_left]
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
          formalEdgeCrossProduct q c d ∈
            SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 2) := by
  intro q
  induction q with
  | zero =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported (formalEdgeCrossProduct 0 c)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) 2) hd
    intro w hw
    rw [formalEdgeCrossProduct_zero_simplex_right]
    exact
      SingularMayerVietoris.formalMap_mem_supported (S := S) (T := S ×ˢ T) (fun v => (v, w 0))
        (fun _ hv => ⟨hv, hw 0⟩) hc
  | succ q ih =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        ((formalEdgeCrossProduct (q + 1)).flip d)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hc
    intro v hv
    change formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v) d ∈ _
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        (formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v))
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hd
    intro w hw
    rw [formalEdgeCrossProduct_simplex_succ]
    apply
      SingularMayerVietoris.formalCone_mem_supported (show (v 0, w 0) ∈ S ×ˢ T from ⟨hv 0, hw 0⟩)
    apply Submodule.sub_mem
    · exact
        formalPointCrossProduct_mem_supported (q + 1)
          (SingularMayerVietoris.formalBoundary_mem_supported 1
            (SingularMayerVietoris.formalSimplex_mem_supported hv))
          (SingularMayerVietoris.formalSimplex_mem_supported hw)
    · exact
        ih (SingularMayerVietoris.formalSimplex_mem_supported hv)
          (SingularMayerVietoris.formalBoundary_mem_supported (q + 1)
            (SingularMayerVietoris.formalSimplex_mem_supported hw))

end Mathoverflow1973
