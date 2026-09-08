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

* `PeriodTorusHigherHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
  [TopologicalSpace Y] (n : ℕ) :
  (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
  (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
  (SingularChains.singularComplex (X × Y)).homology (n + 1)`.

(The file is pre-rename: declarations carry their transitional `PeriodTorusHigherHomology`
names; the rename to the `AlgebraicTopology.SingularHomology` namespace is a separate commit
of this lane.)

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

* `PeriodTorusHigherHomology.crossProductEdge`, `.crossProductTriangle` : the chain-level
  cross products in left degrees 1 and 2.
* `PeriodTorusHigherHomology.crossProductHomology` : the homology-level cross product
  `H₁(X) →ₗ[ℤ] Hₙ(Y) →ₗ[ℤ] H_{n+1}(X × Y)`.
* `PeriodTorusHigherHomology.integerLinearMapModule`, `.integerTensorModule` :
  `@[instance_reducible]` `Module ℤ` instances on `A →ₗ[ℤ] B` and `A ⊗[ℤ] B`, used as local
  instances throughout this file: they pin the diamond between Mathlib's two instances and
  the one the product constructions elaborate against. (Lane-C open item: reproduced
  verbatim; removal is attempted in a later refactor commit and the outcome recorded.)
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

@[instance_reducible]
def PeriodTorusHigherHomology.integerLinearMapModule {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A →ₗ[ℤ] B) :=
  @LinearMap.module ℤ ℤ ℤ A B _ _ _ _ modA modB (RingHom.id ℤ) _ modB
    (@smulCommClass_self ℤ B _ modB.toMulAction)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
@[instance_reducible]
def PeriodTorusHigherHomology.integerTensorModule {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A ⊗[ℤ] B) :=
  @TensorProduct.instModule ℤ _ A B _ _ modA modB

/-! ### Bilinear plumbing -/

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerBilinearRightApply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) : A →ₗ[ℤ] C
    where
  toFun a := F a b
  map_add' a a' := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_add a a')
  map_smul' r a := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_smul r a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.integerBilinearRightApply_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : integerBilinearRightApply F b a = F a b :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerBilinearFlip {A B C : Type*} [AddCommGroup A]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.integerBilinearFlip_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : integerBilinearFlip F b a = F a b :=
  rfl

/-! ### Extending simplex-wise bilinear maps to chains -/

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.chainBilinearLift (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : SingularChains.SingularSimplex X p → SingularChains.SingularSimplex Y q → M) :
    SingularChains.Chains X p →ₗ[ℤ] SingularChains.Chains Y q →ₗ[ℤ] M :=
  SingularChains.chainLift X p fun σ => SingularChains.chainLift Y q (f σ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.chainBilinearLift_simplex_left (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : SingularChains.SingularSimplex X p → SingularChains.SingularSimplex Y q → M)
    (σ : SingularChains.SingularSimplex X p) :
    chainBilinearLift X Y p q f (SingularChains.simplexChain X p σ) =
      SingularChains.chainLift Y q (f σ) :=
  SingularChains.chainLift_simplex X p _ σ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.chainBilinearLift_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : SingularChains.SingularSimplex X p → SingularChains.SingularSimplex Y q → M)
    (σ : SingularChains.SingularSimplex X p) (τ : SingularChains.SingularSimplex Y q) :
    chainBilinearLift X Y p q f (SingularChains.simplexChain X p σ)
        (SingularChains.simplexChain Y q τ) =
      f σ τ := by rw [chainBilinearLift_simplex_left, SingularChains.chainLift_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.chainBilinearMap_ext (X Y : Type) [TopologicalSpace X]
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

def PeriodTorusHigherHomology.zeroSimplexValue {X : Type} [TopologicalSpace X]
    (σ : SingularChains.SingularSimplex X 0) : X :=
  σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))

@[simp]
theorem PeriodTorusHigherHomology.zeroSimplexValue_comp {X X' : Type} [TopologicalSpace X]
    [TopologicalSpace X'] (f : C(X, X')) (σ : SingularChains.SingularSimplex X 0) :
    zeroSimplexValue (f.comp σ) = f (zeroSimplexValue σ) :=
  rfl

def PeriodTorusHigherHomology.crossInsertRight {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (y : Y) : C(X, X × Y) :=
  ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductZeroLeft (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X 0 →ₗ[ℤ]
      SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) n :=
  chainBilinearLift X Y 0 n fun σ τ =>
    SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertLeft (zeroSimplexValue σ)).comp τ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductZeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ]
      SingularChains.Chains Y 0 →ₗ[ℤ] SingularChains.Chains (X × Y) n :=
  chainBilinearLift X Y n 0 fun σ τ =>
    SingularChains.simplexChain (X × Y) n ((PeriodTorusHigherHomology.crossInsertRight (zeroSimplexValue τ)).comp σ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 0) :
    crossProductZeroLeft X Y n (SingularChains.simplexChain X 0 σ) =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft (Y := Y) (zeroSimplexValue σ)) n := by
  apply SingularChains.chainMap_ext Y n
  intro τ
  rw [crossProductZeroLeft, chainBilinearLift_simplex, SingularChains.inducedChain_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductZeroLeft_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 0)
    (τ : SingularChains.SingularSimplex Y n) :
    crossProductZeroLeft X Y n (SingularChains.simplexChain X 0 σ)
        (SingularChains.simplexChain Y n τ) =
      SingularChains.simplexChain (X × Y) n ((SingularHomology.crossInsertLeft (zeroSimplexValue σ)).comp τ) := by
  rw [crossProductZeroLeft_simplex_left, SingularChains.inducedChain_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductZeroRight_simplex_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (c : SingularChains.Chains X n)
    (τ : SingularChains.SingularSimplex Y 0) :
    crossProductZeroRight X Y n c (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (PeriodTorusHigherHomology.crossInsertRight (zeroSimplexValue τ)) n c := by
  have h :
    integerBilinearRightApply (crossProductZeroRight X Y n) (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (PeriodTorusHigherHomology.crossInsertRight (zeroSimplexValue τ)) n := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp only [integerBilinearRightApply_apply, crossProductZeroRight, chainBilinearLift_simplex,
      SingularChains.inducedChain_simplex]
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductZeroRight_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X n)
    (τ : SingularChains.SingularSimplex Y 0) :
    crossProductZeroRight X Y n (SingularChains.simplexChain X n σ)
        (SingularChains.simplexChain Y 0 τ) =
      SingularChains.simplexChain (X × Y) n ((PeriodTorusHigherHomology.crossInsertRight (zeroSimplexValue τ)).comp σ) := by
  rw [crossProductZeroRight_simplex_right, SingularChains.inducedChain_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductZeroLeft_natural {X Y X' Y' : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerBilinearPostcompose {A B C D : Type*} [AddCommGroup A]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.integerBilinearPostcompose_apply {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) (a : A) (b : B) :
    integerBilinearPostcompose F g a b = g (F a b) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerBilinearPrecompose {A B C A' B' : Type*} [AddCommGroup A]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.integerBilinearPrecompose_apply {A B C A' B' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B']
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) (a : A') (b : B') :
    integerBilinearPrecompose F f g a b = F (f a) (g b) :=
  rfl

/-! ### The bilinear lift on formal chains -/

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.integerFormalBilinearMap_ext (V W : Type*) (p q : ℕ) {M : Type*}
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

theorem PeriodTorusHigherHomology.formalChains_bilinear_ext {V W M : Type*} {n m : ℕ}
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

def PeriodTorusHigherHomology.formalBilinearLift {V W M : Type*} {n m : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ] SingularMayerVietoris.FormalChains W m →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => SingularMayerVietoris.formalLift (f v)

@[simp]
theorem PeriodTorusHigherHomology.formalBilinearLift_simplex {V W M : Type*} {n m : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → M) (v : Fin n → V)
    (w : Fin m → W) :
    formalBilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      f v w := by simp [formalBilinearLift]

/-! ### The formal point cross product -/

def PeriodTorusHigherHomology.formalPointCrossProduct {V W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 1 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
        SingularMayerVietoris.FormalChains (V × W) (q + 1) :=
  SingularMayerVietoris.formalLift fun v =>
    SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1)

@[simp]
theorem PeriodTorusHigherHomology.formalPointCrossProduct_simplex_left {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d =
      SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) d

@[simp]
theorem PeriodTorusHigherHomology.formalPointCrossProduct_simplex {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (w : Fin (q + 1) → W) :
    formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (fun i => (v 0, w i)) := by
  rw [formalPointCrossProduct_simplex_left, SingularMayerVietoris.formalMap_simplex]
  rfl

@[simp]
theorem PeriodTorusHigherHomology.formalPointCrossProduct_zero_simplex_right {V W : Type*}
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

theorem PeriodTorusHigherHomology.formalBoundary_pointCrossProduct {V W : Type*} (q : ℕ)
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

theorem PeriodTorusHigherHomology.formalMap_pointCrossProduct {V W V' W' : Type*} (f : V → V')
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

def PeriodTorusHigherHomology.formalEdgeCrossProduct {V W : Type*} :
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

@[simp]
theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (w : Fin 1 → W) :
    formalEdgeCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 2 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

@[simp]
theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
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

theorem PeriodTorusHigherHomology.formalBoundary_edgeCrossProduct_zero {V W : Type*}
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

theorem PeriodTorusHigherHomology.formalBoundary_edgeCrossProduct {V W : Type*} :
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

theorem PeriodTorusHigherHomology.formalMap_edgeCrossProduct {V W V' W' : Type*} (f : V → V')
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

@[simp]
theorem PeriodTorusHigherHomology.affineSimplex_constant {n p : ℕ} (a : SingularChains.Simplex p) :
    SingularMayerVietoris.affineSimplex (fun _ : Fin (n + 1) => a) =
      ContinuousMap.const (SingularChains.Simplex n) a := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (∑ i, t i • (a : Fin (p + 1) → ℝ)) = (a : Fin (p + 1) → ℝ)
  rw [← Finset.sum_smul, stdSimplex.sum_eq_one t, one_smul]

def PeriodTorusHigherHomology.productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    C(SingularChains.Simplex n, SingularChains.Simplex p × SingularChains.Simplex q) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (SingularMayerVietoris.affineSimplex (fun i => (v i).2))

@[simp]
theorem PeriodTorusHigherHomology.productAffineSimplex_vertex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) (i : Fin (n + 1)) :
    productAffineSimplex v (SingularMayerVietoris.stdVertices n i) = v i := by
  apply Prod.ext <;> simp [productAffineSimplex, SingularMayerVietoris.stdVertices]

theorem PeriodTorusHigherHomology.productAffineSimplex_face {n p q : ℕ}
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

theorem PeriodTorusHigherHomology.prodMap_productAffineSimplex {m p q r s : ℕ}
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

def PeriodTorusHigherHomology.productAffineChainMap (p q n : ℕ) :
    SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 1) →ₗ[ℤ]
      SingularChains.Chains (SingularChains.Simplex p × SingularChains.Simplex q) n :=
  SingularMayerVietoris.formalLift fun v =>
    SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
      (productAffineSimplex v)

@[simp]
theorem PeriodTorusHigherHomology.productAffineChainMap_simplex (p q n : ℕ)
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    productAffineChainMap p q n (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
        (productAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

theorem PeriodTorusHigherHomology.productAffineChainMap_boundary (p q n : ℕ)
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

theorem PeriodTorusHigherHomology.inducedChain_productAffineChainMap {m p q r s : ℕ}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductEdge (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) :=
  chainBilinearLift X Y 1 n fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) (n + 1)
      (productAffineChainMap 1 n (n + 1)
        (formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductEdge_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X 1)
    (τ : SingularChains.SingularSimplex Y n) :
    crossProductEdge X Y n (SingularChains.simplexChain X 1 σ) (SingularChains.simplexChain Y n τ) =
      SingularChains.inducedChain (σ.prodMap τ) (n + 1)
        (productAffineChainMap 1 n (n + 1)
          (formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainBilinearLift_simplex X Y 1 n _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_natural {X Y X' Y' : Type} [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.affineSimplex_stdVertices_image {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    SingularMayerVietoris.affineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact SingularMayerVietoris.affineSimplex_vertex v i

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.productAffineSimplex_point_left {n p q : ℕ}
    (a : SingularChains.Simplex p) (v : Fin (n + 1) → SingularChains.Simplex q) :
    productAffineSimplex (fun i => (a, v i)) =
      (SingularHomology.crossInsertLeft a).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.productAffineSimplex_point_right {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (b : SingularChains.Simplex q) :
    productAffineSimplex (fun i => (v i, b)) =
      (PeriodTorusHigherHomology.crossInsertRight b).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductZeroLeft_affineChainMap (p q n : ℕ)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_affineChainMap (p q n : ℕ)
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

def PeriodTorusHigherHomology.formalTriangleCrossProduct {V W : Type*} :
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

@[simp]
theorem PeriodTorusHigherHomology.formalTriangleCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (w : Fin 1 → W) :
    formalTriangleCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 3 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

@[simp]
theorem PeriodTorusHigherHomology.formalTriangleCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
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

theorem PeriodTorusHigherHomology.formalBoundary_triangleCrossProduct_zero {V W : Type*}
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

theorem PeriodTorusHigherHomology.formalBoundary_triangleCrossProduct {V W : Type*} :
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

theorem PeriodTorusHigherHomology.formalMap_triangleCrossProduct {V W V' W' : Type*} (f : V → V')
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductTriangle (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 2) :=
  chainBilinearLift X Y 2 n fun σ τ =>
    SingularChains.inducedChain (σ.prodMap τ) (n + 2)
      (productAffineChainMap 2 n (n + 2)
        (formalTriangleCrossProduct n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductTriangle_simplex (X Y : Type) [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_natural {X Y X' Y' : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_affineChainMap (p q n : ℕ)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_zero_affine (p q : ℕ)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_affine (p q n : ℕ)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_zero {X Y : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_boundary {X Y : Type} [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_of_right_cycle {X Y : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_boundary_zero_affine (p q : ℕ)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_boundary_affine (p q n : ℕ)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_boundary_zero {X Y : Type} [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_boundary {X Y : Type} [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_cycle {X Y : Type} [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_boundary_of_left_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1)
    (ha : ((SingularChains.singularComplex X).d 1 0).hom a = 0)
    (b : SingularChains.Chains Y (n + 1)) :
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductEdge X Y (n + 1) a b) =
      -crossProductEdge X Y n a (((SingularChains.singularComplex Y).d (n + 1) n).hom b) := by
  simp only [crossProductEdge_boundary, ha, map_zero, LinearMap.zero_apply, zero_sub]

/-! ### Descent to homology -/

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
abbrev PeriodTorusHigherHomology.homologyBoundaries (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) : Submodule ℤ (SingularMayerVietoris.ModuleHomology.Cycle K n) :=
  SingularChains.ChainHomology.ShortBoundaries (K.sc n)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
theorem PeriodTorusHigherHomology.homologyLinearMap_ext (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
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
theorem PeriodTorusHigherHomology.homologyBoundaries_le_ker (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
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
def PeriodTorusHigherHomology.homologyDesc (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    K.homology n →ₗ[ℤ] M :=
  ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
@[simp]
theorem PeriodTorusHigherHomology.homologyDesc_cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    homologyDesc K n f hf (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = f c := by
  have h :=
    congrArg (fun q => q.hom (Submodule.Quotient.mk c)) (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)) h

/-! ### The cross product on cycles -/

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductCycles (X Y : Type) [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    (crossProductCycles X Y n a b).1 = crossProductEdge X Y n a.1 b.1 :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductCycleClasses (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  integerBilinearPostcompose (crossProductCycles X Y n)
    (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
      (n + 1))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCycleClasses_boundary_right {X Y : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductHomologyFixed {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1) :
    (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
      (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (SingularChains.singularComplex Y) n (crossProductCycleClasses X Y n a)
    (crossProductCycleClasses_boundary_right n a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductHomologyFixed_cycleClass {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    crossProductHomologyFixed n a
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (crossProductCycles X Y n a b) :=
  homologyDesc_cycleClass _ _ _ _ b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductHomologyCycles (X Y : Type) [TopologicalSpace X]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCycleClasses_boundary_left {X Y : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomologyCycles_boundary_left {X Y : Type}
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
      (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (SingularChains.singularComplex X) 1 (crossProductHomologyCycles X Y n)
    (crossProductHomologyCycles_boundary_left n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductHomology_cycleClass (X Y : Type)
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_zero_eq_zeroRight (X Y : Type)
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
      (PeriodTorusHigherHomology.crossInsertRight (zeroSimplexValue τ)).comp σ
  rw [productAffineSimplex_point_right, SingularMayerVietoris.affineSimplex_stdVertices,
    ContinuousMap.comp_id]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_zero_simplex_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1)
    (τ : SingularChains.SingularSimplex Y 0) :
    crossProductEdge X Y 0 a (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (PeriodTorusHigherHomology.crossInsertRight (zeroSimplexValue τ)) 1 a := by
  rw [crossProductEdge_zero_eq_zeroRight, crossProductZeroRight_simplex_right]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductEdge_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1) (y : Y) :
    crossProductEdge X Y 0 a (SingularHomology.pointCycle y).1 =
      SingularChains.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 1 a := by
  rw [SingularHomology.pointCycle_val, crossProductEdge_zero_simplex_right]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductCycles_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1) (y : Y) :
    crossProductCycles X Y 0 a (SingularHomology.pointCycle y) =
      SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (PeriodTorusHigherHomology.crossInsertRight y)) 1 a := by
  apply Subtype.ext
  rw [crossProductCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact crossProductEdge_pointCycle_right X Y a.1 y

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductHomology_pointClass_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (y : Y) :
    crossProductHomology X Y 0 a (SingularHomology.pointClass y) =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.crossInsertRight y) 1 a := by
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
        (SingularChains.singularChainMap (PeriodTorusHigherHomology.crossInsertRight y)) 1 c).symm

end Mathoverflow1973
