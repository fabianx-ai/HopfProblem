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

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Bilinear and trilinear maps over `ℤ` and their lifts to chains

Plumbing for the singular cross product.  Currying and composition of `ℤ`-bilinear maps
(`SingularHomology.integerBilinearRightApply`, `.integerBilinearFlip`,
`.integerBilinearPostcompose`, `.integerBilinearPrecompose`) and of `ℤ`-trilinear maps
(`PeriodTorusHigherHomology.integerTrilinearPostcompose`, `.integerTrilinearPrecompose`,
`.integerTrilinearLeftAssociated`, `.integerTrilinearRightAssociated`); the extension of a
simplex-wise assignment to a bilinear or trilinear map on the free abelian groups of singular
chains (`SingularHomology.chainBilinearLift`, `PeriodTorusHigherHomology.chainTrilinearLift`,
unique by `SingularHomology.chainBilinearMap_ext`, `PeriodTorusHigherHomology.chainTrilinearMap_ext`)
and on formal chains (`SingularHomology.formalBilinearLift`,
`PeriodTorusHigherHomology.formalTrilinearLift`, with the extensionality statements
`SingularHomology.formalChains_bilinear_ext`, `.integerFormalBilinearMap_ext`,
`PeriodTorusHigherHomology.formalChains_trilinear_ext`).

This is the "extend bilinearly from generators" step of Hatcher's construction of the cross
product on chains (Hatcher, *Algebraic Topology*, §3.B).  Mathlib has `LinearMap.flip`,
`LinearMap.compl₂` and `LinearMap.lcomp` for any semiring; the `ℤ`-versions here are the ones
the product constructions were elaborated against.

## The two module instances

`SingularHomology.integerLinearMapModule` and `.integerTensorModule` are `@[instance_reducible]`
`Module ℤ` structures on `A →ₗ[ℤ] B` and `A ⊗[ℤ] B`.  They pin the diamond between Mathlib's
instances and the one the cross-product constructions elaborate against, and are used as local
instances (`attribute [local instance] … in`) on almost every declaration of the construction.
-/


@[expose] public noncomputable section


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


/-! ### Trilinear maps -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Postcompose a ℤ-trilinear map with a linear map on its output. -/
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
/-- The postcomposed trilinear map evaluates as `g (F a b c)`. -/
@[simp]
theorem PeriodTorusHigherHomology.integerTrilinearPostcompose_apply {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) (a : A) (b : B) (c : C) :
    PeriodTorusHigherHomology.integerTrilinearPostcompose F g a b c = g (F a b c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Precompose a ℤ-trilinear map with linear maps in each of its three arguments. -/
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
/-- The precomposed trilinear map evaluates argumentwise along the three precomposition maps. -/
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
/-- Reassociate a bilinear-then-bilinear pipeline into a trilinear map, left-associated. -/
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
/-- Reassociate a bilinear-then-bilinear pipeline into a trilinear map, right-associated. -/
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

/-! ### Extending simplex-wise trilinear maps to chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- A pointwise-defined map on triples of singular simplices lifts to a ℤ-trilinear map on the free chain groups. -/
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
/-- `chainTrilinearLift` evaluates on basis simplex chains as `f σ τ υ`. -/
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

/-! ### The trilinear lift on formal chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Two trilinear maps on singular chain groups agreeing on all triples of basis simplices are equal. -/
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
/-- Two trilinear maps on formal chains agreeing on formal simplices are equal. -/
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
/-- A pointwise-defined map on triples of formal simplices lifts to a ℤ-trilinear map on formal chain groups. -/
def PeriodTorusHigherHomology.formalTrilinearLift {V W Z M : Type*} {n m l : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => SingularHomology.formalBilinearLift (f v)
/-- `formalTrilinearLift` evaluates on formal simplices as `f v w z`. -/
@[simp]
theorem PeriodTorusHigherHomology.formalTrilinearLift_simplex {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M)
    (v : Fin n → V) (w : Fin m → W) (z : Fin l → Z) :
    PeriodTorusHigherHomology.formalTrilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      f v w z := by simp [PeriodTorusHigherHomology.formalTrilinearLift]
