/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Algebra.Homology.MayerVietorisShortExact
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris

/-!
# The homology of a finite coproduct of spaces

`H_n(⊔_{i∈ι} Xᵢ) ≅ ⊕_{i∈ι} H_n(Xᵢ)` for finite `ι` (Hatcher, Proposition 2.6 in coproduct
form), realized through the finite biproduct of the chain complexes:

* `Coproduct.sigmaHomologyEquiv` — the homology iso, with `_symm_single` computing it on a
  single summand's class;
* the local instance `Coproduct.singularChainsFiniteBiproducts` — finite biproducts of
  `ModuleCat ℤ`-valued chain complexes exist (attached to every declaration of the block,
  as in the source).

Consumed by the local-contributions and recognition files.

## Outline of the proof

1. *Finite biproducts of chain complexes.*  `singularChainsFiniteBiproducts` supplies the
   biproduct decomposition of the chain complex of a finite disjoint union.
2. *The σ-chain dictionary.*  The sigma-type presentation of simplices identifies
   `C(⊔ Xᵢ)` with the biproduct (`sigmaHomologyEquiv` and its `_symm_apply`/
   `_single` computations).

## Main definitions and results

* `Coproduct.sigmaHomologyEquiv` : `H_n(⊔ Xᵢ) ≅ ⊕ H_n(Xᵢ)`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Proposition 2.6

## Tags

coproduct, finite biproduct, homology
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Singular chains of a disjoint union -/

/-- Chain complexes of `ℤ`-modules have finite biproducts. -/
theorem Coproduct.singularChainsFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The inclusion of a summand into the sigma type. -/
def Coproduct.sigmaInclusion {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (i : ι) : C(X i, Σ i, X i) :=
  ⟨Sigma.mk i, continuous_sigmaMk⟩

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- Every simplex of the sigma type factors through a summand. -/
theorem Coproduct.singularSimplex_sigma_split {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) (σ : SingularChains.SingularSimplex (Σ i, X i) n) :
    ∃ (i : ι) (τ : SingularChains.SingularSimplex (X i) n), σ = (sigmaInclusion X i).comp τ := by
  obtain ⟨i, g, hg, heq⟩ := σ.continuous.exists_lift_sigma
  exact ⟨i, ⟨g, hg⟩, ContinuousMap.ext (congrFun heq)⟩

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The map from summand simplices to sigma simplices. -/
def Coproduct.sigmaSimplexMap {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    (Σ i, SingularChains.SingularSimplex (X i) n) → SingularChains.SingularSimplex (Σ i, X i) n :=
  fun σ => (sigmaInclusion X σ.1).comp σ.2

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The sigma simplex map is injective. -/
theorem Coproduct.sigmaSimplexMap_injective {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) : Function.Injective (sigmaSimplexMap X n) := by
  classical
  let z : stdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  rintro ⟨i, σ⟩ ⟨j, τ⟩ h
  have hij : i = j := congrArg (fun f => (f z).1) h
  subst j
  congr 1
  exact ContinuousMap.ext fun t => sigma_mk_injective (congrArg (fun f => f t) h)

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The sigma simplex map is surjective. -/
theorem Coproduct.sigmaSimplexMap_surjective {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) : Function.Surjective (sigmaSimplexMap X n) := by
  intro σ
  obtain ⟨i, τ, hτ⟩ := singularSimplex_sigma_split X n σ
  exact ⟨⟨i, τ⟩, hτ.symm⟩

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- Sigma simplices are equivalent to the sum of summand simplices. -/
def Coproduct.sigmaSimplexEquiv {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    (Σ i, SingularChains.SingularSimplex (X i) n) ≃ SingularChains.SingularSimplex (Σ i, X i) n :=
  Equiv.ofBijective (sigmaSimplexMap X n)
    ⟨sigmaSimplexMap_injective X n, sigmaSimplexMap_surjective X n⟩

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The equivalence inverse on an included simplex. -/
@[simp]
theorem Coproduct.sigmaSimplexEquiv_symm_inclusion {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) (i : ι) (σ : SingularChains.SingularSimplex (X i) n) :
    (sigmaSimplexEquiv X n).symm ((sigmaInclusion X i).comp σ) = ⟨i, σ⟩ :=
  (sigmaSimplexEquiv X n).symm_apply_apply ⟨i, σ⟩

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- Chain maps out of the sigma chains are determined on summands. -/
theorem Coproduct.sigmaChains_hom_ext {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) {M : ModuleCat ℤ}
    (f g : SingularChains.Chains (Σ i, X i) n ⟶ M)
    (h :
      ∀ i,
        (SingularChains.singularChainMap (sigmaInclusion X i)).f n ≫ f =
          (SingularChains.singularChainMap (sigmaInclusion X i)).f n ≫ g) :
    f = g := by
  apply ModuleCat.hom_ext
  apply SingularChains.chainMap_ext (Σ i, X i) n
  intro σ
  obtain ⟨i, τ, rfl⟩ := singularSimplex_sigma_split X n σ
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, SingularChains.inducedChain_simplex] using
    congrArg (fun k => k.hom (SingularChains.simplexChain (X i) n τ)) (h i)

/-! ### The biproduct of singular complexes -/

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The chain map from the biproduct of summand complexes to the complex of the union. -/
def Coproduct.sigmaChainComplexMap {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    (⨁ fun i => SingularChains.singularComplex (X i)) ⟶ SingularChains.singularComplex (Σ i, X i) :=
  CategoryTheory.Limits.biproduct.desc fun i =>
    SingularChains.singularChainMap (sigmaInclusion X i)

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The biproduct map on a summand is the inclusion's chain map. -/
@[simp]
theorem Coproduct.sigmaChainComplexMap_inclusion {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] (i : ι) :
    CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i ≫
        sigmaChainComplexMap X =
      SingularChains.singularChainMap (sigmaInclusion X i) :=
  CategoryTheory.Limits.biproduct.ι_desc _ i

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The degree-`n` inverse chain map to the biproduct. -/
def Coproduct.sigmaChainInverseDegree {ι : Type}
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (n : ℕ) :
    SingularChains.Chains (Σ i, X i) n →ₗ[ℤ]
      (⨁ fun i => SingularChains.singularComplex (X i)).X n :=
  SingularChains.chainLift (Σ i, X i) n fun σ =>
    let τ := (sigmaSimplexEquiv X n).symm σ
    ((CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) τ.1).f
          n).hom
      (SingularChains.simplexChain (X τ.1) n τ.2)

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The inverse degree map on an included simplex. -/
theorem Coproduct.sigmaChainInverseDegree_inclusion
    {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (n : ℕ) (i : ι)
    (σ : SingularChains.SingularSimplex (X i) n) :
    sigmaChainInverseDegree X n
        (SingularChains.simplexChain (Σ i, X i) n ((sigmaInclusion X i).comp σ)) =
      ((CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i).f
            n).hom
        (SingularChains.simplexChain (X i) n σ) := by
  simpa only [sigmaChainInverseDegree, SingularChains.chainLift_simplex] using
    congrArg
      (fun τ : Σ i, SingularChains.SingularSimplex (X i) n =>
        ((CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) τ.1).f
              n).hom
          (SingularChains.simplexChain (X τ.1) n τ.2))
      (sigmaSimplexEquiv_symm_inclusion X n i σ)

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The inverse composed with a summand inclusion. -/
theorem Coproduct.sigmaChainInverseDegree_comp_inclusion
    {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (n : ℕ) (i : ι) :
    (SingularChains.singularChainMap (sigmaInclusion X i)).f n ≫
        ModuleCat.ofHom (sigmaChainInverseDegree X n) =
      (CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i).f n := by
  apply ModuleCat.hom_ext
  apply SingularChains.chainMap_ext (X i) n
  intro σ
  change
    sigmaChainInverseDegree X n
        (SingularChains.inducedChain (sigmaInclusion X i) n
          (SingularChains.simplexChain (X i) n σ)) =
      _
  rw [SingularChains.inducedChain_simplex, sigmaChainInverseDegree_inclusion]

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The inverse chain map from sigma chains to the biproduct. -/
def Coproduct.sigmaChainComplexInverse {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    SingularChains.singularComplex (Σ i, X i) ⟶ (⨁ fun i => SingularChains.singularComplex (X i))
    where
  f n := ModuleCat.ofHom (sigmaChainInverseDegree X n)
  comm' n m
    _ := by
    apply sigmaChains_hom_ext X n
    intro i
    calc
      _ =
          ((SingularChains.singularChainMap (sigmaInclusion X i)).f n ≫
              ModuleCat.ofHom (sigmaChainInverseDegree X n)) ≫
            (⨁ fun i => SingularChains.singularComplex (X i)).d n m :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          (CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i).f
              n ≫
            (⨁ fun i => SingularChains.singularComplex (X i)).d n m :=
        (congrArg
          (fun f :
              SingularChains.Chains (X i) n ⟶
                (⨁ fun i => SingularChains.singularComplex (X i)).X n =>
            f ≫ (⨁ fun i => SingularChains.singularComplex (X i)).d n m)
          (sigmaChainInverseDegree_comp_inclusion X n i))
      _ =
          (SingularChains.singularComplex (X i)).d n m ≫
            (CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i).f
              m :=
        ((CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i).comm
          n m)
      _ =
          (SingularChains.singularComplex (X i)).d n m ≫
            ((SingularChains.singularChainMap (sigmaInclusion X i)).f m ≫
              ModuleCat.ofHom (sigmaChainInverseDegree X m)) :=
        (congrArg
            (fun f :
                SingularChains.Chains (X i) m ⟶
                  (⨁ fun i => SingularChains.singularComplex (X i)).X m =>
              (SingularChains.singularComplex (X i)).d n m ≫ f)
            (sigmaChainInverseDegree_comp_inclusion X m i)).symm
      _ =
          ((SingularChains.singularComplex (X i)).d n m ≫
              (SingularChains.singularChainMap (sigmaInclusion X i)).f m) ≫
            ModuleCat.ofHom (sigmaChainInverseDegree X m) :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          ((SingularChains.singularChainMap (sigmaInclusion X i)).f n ≫
              (SingularChains.singularComplex (Σ i, X i)).d n m) ≫
            ModuleCat.ofHom (sigmaChainInverseDegree X m) :=
        (congrArg
          (fun f : SingularChains.Chains (X i) n ⟶ SingularChains.Chains (Σ i, X i) m =>
            f ≫ ModuleCat.ofHom (sigmaChainInverseDegree X m))
          ((SingularChains.singularChainMap (sigmaInclusion X i)).comm n m).symm)
      _ = _ := CategoryTheory.Category.assoc _ _ _

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The inverse composed with a summand chain map. -/
@[simp]
theorem Coproduct.sigmaChainComplexInverse_inclusion {ι : Type}
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (i : ι) :
    SingularChains.singularChainMap (sigmaInclusion X i) ≫ sigmaChainComplexInverse X =
      CategoryTheory.Limits.biproduct.ι (fun i => SingularChains.singularComplex (X i)) i := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sigmaChainInverseDegree_comp_inclusion X n i

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The biproduct map followed by the inverse is the identity. -/
theorem Coproduct.sigmaChainComplexMap_comp_inverse {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    sigmaChainComplexMap X ≫ sigmaChainComplexInverse X =
      𝟙 (⨁ fun i => SingularChains.singularComplex (X i)) := by
  apply CategoryTheory.Limits.biproduct.hom_ext'
  intro i
  rw [← CategoryTheory.Category.assoc, sigmaChainComplexMap_inclusion,
    sigmaChainComplexInverse_inclusion, CategoryTheory.Category.comp_id]

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The inverse followed by the biproduct map is the identity. -/
theorem Coproduct.sigmaChainComplexInverse_comp_map {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    sigmaChainComplexInverse X ≫ sigmaChainComplexMap X =
      𝟙 (SingularChains.singularComplex (Σ i, X i)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply sigmaChains_hom_ext X n
  intro i
  have h :
    SingularChains.singularChainMap (sigmaInclusion X i) ≫
        (sigmaChainComplexInverse X ≫ sigmaChainComplexMap X) =
      SingularChains.singularChainMap (sigmaInclusion X i) := by
    rw [← CategoryTheory.Category.assoc, sigmaChainComplexInverse_inclusion,
      sigmaChainComplexMap_inclusion]
  exact (congrArg (fun f => f.f n) h).trans (CategoryTheory.Category.comp_id _).symm

attribute [local instance] Coproduct.singularChainsFiniteBiproducts in
/-- The singular chains of a finite sigma type are the biproduct of the summand complexes. -/
def Coproduct.sigmaChainComplexIso {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    (⨁ fun i => SingularChains.singularComplex (X i)) ≅ SingularChains.singularComplex (Σ i, X i)
    where
  hom := sigmaChainComplexMap X
  inv := sigmaChainComplexInverse X
  hom_inv_id := sigmaChainComplexMap_comp_inverse X
  inv_hom_id := sigmaChainComplexInverse_comp_map X

/-- Homology chain complexes admit finite biproducts. -/
theorem Coproduct.homologyFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] Coproduct.homologyFiniteBiproducts in
/-- The projection of an inclusion is the identity on homology. -/
theorem Coproduct.homology_π_ι_self {ι : Type} [Finite ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (i : ι) (a : (K i).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom a) =
      a := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biproduct.ι K i)
      (CategoryTheory.Limits.biproduct.π K i) n
  rw [CategoryTheory.Limits.biproduct.ι_π_self, HomologicalComplex.homologyMap_id] at h
  exact (congrArg (fun f => f.hom a) h).symm

attribute [local instance] Coproduct.homologyFiniteBiproducts in
/-- Distinct biproduct homology components are orthogonal. -/
theorem Coproduct.homology_π_ι_ne {ι : Type} [Finite ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) {i j : ι} (hij : i ≠ j)
    (a : (K i).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K j) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom a) =
      0 := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biproduct.ι K i)
      (CategoryTheory.Limits.biproduct.π K j) n
  rw [CategoryTheory.Limits.biproduct.ι_π_ne K hij, HomologicalComplex.homologyMap_zero] at h
  exact (congrArg (fun f => f.hom a) h).symm

/-! ### Homology of biproducts -/

attribute [local instance] Coproduct.homologyFiniteBiproducts in
/-- Every biproduct homology class decomposes. -/
theorem Coproduct.homology_biproduct_total {ι : Type}
    [Fintype ι] (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : (⨁ K).homology n) :
    ∑ i,
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom a) =
      a := by
  have h :
    HomologicalComplex.homologyMap
        (∑ i, CategoryTheory.Limits.biproduct.π K i ≫ CategoryTheory.Limits.biproduct.ι K i) n =
      𝟙 ((⨁ K).homology n) := by
    rw [CategoryTheory.Limits.biproduct.total, HomologicalComplex.homologyMap_id]
  change
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
        (∑ i, CategoryTheory.Limits.biproduct.π K i ≫ CategoryTheory.Limits.biproduct.ι K i) =
      _ at h
  rw [CategoryTheory.Functor.map_sum] at h
  change
    (∑ i,
        HomologicalComplex.homologyMap
          (CategoryTheory.Limits.biproduct.π K i ≫ CategoryTheory.Limits.biproduct.ι K i) n) =
      _ at h
  simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using
    congrArg (fun f => f.hom a) h

attribute [local instance] Coproduct.homologyFiniteBiproducts in
/-- Homology of a biproduct is the product of homologies. -/
def Coproduct.homologyBiproductEquiv {ι : Type} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (⨁ K).homology n ≃ₗ[ℤ] (∀ i, (K i).homology n) := by
  classical
    exact
    ({    toFun a
            i := (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom a
          invFun
            a :=
            ∑ i,
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom (a i)
          left_inv := homology_biproduct_total K n
          right_inv
            a := by
            funext i
            change
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom
                  (∑ j,
                    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K j) n).hom
                      (a j)) =
                a i
            rw [map_sum, Finset.sum_eq_single i]
            · exact homology_π_ι_self K n i (a i)
            · intro j _ hji
              exact homology_π_ι_ne K n hji (a j)
            · simp
          map_add' a
            b := by
            funext i
            exact
              map_add
                (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom a
                b } :
        (⨁ K).homology n ≃+ (∀ i, (K i).homology n)).toIntLinearEquiv

attribute [local instance] Coproduct.homologyFiniteBiproducts in
/-- The inverse equivalence sums the inclusion images. -/
theorem Coproduct.homologyBiproductEquiv_symm_apply {ι : Type} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : ∀ i, (K i).homology n) :
    (homologyBiproductEquiv K n).symm a =
      ∑ i, (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom (a i) :=
  rfl

attribute [local instance] Coproduct.homologyFiniteBiproducts in
/-- The equivalence descends a family of chain maps. -/
theorem Coproduct.homologyBiproductEquiv_desc {ι : Type} [Fintype ι]
    {K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ} (n : ℕ) {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, K i ⟶ L) (a : ∀ i, (K i).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.desc f) n).hom
        ((homologyBiproductEquiv K n).symm a) =
      ∑ i, (HomologicalComplex.homologyMap (f i) n).hom (a i) := by
  rw [homologyBiproductEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biproduct.ι K i)
      (CategoryTheory.Limits.biproduct.desc f) n
  rw [CategoryTheory.Limits.biproduct.ι_desc] at h
  exact (congrArg (fun k => k.hom (a i)) h).symm

/-- Singular homology of a finite disjoint union is the product of the summand homologies. -/
def Coproduct.sigmaHomologyEquiv {ι : Type} [Fintype ι] (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Σ i, X i) n ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (X i) n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (sigmaChainComplexIso X)).symm.toLinearEquiv.trans
    (homologyBiproductEquiv (fun i => SingularChains.singularComplex (X i)) n)

/-- The inverse equivalence maps a tuple of classes to the sum of their included classes. -/
theorem Coproduct.sigmaHomologyEquiv_symm_apply {ι : Type} [Fintype ι]
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] (n : ℕ)
    (a : ∀ i, SingularMayerVietoris.SingularHomology (X i) n) :
    (sigmaHomologyEquiv X n).symm a =
      ∑ i, SingularMayerVietoris.singularHomologyMap (sigmaInclusion X i) n (a i) := by
  change
    (HomologicalComplex.homologyMap (sigmaChainComplexMap X) n).hom
        ((homologyBiproductEquiv (fun i => SingularChains.singularComplex (X i)) n).symm a) =
      _
  exact
    homologyBiproductEquiv_desc n (fun i => SingularChains.singularChainMap (sigmaInclusion X i)) a

/-- The homology equivalence inverse on a single component. -/
@[simp]
theorem Coproduct.sigmaHomologyEquiv_symm_single {ι : Type} [Fintype ι]
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] [DecidableEq ι] (n : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (X i) n) :
    (sigmaHomologyEquiv X n).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (sigmaInclusion X i) n a := by
  rw [sigmaHomologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp
