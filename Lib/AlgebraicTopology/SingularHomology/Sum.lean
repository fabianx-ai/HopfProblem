/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Suspension

/-!
# Homology of disjoint unions and finite coproducts

The singular chains of a disjoint union are the direct sum of the singular chains, and
homology commutes with finite coproducts (Hatcher, Proposition 2.6):

* `SingularHomology.sumHomologyEquiv` — the homology of a finite disjoint union is
  the direct sum of the homologies, natural in the inclusions
  (`sumHomologyEquiv_inl`, `sumHomologyEquiv_inr`, `sumHomologyEquiv_symm_apply`).

The engine is a chain-complex iso: `sumChainComplexIso` lifts the element-level
simplex identifications (`singularSimplex_sum_split`, `sumSimplexEquiv`) to a chain
isomorphism whose components are inverse (`sumChainInverseDegree_*`) — so the statement is
an equality of homology functors on coproducts, not a mere abstract iso.

## Outline of the proof

1. *Simplices over a disjoint union split.*  Each simplex of `⊔ Xᵢ` lands in one summand;
   `singularSimplex_sum_split` and `sumSimplexMap`/`sumSimplexEquiv` trade simplices for
   pairs (component, simplex).
2. *The chain iso.*  `sumChainComplexMap` and `sumChainInverseDegree` are inverse
   (`sumChainComplexMap_comp_inverse_*`, `sumChainInverse_comp_map_*`, componentwise
   isomorphism `sumChainComplexMap_component_isIso_*`), giving `sumChainComplexIso`.
3. *Homology.*  `sumHomologyEquiv` with its computation lemmas
   (`sumHomologyEquiv_inl`, `_inr`, `sumElim_homology_inl/_inr`,
   `sumHomologyEquiv_sumElim_symm`).

## Main definitions and results

* `SingularHomology.sumChainComplexIso` : `C(⊔ Xᵢ) ≅ ⊕ C(Xᵢ)` as chain complexes.
* `SingularHomology.sumHomologyEquiv` : `H_n(⊔ Xᵢ) ≅ ⊕ H_n(Xᵢ)` (Hatcher Prop 2.6).

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Proposition 2.6

## Tags

disjoint union, coproduct, homology
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def SingularHomology.sumInlMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    C(X, X ⊕ Y) :=
  ⟨Sum.inl, continuous_inl⟩

def SingularHomology.sumInrMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    C(Y, X ⊕ Y) :=
  ⟨Sum.inr, continuous_inr⟩

def SingularHomology.sumElimMap {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Z)) (g : C(Y, Z)) : C(X ⊕ Y, Z) :=
  ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩

theorem SingularHomology.singularSimplex_sum_split (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex (X ⊕ Y) n) :
    (∃ τ : SingularChains.SingularSimplex X n, σ = (sumInlMap X Y).comp τ) ∨
      (∃ τ : SingularChains.SingularSimplex Y n, σ = (sumInrMap X Y).comp τ) := by
  rcases Sum.isConnected_iff.mp (isConnected_range σ.continuous) with ⟨s, _, hs⟩ | ⟨s, _, hs⟩
  · have hr : Set.range σ ⊆ Set.range (Sum.inl : X → X ⊕ Y) :=
      hs.trans_subset (Set.image_subset_range _ _)
    obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.mp hr
    have hc : Continuous g := Topology.IsEmbedding.inl.continuous_iff.mpr (hg ▸ σ.continuous)
    exact Or.inl ⟨⟨g, hc⟩, ContinuousMap.ext (congrFun hg)⟩
  · have hr : Set.range σ ⊆ Set.range (Sum.inr : Y → X ⊕ Y) :=
      hs.trans_subset (Set.image_subset_range _ _)
    obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.mp hr
    have hc : Continuous g := Topology.IsEmbedding.inr.continuous_iff.mpr (hg ▸ σ.continuous)
    exact Or.inr ⟨⟨g, hc⟩, ContinuousMap.ext (congrFun hg)⟩

def SingularHomology.sumSimplexMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) :
    SingularChains.SingularSimplex X n ⊕ SingularChains.SingularSimplex Y n →
      SingularChains.SingularSimplex (X ⊕ Y) n :=
  Sum.elim ((sumInlMap X Y).comp) ((sumInrMap X Y).comp)

theorem SingularHomology.sumSimplexMap_injective (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) : Function.Injective (sumSimplexMap X Y n) := by
  classical
  let z : stdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  intro σ τ h
  cases σ with
  | inl σ =>
    cases τ with
    | inl τ =>
      congr 1
      exact ContinuousMap.ext fun t => Sum.inl.inj (congrArg (fun f => f t) h)
    | inr τ => exact False.elim (Sum.inl_ne_inr (congrArg (fun f => f z) h))
  | inr σ =>
    cases τ with
    | inl τ => exact False.elim (Sum.inr_ne_inl (congrArg (fun f => f z) h))
    | inr τ =>
      congr 1
      exact ContinuousMap.ext fun t => Sum.inr.inj (congrArg (fun f => f t) h)

theorem SingularHomology.sumSimplexMap_surjective (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) : Function.Surjective (sumSimplexMap X Y n) := by
  intro σ
  rcases singularSimplex_sum_split X Y n σ with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
  · exact ⟨Sum.inl τ, hτ.symm⟩
  · exact ⟨Sum.inr τ, hτ.symm⟩

def SingularHomology.sumSimplexEquiv (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularChains.SingularSimplex X n ⊕ SingularChains.SingularSimplex Y n ≃
      SingularChains.SingularSimplex (X ⊕ Y) n :=
  Equiv.ofBijective (sumSimplexMap X Y n)
    ⟨sumSimplexMap_injective X Y n, sumSimplexMap_surjective X Y n⟩

@[simp]
theorem SingularHomology.sumSimplexEquiv_symm_inl (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X n) :
    (sumSimplexEquiv X Y n).symm ((sumInlMap X Y).comp σ) = Sum.inl σ :=
  (sumSimplexEquiv X Y n).symm_apply_apply (Sum.inl σ)

@[simp]
theorem SingularHomology.sumSimplexEquiv_symm_inr (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex Y n) :
    (sumSimplexEquiv X Y n).symm ((sumInrMap X Y).comp σ) = Sum.inr σ :=
  (sumSimplexEquiv X Y n).symm_apply_apply (Sum.inr σ)

def SingularHomology.sumChainComplexMap (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y ⟶
      SingularChains.singularComplex (X ⊕ Y) :=
  CategoryTheory.Limits.biprod.desc (SingularChains.singularChainMap (sumInlMap X Y))
    (SingularChains.singularChainMap (sumInrMap X Y))

def SingularHomology.sumChainInverseDegree_mo1973_4506 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    SingularChains.Chains (X ⊕ Y) n →ₗ[ℤ]
      (SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).X n :=
  SingularChains.chainLift (X ⊕ Y) n fun σ =>
    Sum.elim
      (fun τ =>
        (CategoryTheory.Limits.biprod.inl :
                SingularChains.singularComplex X ⟶
                  SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).f
            n |>.hom
          (SingularChains.simplexChain X n τ))
      (fun τ =>
        (CategoryTheory.Limits.biprod.inr :
                SingularChains.singularComplex Y ⟶
                  SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).f
            n |>.hom
          (SingularChains.simplexChain Y n τ))
      ((sumSimplexEquiv X Y n).symm σ)

theorem SingularHomology.sumChainInverseDegree_inl_mo1973_4507 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex X n) :
    sumChainInverseDegree_mo1973_4506 X Y n
        (SingularChains.simplexChain (X ⊕ Y) n ((sumInlMap X Y).comp σ)) =
      ((CategoryTheory.Limits.biprod.inl :
                SingularChains.singularComplex X ⟶
                  SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).f
            n).hom
        (SingularChains.simplexChain X n σ) := by
  simp only [sumChainInverseDegree_mo1973_4506, SingularChains.chainLift_simplex,
    sumSimplexEquiv_symm_inl, Sum.elim_inl]

theorem SingularHomology.sumChainInverseDegree_inr_mo1973_4508 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : SingularChains.SingularSimplex Y n) :
    sumChainInverseDegree_mo1973_4506 X Y n
        (SingularChains.simplexChain (X ⊕ Y) n ((sumInrMap X Y).comp σ)) =
      ((CategoryTheory.Limits.biprod.inr :
                SingularChains.singularComplex Y ⟶
                  SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).f
            n).hom
        (SingularChains.simplexChain Y n σ) := by
  simp only [sumChainInverseDegree_mo1973_4506, SingularChains.chainLift_simplex,
    sumSimplexEquiv_symm_inr, Sum.elim_inr]

theorem SingularHomology.sumChainComplexMap_comp_inverse_mo1973_4509 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    (sumChainComplexMap X Y).f n ≫ ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) =
      𝟙 ((SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).X n) := by
  apply HomologicalComplex.biprodX_ext_from
  · calc
      _ =
          ((CategoryTheory.Limits.biprod.inl :
                    SingularChains.singularComplex X ⟶
                      SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).f
                n ≫
              (sumChainComplexMap X Y).f n) ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          (SingularChains.singularChainMap (sumInlMap X Y)).f n ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (congrArg
          (fun f : SingularChains.Chains X n ⟶ SingularChains.Chains (X ⊕ Y) n =>
            f ≫ ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n))
          (HomologicalComplex.biprod_inl_desc_f (SingularChains.singularChainMap (sumInlMap X Y))
            (SingularChains.singularChainMap (sumInrMap X Y)) n))
      _ = _ := by
        apply ModuleCat.hom_ext
        apply SingularChains.chainMap_ext X n
        intro σ
        change
          sumChainInverseDegree_mo1973_4506 X Y n
              (SingularChains.inducedChain (sumInlMap X Y) n (SingularChains.simplexChain X n σ)) =
            _
        rw [SingularChains.inducedChain_simplex, sumChainInverseDegree_inl_mo1973_4507,
          CategoryTheory.Category.comp_id]
  · calc
      _ =
          ((CategoryTheory.Limits.biprod.inr :
                    SingularChains.singularComplex Y ⟶
                      SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y).f
                n ≫
              (sumChainComplexMap X Y).f n) ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          (SingularChains.singularChainMap (sumInrMap X Y)).f n ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (congrArg
          (fun f : SingularChains.Chains Y n ⟶ SingularChains.Chains (X ⊕ Y) n =>
            f ≫ ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n))
          (HomologicalComplex.biprod_inr_desc_f (SingularChains.singularChainMap (sumInlMap X Y))
            (SingularChains.singularChainMap (sumInrMap X Y)) n))
      _ = _ := by
        apply ModuleCat.hom_ext
        apply SingularChains.chainMap_ext Y n
        intro σ
        change
          sumChainInverseDegree_mo1973_4506 X Y n
              (SingularChains.inducedChain (sumInrMap X Y) n (SingularChains.simplexChain Y n σ)) =
            _
        rw [SingularChains.inducedChain_simplex, sumChainInverseDegree_inr_mo1973_4508,
          CategoryTheory.Category.comp_id]

theorem SingularHomology.sumChainInverse_comp_map_mo1973_4510 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) ≫ (sumChainComplexMap X Y).f n =
      𝟙 (SingularChains.Chains (X ⊕ Y) n) := by
  apply ModuleCat.hom_ext
  apply SingularChains.chainMap_ext (X ⊕ Y) n
  intro σ
  rcases singularSimplex_sum_split X Y n σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · change
      ((sumChainComplexMap X Y).f n).hom
          (sumChainInverseDegree_mo1973_4506 X Y n
            (SingularChains.simplexChain (X ⊕ Y) n ((sumInlMap X Y).comp τ))) =
        _
    rw [sumChainInverseDegree_inl_mo1973_4507]
    exact
      (congrArg (fun f => f.hom (SingularChains.simplexChain X n τ))
            (HomologicalComplex.biprod_inl_desc_f (SingularChains.singularChainMap (sumInlMap X Y))
              (SingularChains.singularChainMap (sumInrMap X Y)) n)).trans
        (SingularChains.inducedChain_simplex (sumInlMap X Y) n τ)
  · change
      ((sumChainComplexMap X Y).f n).hom
          (sumChainInverseDegree_mo1973_4506 X Y n
            (SingularChains.simplexChain (X ⊕ Y) n ((sumInrMap X Y).comp τ))) =
        _
    rw [sumChainInverseDegree_inr_mo1973_4508]
    exact
      (congrArg (fun f => f.hom (SingularChains.simplexChain Y n τ))
            (HomologicalComplex.biprod_inr_desc_f (SingularChains.singularChainMap (sumInlMap X Y))
              (SingularChains.singularChainMap (sumInrMap X Y)) n)).trans
        (SingularChains.inducedChain_simplex (sumInrMap X Y) n τ)

theorem SingularHomology.sumChainComplexMap_component_isIso_mo1973_4511
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    CategoryTheory.IsIso ((sumChainComplexMap X Y).f n) :=
  ⟨⟨ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n),
      sumChainComplexMap_comp_inverse_mo1973_4509 X Y n,
      sumChainInverse_comp_map_mo1973_4510 X Y n⟩⟩

def SingularHomology.sumChainComplexIso (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularChains.singularComplex X ⊞ SingularChains.singularComplex Y ≅
      SingularChains.singularComplex (X ⊕ Y) := by
  letI (n : ℕ) : CategoryTheory.IsIso ((sumChainComplexMap X Y).f n) :=
    sumChainComplexMap_component_isIso_mo1973_4511 X Y n
  letI : CategoryTheory.IsIso (sumChainComplexMap X Y) :=
    HomologicalComplex.Hom.isIso_of_components (sumChainComplexMap X Y)
  exact CategoryTheory.asIso (sumChainComplexMap X Y)

def SingularHomology.sumHomologyEquiv (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (X ⊕ Y) n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology Y n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (sumChainComplexIso X Y)).symm.toLinearEquiv.trans
    (SingularMayerVietoris.homologyBiprodEquiv (SingularChains.singularComplex X)
      (SingularChains.singularComplex Y) n)

theorem SingularHomology.sumHomologyEquiv_symm_apply (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology Y n) :
    (sumHomologyEquiv X Y n).symm a =
      SingularMayerVietoris.singularHomologyMap (sumInlMap X Y) n a.1 +
        SingularMayerVietoris.singularHomologyMap (sumInrMap X Y) n a.2 := by
  change
    (HomologicalComplex.homologyMap (sumChainComplexMap X Y) n).hom
        ((SingularMayerVietoris.homologyBiprodEquiv (SingularChains.singularComplex X)
              (SingularChains.singularComplex Y) n).symm
          a) =
      _
  exact
    SingularMayerVietoris.homologyBiprodEquiv_desc n
      (SingularChains.singularChainMap (sumInlMap X Y))
      (SingularChains.singularChainMap (sumInrMap X Y)) a

@[simp]
theorem SingularHomology.sumHomologyEquiv_inl (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    sumHomologyEquiv X Y n (SingularMayerVietoris.singularHomologyMap (sumInlMap X Y) n a) =
      (a, 0) := by
  apply (sumHomologyEquiv X Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sumHomologyEquiv_symm_apply, map_zero, add_zero]

@[simp]
theorem SingularHomology.sumHomologyEquiv_inr (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology Y n) :
    sumHomologyEquiv X Y n (SingularMayerVietoris.singularHomologyMap (sumInrMap X Y) n a) =
      (0, a) := by
  apply (sumHomologyEquiv X Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sumHomologyEquiv_symm_apply, map_zero, zero_add]

theorem SingularHomology.sumElim_homology_inl_mo1973_4520 {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n
        (SingularMayerVietoris.singularHomologyMap (sumInlMap X Y) n a) =
      SingularMayerVietoris.singularHomologyMap f n a := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (sumInlMap X Y)) (TopCat.ofHom (sumElimMap f g))
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a).symm

theorem SingularHomology.sumElim_homology_inr_mo1973_4521 {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n
        (SingularMayerVietoris.singularHomologyMap (sumInrMap X Y) n a) =
      SingularMayerVietoris.singularHomologyMap g n a := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (sumInrMap X Y)) (TopCat.ofHom (sumElimMap f g))
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a).symm

theorem SingularHomology.disjointHomology_id_apply_mo1973_4522 {X : Type}
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n a = a := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_id
      (TopCat.of X)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a

theorem SingularHomology.sumHomologyEquiv_sumElim_symm {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n
        ((sumHomologyEquiv X Y n).symm a) =
      SingularMayerVietoris.singularHomologyMap f n a.1 +
        SingularMayerVietoris.singularHomologyMap g n a.2 := by
  rw [sumHomologyEquiv_symm_apply, map_add, sumElim_homology_inl_mo1973_4520,
    sumElim_homology_inr_mo1973_4521]

theorem SingularHomology.sumHomologyEquiv_sumElim {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n a =
      SingularMayerVietoris.singularHomologyMap f n (sumHomologyEquiv X Y n a).1 +
        SingularMayerVietoris.singularHomologyMap g n (sumHomologyEquiv X Y n a).2 := by
  have h := sumHomologyEquiv_sumElim_symm f g n (sumHomologyEquiv X Y n a)
  rwa [LinearEquiv.symm_apply_apply] at h

theorem SingularHomology.sumHomologyEquiv_fold {X : Type} [TopologicalSpace X] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X ⊕ X) n) :
    SingularMayerVietoris.singularHomologyMap
        (sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)) n a =
      (sumHomologyEquiv X X n a).1 + (sumHomologyEquiv X X n a).2 := by
  rw [sumHomologyEquiv_sumElim, disjointHomology_id_apply_mo1973_4522,
    disjointHomology_id_apply_mo1973_4522]
end Mathoverflow1973
