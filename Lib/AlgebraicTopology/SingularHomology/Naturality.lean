/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.Topology.OnePointCollapse

/-!
# Naturality of the Mayer–Vietoris connecting homomorphism

The connecting homomorphism of the Mayer–Vietoris long exact sequence is natural in maps of
two-open covers: a map `f : X → Y` with `f U ⊆ U'`, `f V ⊆ V'` commutes with the connecting
maps of the two covers.

* `CoverNaturality.connecting_naturality_apply`-family (SphereTopology block) and
  `SingularMayerVietoris.connectingHomomorphism_naturality_apply` (CuspFilling block) — the
  element-level statement, with `coverRestriction` and the cover connecting maps as the
  intermediate presentation.

## Outline of the proof

1. *The chain-level square.*  The connecting map is defined on representatives via
   `intersectionToLeft`; naturality reduces to the commutation of the restriction maps
   (`coverRestriction`) with the boundary (`connectingMap_lift_is_cycle`,
   `connectingMap_homologyClassOfCycle`).
2. *Element statement.*  `connectingHomomorphism_naturality_apply` applies the general
   naturality to a cycle representative.

## Main definitions and results

* `SingularMayerVietoris.connectingHomomorphism_naturality_apply` : the naturality square on
  elements.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.2, naturality of the MV sequence

## Tags

naturality, connecting homomorphism, Mayer–Vietoris
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

def CoverNaturality.mapOn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x.val, hf x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem CoverNaturality.chainMap_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    SingularChains.singularChainMap f ≫ SingularChains.singularChainMap g =
      SingularChains.singularChainMap (g.comp f) :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g)).symm

theorem CoverNaturality.map_intersection {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') : Set.MapsTo f (U ∩ V) (U' ∩ V') := fun _ hx => ⟨hU hx.1, hV hx.2⟩

theorem CoverNaturality.inducedChain_mem_small {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') (n : ℕ) (c : SingularChains.Chains X n)
    (hc : c ∈ SingularMayerVietoris.smallChainSubmodule U V n) :
    SingularChains.inducedChain f n c ∈ SingularMayerVietoris.smallChainSubmodule U' V' n := by
  have hle :
    SingularMayerVietoris.smallChainSubmodule U V n ≤
      (SingularMayerVietoris.smallChainSubmodule U' V' n).comap
        (SingularChains.inducedChain f n) := by
    rw [SingularMayerVietoris.smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change
      SingularChains.inducedChain f n (SingularChains.simplexChain X n σ) ∈
        SingularMayerVietoris.smallChainSubmodule U' V' n
    rw [SingularChains.inducedChain_simplex]
    apply SingularMayerVietoris.simplexChain_mem_small
    rcases hσ with hσ | hσ
    · left
      rintro _ ⟨t, rfl⟩
      exact hU (hσ ⟨t, rfl⟩)
    · right
      rintro _ ⟨t, rfl⟩
      exact hV (hσ ⟨t, rfl⟩)
  exact hle hc

def CoverNaturality.smallMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.smallComplex U V ⟶ SingularMayerVietoris.smallComplex U' V' :=
  SingularMayerVietoris.liftToSmall U' V'
    (SingularMayerVietoris.smallInclusion U V ≫ SingularChains.singularChainMap f)
    (fun n c => inducedChain_mem_small U V U' V' f hU hV n c.val c.property)

theorem CoverNaturality.smallMap_inclusion {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    smallMap U V U' V' f hU hV ≫ SingularMayerVietoris.smallInclusion U' V' =
      SingularMayerVietoris.smallInclusion U V ≫ SingularChains.singularChainMap f :=
  SingularMayerVietoris.liftToSmall_inclusion U' V' _ _

theorem CoverNaturality.smallMap_left {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.toSmallLeft U V ≫ smallMap U V U' V' f hU hV =
      SingularChains.singularChainMap (mapOn f U U' hU) ≫
        SingularMayerVietoris.toSmallLeft U' V' := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion U' V')).mp
  rw [CategoryTheory.Category.assoc, smallMap_inclusion, ← CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallLeft_inclusion, CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallLeft_inclusion, chainMap_comp, chainMap_comp]
  rfl

theorem CoverNaturality.smallMap_right {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.toSmallRight U V ≫ smallMap U V U' V' f hU hV =
      SingularChains.singularChainMap (mapOn f V V' hV) ≫
        SingularMayerVietoris.toSmallRight U' V' := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion U' V')).mp
  rw [CategoryTheory.Category.assoc, smallMap_inclusion, ← CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallRight_inclusion, CategoryTheory.Category.assoc,
    SingularMayerVietoris.toSmallRight_inclusion, chainMap_comp, chainMap_comp]
  rfl

theorem CoverNaturality.intersection_left {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularChains.singularChainMap
          (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) ≫
        SingularMayerVietoris.intersectionToLeft U' V' =
      SingularMayerVietoris.intersectionToLeft U V ≫
        SingularChains.singularChainMap (mapOn f U U' hU) := by
  unfold SingularMayerVietoris.intersectionToLeft
  rw [chainMap_comp, chainMap_comp]
  rfl

theorem CoverNaturality.intersection_right {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularChains.singularChainMap
          (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) ≫
        SingularMayerVietoris.intersectionToRight U' V' =
      SingularMayerVietoris.intersectionToRight U V ≫
        SingularChains.singularChainMap (mapOn f V V' hV) := by
  unfold SingularMayerVietoris.intersectionToRight
  rw [chainMap_comp, chainMap_comp]
  rfl

def CoverNaturality.chainSequenceMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') :
    SingularMayerVietoris.chainSequence U V ⟶ SingularMayerVietoris.chainSequence U' V'
    where
  τ₁ :=
    SingularChains.singularChainMap
      (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV))
  τ₂ :=
    CategoryTheory.Limits.biprod.map (SingularChains.singularChainMap (mapOn f U U' hU))
      (SingularChains.singularChainMap (mapOn f V V' hV))
  τ₃ := smallMap U V U' V' f hU hV
  comm₁₂ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.leftMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_fst,
        CategoryTheory.Limits.biprod.map_fst, CategoryTheory.Limits.biprod.lift_fst_assoc]
      exact intersection_left U V U' V' f hU hV
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_snd,
        CategoryTheory.Limits.biprod.map_snd, CategoryTheory.Limits.biprod.lift_snd_assoc,
        CategoryTheory.Preadditive.comp_neg, CategoryTheory.Preadditive.neg_comp]
      exact congrArg Neg.neg (intersection_right U V U' V' f hU hV)
  comm₂₃ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.rightMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext'
    · simp only [CategoryTheory.Limits.biprod.inl_map_assoc,
        CategoryTheory.Limits.biprod.inl_desc, CategoryTheory.Limits.biprod.inl_desc_assoc]
      exact (smallMap_left U V U' V' f hU hV).symm
    · simp only [CategoryTheory.Limits.biprod.inr_map_assoc,
        CategoryTheory.Limits.biprod.inr_desc, CategoryTheory.Limits.biprod.inr_desc_assoc]
      exact (smallMap_right U V U' V' f hU hV).symm

theorem CoverNaturality.smallConnecting_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap
            (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) n).comp
        (SingularMayerVietoris.smallConnectingMap U V n) =
      (SingularMayerVietoris.smallConnectingMap U' V' n).comp
        (SingularMayerVietoris.homologyLinearMap (smallMap U V U' V' f hU hV) (n + 1)) :=
  SingularMayerVietoris.connectingMap_naturality
    (SingularMayerVietoris.chainSequence_shortExact U V) (chainSequenceMap U V U' V' f hU hV)
    (SingularMayerVietoris.chainSequence_shortExact U' V') n

theorem CoverNaturality.comparison_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U U')
    (hV : Set.MapsTo f V V') (n : ℕ) :
    (SingularMayerVietoris.smallHomologyComparison U' V' n).comp
        (SingularMayerVietoris.homologyLinearMap (smallMap U V U' V' f hU hV) n) =
      (SingularMayerVietoris.singularHomologyMap f n).comp
        (SingularMayerVietoris.smallHomologyComparison U V n) := by
  unfold SingularMayerVietoris.smallHomologyComparison
  rw [← SingularMayerVietoris.homologyLinearMap_comp, smallMap_inclusion,
    SingularMayerVietoris.homologyLinearMap_comp]

theorem CoverNaturality.connecting_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap
            (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)) n).comp
        (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n) =
      (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n).comp
        (SingularMayerVietoris.singularHomologyMap f (n + 1)) := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (SingularMayerVietoris.smallHomologyEquiv U V hU hV hc (n + 1)).surjective a
  have hb' : SingularMayerVietoris.smallHomologyComparison U V (n + 1) b = a := hb
  rw [← hb']
  change
    SingularMayerVietoris.singularHomologyMap _ n
        (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n
          (SingularMayerVietoris.smallHomologyComparison U V (n + 1) b)) =
      SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n
        (SingularMayerVietoris.singularHomologyMap f (n + 1)
          (SingularMayerVietoris.smallHomologyComparison U V (n + 1) b))
  rw [SingularMayerVietoris.connectingHomomorphism_comparison]
  have hcomp := LinearMap.congr_fun (comparison_naturality U V U' V' f hfU hfV (n + 1)) b
  change
    SingularMayerVietoris.smallHomologyComparison U' V' (n + 1)
        (SingularMayerVietoris.homologyLinearMap (smallMap U V U' V' f hfU hfV) (n + 1) b) =
      SingularMayerVietoris.singularHomologyMap f (n + 1)
        (SingularMayerVietoris.smallHomologyComparison U V (n + 1) b) at hcomp
  rw [← hcomp, SingularMayerVietoris.connectingHomomorphism_comparison]
  exact LinearMap.congr_fun (smallConnecting_naturality U V U' V' f hfU hfV n) b

theorem CoverNaturality.connecting_naturality_apply {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.singularHomologyMap
        (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)) n
        (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n a) =
      SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a) :=
  LinearMap.congr_fun (connecting_naturality U V U' V' f hfU hfV hU hV hc hU' hV' hc' n) a

def CoverNaturality.intersectionSwap {X : Type} [TopologicalSpace X] (U V : Set X) :
    C(↥(U ∩ V), ↥(V ∩ U)) :=
  ⟨fun x => ⟨x.val, x.property.symm⟩, continuous_subtype_val.subtype_mk _⟩

def CoverNaturality.smallSwap {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.smallComplex U V ⟶ SingularMayerVietoris.smallComplex V U :=
  SingularMayerVietoris.liftToSmall V U (SingularMayerVietoris.smallInclusion U V)
    (fun n c => by
      change c.val ∈ SingularMayerVietoris.smallChainSubmodule V U n
      simpa only [SingularMayerVietoris.smallChainSubmodule, sup_comm] using c.property)

theorem CoverNaturality.smallSwap_inclusion {X : Type} [TopologicalSpace X] (U V : Set X) :
    smallSwap U V ≫ SingularMayerVietoris.smallInclusion V U =
      SingularMayerVietoris.smallInclusion U V :=
  SingularMayerVietoris.liftToSmall_inclusion V U _ _

theorem CoverNaturality.smallSwap_left {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.toSmallLeft U V ≫ smallSwap U V =
      SingularMayerVietoris.toSmallRight V U := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion V U)).mp
  rw [CategoryTheory.Category.assoc, smallSwap_inclusion,
    SingularMayerVietoris.toSmallLeft_inclusion, SingularMayerVietoris.toSmallRight_inclusion]

theorem CoverNaturality.smallSwap_right {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.toSmallRight U V ≫ smallSwap U V =
      SingularMayerVietoris.toSmallLeft V U := by
  apply (CategoryTheory.cancel_mono (SingularMayerVietoris.smallInclusion V U)).mp
  rw [CategoryTheory.Category.assoc, smallSwap_inclusion,
    SingularMayerVietoris.toSmallRight_inclusion, SingularMayerVietoris.toSmallLeft_inclusion]

theorem CoverNaturality.intersectionSwap_left {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    SingularChains.singularChainMap (intersectionSwap U V) ≫
        SingularMayerVietoris.intersectionToLeft V U =
      SingularMayerVietoris.intersectionToRight U V := by
  unfold SingularMayerVietoris.intersectionToLeft SingularMayerVietoris.intersectionToRight
  rw [chainMap_comp]
  rfl

theorem CoverNaturality.intersectionSwap_right {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    SingularChains.singularChainMap (intersectionSwap U V) ≫
        SingularMayerVietoris.intersectionToRight V U =
      SingularMayerVietoris.intersectionToLeft U V := by
  unfold SingularMayerVietoris.intersectionToLeft SingularMayerVietoris.intersectionToRight
  rw [chainMap_comp]
  rfl

def CoverNaturality.chainSequenceSwap {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularMayerVietoris.chainSequence U V ⟶ SingularMayerVietoris.chainSequence V U
    where
  τ₁ := -SingularChains.singularChainMap (intersectionSwap U V)
  τ₂ :=
    CategoryTheory.Limits.biprod.lift CategoryTheory.Limits.biprod.snd
      CategoryTheory.Limits.biprod.fst
  τ₃ := smallSwap U V
  comm₁₂ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.leftMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_fst,
        CategoryTheory.Limits.biprod.lift_snd, CategoryTheory.Preadditive.neg_comp]
      exact congrArg Neg.neg (intersectionSwap_left U V)
    · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_snd,
        CategoryTheory.Limits.biprod.lift_fst, CategoryTheory.Preadditive.neg_comp,
        CategoryTheory.Preadditive.comp_neg, neg_neg]
      exact intersectionSwap_right U V
  comm₂₃ := by
    dsimp only [SingularMayerVietoris.chainSequence, SingularMayerVietoris.rightMap,
      SingularMayerVietoris.middleComplex]
    apply CategoryTheory.Limits.biprod.hom_ext'
    · simp only [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.comp_add,
        CategoryTheory.Limits.biprod.inl_snd_assoc, CategoryTheory.Limits.biprod.inl_fst_assoc,
        CategoryTheory.Limits.zero_comp, zero_add, CategoryTheory.Limits.biprod.inl_desc_assoc]
      exact (smallSwap_left U V).symm
    · simp only [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.comp_add,
        CategoryTheory.Limits.biprod.inr_snd_assoc, CategoryTheory.Limits.biprod.inr_fst_assoc,
        CategoryTheory.Limits.zero_comp, add_zero, CategoryTheory.Limits.biprod.inr_desc_assoc]
      exact (smallSwap_right U V).symm

theorem CoverNaturality.smallConnecting_swap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularMayerVietoris.SmallHomology U V (n + 1)) :
    SingularMayerVietoris.smallConnectingMap V U n
        (SingularMayerVietoris.homologyLinearMap (smallSwap U V) (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap (intersectionSwap U V) n
          (SingularMayerVietoris.smallConnectingMap U V n a) := by
  have h :=
    LinearMap.congr_fun
      (SingularMayerVietoris.connectingMap_naturality
        (SingularMayerVietoris.chainSequence_shortExact U V) (chainSequenceSwap U V)
        (SingularMayerVietoris.chainSequence_shortExact V U) n)
      a
  change
    SingularMayerVietoris.homologyLinearMap
        (-SingularChains.singularChainMap (intersectionSwap U V)) n
        (SingularMayerVietoris.smallConnectingMap U V n a) =
      _ at h
  rw [SingularMayerVietoris.homologyLinearMap_neg] at h
  exact h.symm

theorem CoverNaturality.comparison_swap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularMayerVietoris.SmallHomology U V n) :
    SingularMayerVietoris.smallHomologyComparison V U n
        (SingularMayerVietoris.homologyLinearMap (smallSwap U V) n a) =
      SingularMayerVietoris.smallHomologyComparison U V n a := by
  change
    SingularMayerVietoris.homologyLinearMap (SingularMayerVietoris.smallInclusion V U) n
        (SingularMayerVietoris.homologyLinearMap (smallSwap U V) n a) =
      _
  rw [← LinearMap.comp_apply, ← SingularMayerVietoris.homologyLinearMap_comp, smallSwap_inclusion]
  rfl

theorem CoverNaturality.connecting_swap {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ) (hc' : V ∪ U = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.connectingHomomorphism V U hV hU hc' n a =
      -SingularMayerVietoris.singularHomologyMap (intersectionSwap U V) n
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n a) := by
  obtain ⟨b, hb⟩ := (SingularMayerVietoris.smallHomologyEquiv U V hU hV hc (n + 1)).surjective a
  have hb' : SingularMayerVietoris.smallHomologyComparison U V (n + 1) b = a := hb
  rw [← hb', SingularMayerVietoris.connectingHomomorphism_comparison]
  rw [← comparison_swap U V (n + 1) b, SingularMayerVietoris.connectingHomomorphism_comparison]
  exact smallConnecting_swap U V n b

def CoverNaturality.reversingIntersectionMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hU : Set.MapsTo f U V')
    (hV : Set.MapsTo f V U') : C(↥(U ∩ V), ↥(U' ∩ V')) :=
  mapOn f _ _ (fun _ hx => ⟨hV hx.2, hU hx.1⟩)

theorem CoverNaturality.connecting_reversing_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U V')
    (hfV : Set.MapsTo f V U') (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' n
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap (reversingIntersectionMap U V U' V' f hfU hfV) n
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc n a) := by
  have hswap : V' ∪ U' = Set.univ := (Set.union_comm V' U').trans hc'
  rw [connecting_swap V' U' hV' hU' hswap hc']
  rw [← connecting_naturality_apply U V V' U' f hfU hfV hU hV hc hV' hU' hswap]
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

def CoverNaturality.overlapCoordinateMap {X Y S T : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T] (U V : Set X) (U' V' : Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (eS : S ≃ₕ ↥(U ∩ V))
    (eT : T ≃ₕ ↥(U' ∩ V')) : C(S, T) :=
  eT.invFun.comp
    ((mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)).comp eS.toFun)

theorem CoverNaturality.normalized_connecting_naturality {X Y S T : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T]
    (U V : Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (eS : S ≃ₕ ↥(U ∩ V)) (eT : T ≃ₕ ↥(U' ∩ V')) (hU : IsOpen U)
    (hV : IsOpen V) (hc : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V')
    (hc' : U' ∪ V' = Set.univ) (k : ℕ) (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (overlapCoordinateMap U V U' V' f hfU hfV eS eT) k
        ((SingularHomology.homotopyEquivHomologyEquiv eS k).symm
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc k a)) =
      (SingularHomology.homotopyEquivHomologyEquiv eT k).symm
        (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' k
          (SingularMayerVietoris.singularHomologyMap f (k + 1) a)) := by
  have hS :
    SingularMayerVietoris.singularHomologyMap eS.toFun k
        ((SingularHomology.homotopyEquivHomologyEquiv eS k).symm
          (SingularMayerVietoris.connectingHomomorphism U V hU hV hc k a)) =
      SingularMayerVietoris.connectingHomomorphism U V hU hV hc k a :=
    (SingularHomology.homotopyEquivHomologyEquiv eS k).apply_symm_apply _
  unfold overlapCoordinateMap
  rw [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply, hS,
    connecting_naturality_apply U V U' V' f hfU hfV hU hV hc hU' hV' hc',
    SingularHomology.homotopyEquivHomologyEquiv_symm_apply]
  rfl

def SingularMayerVietoris.coverRestriction {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x, hf x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

def SingularMayerVietoris.intersectionRestriction {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : C((U ∩ V : Set X), (U' ∩ V' : Set Y)) :=
  coverRestriction f (U ∩ V) (U' ∩ V') (fun _ hx => ⟨hfU hx.1, hfV hx.2⟩)

theorem SingularMayerVietoris.coverRestriction_ambient {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    SingularChains.singularChainMap (coverRestriction f A B hf) ≫
        SingularChains.singularChainMap (subtypeInclusion B) =
      SingularChains.singularChainMap (subtypeInclusion A) ≫ SingularChains.singularChainMap f := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  have h₁ :=
    F.map_comp (TopCat.ofHom (coverRestriction f A B hf)) (TopCat.ofHom (subtypeInclusion B))
  have h₂ := F.map_comp (TopCat.ofHom (subtypeInclusion A)) (TopCat.ofHom f)
  exact h₁.symm.trans h₂

theorem SingularMayerVietoris.coverRestriction_intersection_left {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    intersectionToLeft U V ≫ SingularChains.singularChainMap (coverRestriction f U U' hfU) =
      SingularChains.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        intersectionToLeft U' V' := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  have h₁ :=
    F.map_comp (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.ofHom (coverRestriction f U U' hfU))
  have h₂ :=
    F.map_comp (TopCat.ofHom (intersectionRestriction f U V U' V' hfU hfV))
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U' ∩ V' ⊆ U')))
  exact h₁.symm.trans h₂

theorem SingularMayerVietoris.coverRestriction_intersection_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    intersectionToRight U V ≫ SingularChains.singularChainMap (coverRestriction f V V' hfV) =
      SingularChains.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        intersectionToRight U' V' := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  have h₁ :=
    F.map_comp (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopCat.ofHom (coverRestriction f V V' hfV))
  have h₂ :=
    F.map_comp (TopCat.ofHom (intersectionRestriction f U V U' V' hfU hfV))
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U' ∩ V' ⊆ V')))
  exact h₁.symm.trans h₂

theorem SingularMayerVietoris.inducedChain_mem_small_of_mapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (n : ℕ) (c : SingularChains.Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) :
    SingularChains.inducedChain f n c ∈ smallChainSubmodule U' V' n := by
  have hle :
    smallChainSubmodule U V n ≤
      (smallChainSubmodule U' V' n).comap (SingularChains.inducedChain f n) := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change
      SingularChains.inducedChain f n (SingularChains.simplexChain X n σ) ∈
        smallChainSubmodule U' V' n
    rw [SingularChains.inducedChain_simplex]
    apply simplexChain_mem_small
    rcases hσ with hσ | hσ
    · left
      rintro _ ⟨s, rfl⟩
      exact hfU (hσ ⟨s, rfl⟩)
    · right
      rintro _ ⟨s, rfl⟩
      exact hfV (hσ ⟨s, rfl⟩)
  exact hle hc

def SingularMayerVietoris.smallMapOfMapsTo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : smallComplex U V ⟶ smallComplex U' V' :=
  liftToSmall U' V' (smallInclusion U V ≫ SingularChains.singularChainMap f)
    (fun n c => inducedChain_mem_small_of_mapsTo f U V U' V' hfU hfV n c.1 c.2)

@[simp]
theorem SingularMayerVietoris.smallMapOfMapsTo_inclusion {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V' =
      smallInclusion U V ≫ SingularChains.singularChainMap f :=
  liftToSmall_inclusion U' V' _ _

theorem SingularMayerVietoris.toSmallLeft_smallMapOfMapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    toSmallLeft U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV =
      SingularChains.singularChainMap (coverRestriction f U U' hfU) ≫ toSmallLeft U' V' := by
  apply (CategoryTheory.cancel_mono (smallInclusion U' V')).mp
  calc
    (toSmallLeft U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV) ≫ smallInclusion U' V' =
        toSmallLeft U V ≫ (smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V') :=
      CategoryTheory.Category.assoc _ _ _
    _ = toSmallLeft U V ≫ (smallInclusion U V ≫ SingularChains.singularChainMap f) :=
      (congrArg (toSmallLeft U V ≫ ·) (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV))
    _ = (toSmallLeft U V ≫ smallInclusion U V) ≫ SingularChains.singularChainMap f :=
      (CategoryTheory.Category.assoc _ _ _).symm
    _ = SingularChains.singularChainMap (subtypeInclusion U) ≫ SingularChains.singularChainMap f :=
      (congrArg (· ≫ SingularChains.singularChainMap f) (toSmallLeft_inclusion U V))
    _ =
        SingularChains.singularChainMap (coverRestriction f U U' hfU) ≫
          SingularChains.singularChainMap (subtypeInclusion U') :=
      (coverRestriction_ambient f U U' hfU).symm
    _ =
        SingularChains.singularChainMap (coverRestriction f U U' hfU) ≫
          (toSmallLeft U' V' ≫ smallInclusion U' V') :=
      (congrArg (SingularChains.singularChainMap (coverRestriction f U U' hfU) ≫ ·)
        (toSmallLeft_inclusion U' V').symm)
    _ =
        (SingularChains.singularChainMap (coverRestriction f U U' hfU) ≫ toSmallLeft U' V') ≫
          smallInclusion U' V' :=
      (CategoryTheory.Category.assoc _ _ _).symm

theorem SingularMayerVietoris.toSmallRight_smallMapOfMapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    toSmallRight U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV =
      SingularChains.singularChainMap (coverRestriction f V V' hfV) ≫ toSmallRight U' V' := by
  apply (CategoryTheory.cancel_mono (smallInclusion U' V')).mp
  calc
    (toSmallRight U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV) ≫ smallInclusion U' V' =
        toSmallRight U V ≫ (smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V') :=
      CategoryTheory.Category.assoc _ _ _
    _ = toSmallRight U V ≫ (smallInclusion U V ≫ SingularChains.singularChainMap f) :=
      (congrArg (toSmallRight U V ≫ ·) (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV))
    _ = (toSmallRight U V ≫ smallInclusion U V) ≫ SingularChains.singularChainMap f :=
      (CategoryTheory.Category.assoc _ _ _).symm
    _ = SingularChains.singularChainMap (subtypeInclusion V) ≫ SingularChains.singularChainMap f :=
      (congrArg (· ≫ SingularChains.singularChainMap f) (toSmallRight_inclusion U V))
    _ =
        SingularChains.singularChainMap (coverRestriction f V V' hfV) ≫
          SingularChains.singularChainMap (subtypeInclusion V') :=
      (coverRestriction_ambient f V V' hfV).symm
    _ =
        SingularChains.singularChainMap (coverRestriction f V V' hfV) ≫
          (toSmallRight U' V' ≫ smallInclusion U' V') :=
      (congrArg (SingularChains.singularChainMap (coverRestriction f V V' hfV) ≫ ·)
        (toSmallRight_inclusion U' V').symm)
    _ =
        (SingularChains.singularChainMap (coverRestriction f V V' hfV) ≫ toSmallRight U' V') ≫
          smallInclusion U' V' :=
      (CategoryTheory.Category.assoc _ _ _).symm

def SingularMayerVietoris.coverMiddleMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : middleComplex U V ⟶ middleComplex U' V' :=
  CategoryTheory.Limits.biprod.map (SingularChains.singularChainMap (coverRestriction f U U' hfU))
    (SingularChains.singularChainMap (coverRestriction f V V' hfV))

theorem SingularMayerVietoris.intersectionRestriction_leftMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    SingularChains.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫ leftMap U' V' =
      leftMap U V ≫ coverMiddleMap f U V U' V' hfU hfV := by
  change
    SingularChains.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        CategoryTheory.Limits.biprod.lift (intersectionToLeft U' V')
          (-(intersectionToRight U' V')) =
      CategoryTheory.Limits.biprod.lift (intersectionToLeft U V) (-(intersectionToRight U V)) ≫
        CategoryTheory.Limits.biprod.map
          (SingularChains.singularChainMap (coverRestriction f U U' hfU))
          (SingularChains.singularChainMap (coverRestriction f V V' hfV))
  apply CategoryTheory.Limits.biprod.hom_ext
  · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_fst,
      CategoryTheory.Limits.biprod.map_fst, CategoryTheory.Limits.biprod.lift_fst_assoc]
    exact (coverRestriction_intersection_left f U V U' V' hfU hfV).symm
  · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_snd,
      CategoryTheory.Limits.biprod.map_snd, CategoryTheory.Limits.biprod.lift_snd_assoc,
      CategoryTheory.Preadditive.comp_neg, CategoryTheory.Preadditive.neg_comp]
    exact congrArg Neg.neg (coverRestriction_intersection_right f U V U' V' hfU hfV).symm

theorem SingularMayerVietoris.coverMiddleMap_rightMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    coverMiddleMap f U V U' V' hfU hfV ≫ rightMap U' V' =
      rightMap U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV := by
  change
    CategoryTheory.Limits.biprod.map
          (SingularChains.singularChainMap (coverRestriction f U U' hfU))
          (SingularChains.singularChainMap (coverRestriction f V V' hfV)) ≫
        CategoryTheory.Limits.biprod.desc (toSmallLeft U' V') (toSmallRight U' V') =
      CategoryTheory.Limits.biprod.desc (toSmallLeft U V) (toSmallRight U V) ≫
        smallMapOfMapsTo f U V U' V' hfU hfV
  apply CategoryTheory.Limits.biprod.hom_ext'
  · simp only [CategoryTheory.Limits.biprod.inl_map_assoc,
      CategoryTheory.Limits.biprod.inl_desc_assoc, CategoryTheory.Limits.biprod.inl_desc]
    exact (toSmallLeft_smallMapOfMapsTo f U V U' V' hfU hfV).symm
  · simp only [CategoryTheory.Limits.biprod.inr_map_assoc,
      CategoryTheory.Limits.biprod.inr_desc_assoc, CategoryTheory.Limits.biprod.inr_desc]
    exact (toSmallRight_smallMapOfMapsTo f U V U' V' hfU hfV).symm

def SingularMayerVietoris.chainSequenceMapOfMapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : chainSequence U V ⟶ chainSequence U' V'
    where
  τ₁ := SingularChains.singularChainMap (intersectionRestriction f U V U' V' hfU hfV)
  τ₂ := coverMiddleMap f U V U' V' hfU hfV
  τ₃ := smallMapOfMapsTo f U V U' V' hfU hfV
  comm₁₂ := intersectionRestriction_leftMap f U V U' V' hfU hfV
  comm₂₃ := coverMiddleMap_rightMap f U V U' V' hfU hfV

theorem SingularMayerVietoris.smallHomologyComparison_naturality_of_comm {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (g : smallComplex U V ⟶ smallComplex U' V')
    (hg : g ≫ smallInclusion U' V' = smallInclusion U V ≫ SingularChains.singularChainMap f)
    (n : ℕ) (a : SmallHomology U V n) :
    smallHomologyComparison U' V' n (homologyLinearMap g n a) =
      singularHomologyMap f n (smallHomologyComparison U V n a) := by
  have h := congrArg (fun q => homologyLinearMap q n) hg
  rw [homologyLinearMap_comp, homologyLinearMap_comp] at h
  exact LinearMap.congr_fun h a

theorem SingularMayerVietoris.connectingHomomorphism_naturality_of_sequenceMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (hU' : IsOpen U')
    (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) (φ : chainSequence U V ⟶ chainSequence U' V')
    (hφ : φ.τ₃ ≫ smallInclusion U' V' = smallInclusion U V ≫ SingularChains.singularChainMap f)
    (n : ℕ) :
    (homologyLinearMap φ.τ₁ n).comp (connectingHomomorphism U V hU hV hcover n) =
      (connectingHomomorphism U' V' hU' hV' hcover' n).comp (singularHomologyMap f (n + 1)) := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (smallHomologyEquiv U V hU hV hcover (n + 1)).surjective a
  have hb' : smallHomologyComparison U V (n + 1) b = a := hb
  change
    homologyLinearMap φ.τ₁ n (connectingHomomorphism U V hU hV hcover n a) =
      connectingHomomorphism U' V' hU' hV' hcover' n (singularHomologyMap f (n + 1) a)
  rw [← hb', connectingHomomorphism_comparison]
  have hδ :
    homologyLinearMap φ.τ₁ n (smallConnectingMap U V n b) =
      smallConnectingMap U' V' n (homologyLinearMap φ.τ₃ (n + 1) b) :=
    LinearMap.congr_fun
      (connectingMap_naturality (chainSequence_shortExact U V) φ (chainSequence_shortExact U' V')
        n)
      b
  have hc :=
    (connectingHomomorphism_comparison U' V' hU' hV' hcover' n
        (homologyLinearMap φ.τ₃ (n + 1) b)).symm
  have hn :=
    congrArg (connectingHomomorphism U' V' hU' hV' hcover' n)
      (smallHomologyComparison_naturality_of_comm f U V U' V' φ.τ₃ hφ (n + 1) b)
  exact hδ.trans (hc.trans hn)

theorem SingularMayerVietoris.connectingHomomorphism_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) (n : ℕ) :
    (singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n).comp
        (connectingHomomorphism U V hU hV hcover n) =
      (connectingHomomorphism U' V' hU' hV' hcover' n).comp (singularHomologyMap f (n + 1)) :=
  connectingHomomorphism_naturality_of_sequenceMap f U V U' V' hU hV hcover hU' hV' hcover'
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV)
    (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV) n

theorem SingularMayerVietoris.connectingHomomorphism_naturality_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
    (n : ℕ) (a : SingularHomology X (n + 1)) :
    singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n
        (connectingHomomorphism U V hU hV hcover n a) =
      connectingHomomorphism U' V' hU' hV' hcover' n (singularHomologyMap f (n + 1) a) :=
  LinearMap.congr_fun
    (connectingHomomorphism_naturality f U V U' V' hfU hfV hU hV hcover hU' hV' hcover' n) a
end Mathoverflow1973
