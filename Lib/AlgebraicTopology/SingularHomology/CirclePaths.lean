/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.PathClass
public import Lib.AlgebraicTopology.SingularHomology.Sum

/-!
# Circle paths, the positive loop, and the circle section of `H_n(S¹ × X)`

The circle `S¹` is covered by two overlapping arcs `arcU`, `arcV`
(`SingularHomology.CircleTopology`). This file builds the concrete one-chains and
sections on that cover, and identifies the circle factor of the Künneth splitting
`H_n(S¹ × X) ≅ H_n(X) ⊕ H_{n-1}(X)` (`SingularHomology.circleProductHomologyEquiv`)
with the *positive circle cross*: crossing a class with the homology class of the
positively-oriented loop.

## Main definitions and results

* `PeriodTorusHigherHomology.CirclePaths.positiveLoop` : the loop `t ↦ t` on
  `AddCircle 1`, the positive generator of `π₁(S¹)`.
* `PeriodTorusHigherHomology.CirclePaths.arcSumCycle` : the one-cycle obtained by
  splitting the positive loop at the quarter and three-quarter points into the
  two arc paths `uCirclePath`, `vCirclePath`.
* `PeriodTorusHigherHomology.positiveCircleCross` : the map `H_n(X) → H_{n+1}(S¹ × X)`
  crossing with `[positiveLoop]`; realized at cycle level by the arc-sum cycle
  (`positiveCircleCross_arcSum_cycleClass`).
* `PeriodTorusHigherHomology.circleBoundary_positiveCircleCross`,
  `circleProductHomologyEquiv_positiveCircleCross` : the positive circle cross is the
  `H_{n-1}(X)`-summand section of the circle-product splitting.
* `PeriodTorusHigherHomology.positiveCircleCross_naturality` : naturality in `X`.

## Implementation notes

* `twoChainMiddle`, `twoChainSmallCycle`, `connectingHomomorphism_twoChain` realize a
  Mayer–Vietoris two-chain (a pair of `(n+1)`-chains on `U`, `V` with prescribed
  boundary on `U ∩ V`) as a cycle of the small chain complex; this is the chain-level
  engine behind the connecting-homomorphism computation.
* `quarterIntersectionSection`, `threeQuarterIntersectionSection` are the constant
  sections of the intersection `productU ∩ productV ≅ X ⊔ X` at the quarter and
  three-quarter points; their difference is the intersection difference cycle.
* `uCrossChain`, `vCrossChain` are the cross products of a cycle with the two arc
  paths; their sum is the `arcSumCycle` cross product
  (`arcCrossChains_inclusion_sum`).

## Tags

circle, positive loop, Mayer–Vietoris, cross product, Künneth
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

open SingularHomology

def PeriodTorusHigherHomology.CirclePaths.circleTranslation (a : ℝ) :
    C((CircleTopology.Circle),
      (CircleTopology.Circle)) :=
  ⟨fun z => (a : (CircleTopology.Circle)) + z, by
    exact
      (continuous_const :
            Continuous
              (fun _ : (CircleTopology.Circle) =>
                (a : (CircleTopology.Circle)))).add
        continuous_id⟩

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply (a : ℝ)
    (z : (CircleTopology.Circle)) :
    circleTranslation a z = (a : (CircleTopology.Circle)) + z :=
  rfl

def PeriodTorusHigherHomology.CirclePaths.circleTranslationHomotopy (a : ℝ) :
    (circleTranslation a).Homotopy
      (ContinuousMap.id (CircleTopology.Circle))
    where
  toFun
    p := ((((1 - (p.1 : ℝ)) * a : ℝ) : (CircleTopology.Circle)) + p.2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            continuous_const)).add
      continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_singularHomologyMap (a : ℝ)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (circleTranslation a) n = LinearMap.id := by
  rw [homotopy_homologyMap (circleTranslationHomotopy a) n,
    singularHomologyMap_id]

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_inducedHomology (a : ℝ) :
    SingularChains.inducedHomology (circleTranslation a) = LinearMap.id :=
  circleTranslation_singularHomologyMap a 1

theorem PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation (a : ℝ)
    {x : (CircleTopology.Circle)} (p : Path x x) :
    SingularChains.loopHomologyClass (p.map (circleTranslation a).continuous) =
      SingularChains.loopHomologyClass p := by
  rw [← SingularChains.inducedHomology_loopHomologyClass (circleTranslation a) x p,
    circleTranslation_inducedHomology]
  rfl


def PeriodTorusHigherHomology.CirclePaths.positiveLoop :
    Path (0 : (CircleTopology.Circle)) 0
    where
  toFun t := ((t : ℝ) : (CircleTopology.Circle))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := AddCircle.coe_zero (1 : ℝ)
  target' := AddCircle.coe_period (1 : ℝ)

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply (t : unitInterval) :
    positiveLoop t = ((t : ℝ) : (CircleTopology.Circle)) :=
  rfl


def PeriodTorusHigherHomology.positiveCircleCross (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((CircleTopology.Circle) × X) (n + 1) :=
  crossProductHomology (CircleTopology.Circle) X n
    (SingularChains.loopHomologyClass CirclePaths.positiveLoop)


theorem PeriodTorusHigherHomology.crossProductEdge_boundary_of_right_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    ((SingularChains.singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b.1) =
      crossProductZeroLeft X Y n (((SingularChains.singularComplex X).d 1 0).hom a) b.1 := by
  cases n with
  | zero => exact crossProductEdge_boundary_zero a b.1
  | succ
    n =>
    have hb : ((SingularChains.singularComplex Y).d (n + 1) n).hom b.1 = 0 := by
      simpa only [Nat.succ_sub_one] using
        SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Y)
          (n + 1) b
    simp only [crossProductEdge_boundary, hb, map_zero, sub_zero]

theorem PeriodTorusHigherHomology.crossProductEdge_path_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) {x y : X} (p : Path x y)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    ((SingularChains.singularComplex (X × Y)).d (n + 1) n).hom
        (crossProductEdge X Y n (SingularChains.pathChain p) b.1) =
      SingularChains.inducedChain (crossInsertLeft y) n b.1 -
        SingularChains.inducedChain (crossInsertLeft x) n b.1 := by
  rw [crossProductEdge_boundary_of_right_cycle]
  change
    crossProductZeroLeft X Y n (SingularChains.boundaryOne X (SingularChains.pathChain p)) b.1 = _
  rw [SingularChains.boundaryOne_pathChain, map_sub, LinearMap.sub_apply]
  simp only [SingularChains.pointChain, crossProductZeroLeft_simplex_left]
  rfl

theorem PeriodTorusHigherHomology.const_prodMk_id_eq_crossInsertLeft_mo1973_12793
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) :
    (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y) = crossInsertLeft x := by
  apply ContinuousMap.ext
  intro y
  rfl


def PeriodTorusHigherHomology.biprodElement_mo1973_12801
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.X n) (b : L.X n) : (K ⊞ L).X n :=
  ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
    ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b

theorem PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (n : ℕ) (z : J.X n) :
    ((CategoryTheory.Limits.biprod.lift f g).f n).hom z =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom ((f.f n).hom z) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom ((g.f n).hom z) := by
  have htotal :=
    congrArg (fun h => h.hom (((CategoryTheory.Limits.biprod.lift f g).f n).hom z))
      (HomologicalComplex.biprod_total_f K L n)
  have hfst := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_fst_f f g n)
  have hsnd := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_snd_f f g n)
  change
    ((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (f.f n).hom z at hfst
  change
    ((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (g.f n).hom z at hsnd
  change
    ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) =
      ((CategoryTheory.Limits.biprod.lift f g).f n).hom z at htotal
  rw [hfst, hsnd] at htotal
  exact htotal.symm

theorem PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803
    {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T) (n : ℕ) (a : K.X n)
    (b : L.X n) :
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom (biprodElement_mo1973_12801 K L n a b) =
      (f.f n).hom a + (g.f n).hom b := by
  change
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b) =
      _
  rw [map_add]
  congr 1
  · exact congrArg (fun h => h.hom a) (HomologicalComplex.biprod_inl_desc_f f g n)
  · exact congrArg (fun h => h.hom b) (HomologicalComplex.biprod_inr_desc_f f g n)

theorem PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i j : ℕ) (a : K.X i) (b : L.X i) :
    ((K ⊞ L).d i j).hom (biprodElement_mo1973_12801 K L i a b) =
      biprodElement_mo1973_12801 K L j ((K.d i j).hom a) ((L.d i j).hom b) := by
  have hK := congrArg (fun f => f.hom a) ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).comm i j)
  have hL := congrArg (fun f => f.hom b) ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).comm i j)
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a) =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f j).hom ((K.d i j).hom a) at hK
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f j).hom ((L.d i j).hom b) at hL
  change
    ((K ⊞ L).d i j).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      _
  rw [map_add, hK, hL]
  rfl

theorem PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (i j : ℕ) (a : K.X i)
    (b : L.X i) (z : J.X j) (ha : (K.d i j).hom a = (f.f j).hom z)
    (hb : (L.d i j).hom b = (g.f j).hom z) :
    ((CategoryTheory.Limits.biprod.lift f g).f j).hom z =
      ((K ⊞ L).d i j).hom (biprodElement_mo1973_12801 K L i a b) := by
  have hlift := biprod_lift_f_apply_mo1973_12802 f g j z
  have hboundary := biprodElement_boundary_mo1973_12804 K L i j a b
  have hab := congrArg₂ (biprodElement_mo1973_12801 K L j) ha hb
  exact hlift.trans (hab.symm.trans hboundary.symm)

def PeriodTorusHigherHomology.twoChainMiddle {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ)
    (a : SingularChains.Chains U (n + 1)) (b : SingularChains.Chains V (n + 1)) :
    (SingularMayerVietoris.middleComplex U V).X (n + 1) :=
  biprodElement_mo1973_12801 (SingularChains.singularComplex U) (SingularChains.singularComplex V)
    (n + 1) a b

theorem PeriodTorusHigherHomology.twoChainMiddle_rightMap {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1)) :
    ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) =
      ((SingularMayerVietoris.toSmallLeft U V).f (n + 1)).hom a +
        ((SingularMayerVietoris.toSmallRight U V).f (n + 1)).hom b :=
  biprodElement_desc_mo1973_12803 (SingularMayerVietoris.toSmallLeft U V)
    (SingularMayerVietoris.toSmallRight U V) (n + 1) a b

theorem PeriodTorusHigherHomology.twoChainMiddle_boundary {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.leftMap U V).f n).hom z.1 =
      ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom (twoChainMiddle U V n a b) :=
  biprod_lift_eq_boundary_mo1973_12805 (SingularMayerVietoris.intersectionToLeft U V)
    (-(SingularMayerVietoris.intersectionToRight U V)) (n + 1) n a b z.1 ha hb

theorem PeriodTorusHigherHomology.twoChainSmallCycle_condition {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.smallComplex U V).d (n + 1) n).hom
        (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b)) =
      0 := by
  have hcomm :=
    congrArg (fun f => f.hom (twoChainMiddle U V n a b))
      ((SingularMayerVietoris.rightMap U V).comm (n + 1) n)
  have hzero := congrArg (fun f => (f.f n).hom z.1) (SingularMayerVietoris.leftMap_rightMap U V)
  calc
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom
            (twoChainMiddle U V n a b)) :=
      hcomm
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.leftMap U V).f n).hom z.1) :=
      (congrArg ((SingularMayerVietoris.rightMap U V).f n).hom
        (twoChainMiddle_boundary U V n a b z ha hb).symm)
    _ = 0 := hzero

def PeriodTorusHigherHomology.twoChainSmallCycle {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularChains.Chains U (n + 1)) (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularMayerVietoris.smallComplex U V) (n + 1)
    (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b))
    (by
      rw [Nat.add_sub_cancel]
      exact twoChainSmallCycle_condition U V n a b z ha hb)

@[simp]
theorem PeriodTorusHigherHomology.twoChainSmallCycle_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (twoChainSmallCycle U V n a b z ha hb).1 =
      ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) :=
  rfl

theorem PeriodTorusHigherHomology.twoChainSmallCycle_ambient_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (SingularMayerVietoris.ModuleHomology.mapCycles (SingularMayerVietoris.smallInclusion U V)
          (n + 1) (twoChainSmallCycle U V n a b z ha hb)).1 =
      SingularChains.inducedChain (SingularMayerVietoris.subtypeInclusion U) (n + 1) a +
        SingularChains.inducedChain (SingularMayerVietoris.subtypeInclusion V) (n + 1) b := by
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, twoChainSmallCycle_val,
    twoChainMiddle_rightMap, map_add]
  have hU :=
    congrArg (fun f => (f.f (n + 1)).hom a) (SingularMayerVietoris.toSmallLeft_inclusion U V)
  have hV :=
    congrArg (fun f => (f.f (n + 1)).hom b) (SingularMayerVietoris.toSmallRight_inclusion U V)
  exact congrArg₂ (· + ·) hU hV

theorem PeriodTorusHigherHomology.connectingHomomorphism_twoChain {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : SingularChains.Chains U (n + 1)) (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion U V) (n + 1)
            (twoChainSmallCycle U V n a b z ha hb))) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (U ∩ V : Set X)) n z :=
  connectingHomomorphism_cycleClass U V hU hV hcover n (twoChainSmallCycle U V n a b z ha hb)
    (twoChainMiddle U V n a b) rfl z (twoChainMiddle_boundary U V n a b z ha hb)


@[simp]
theorem PeriodTorusHigherHomology.circleProjection_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProjectionHomology X (n + 1) (positiveCircleCross X n b) = 0 :=
  crossProductHomology_snd n (SingularChains.loopHomologyClass CirclePaths.positiveLoop) b


def PeriodTorusHigherHomology.CirclePaths.quarterIntersection :
    ↥(CircleTopology.arcU ∩
        CircleTopology.arcV) :=
  CircleTopology.intersectionHomeomorph.symm
    (Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩)

def PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection :
    ↥(CircleTopology.arcU ∩
        CircleTopology.arcV) :=
  CircleTopology.intersectionHomeomorph.symm
    (Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩)

def PeriodTorusHigherHomology.CirclePaths.quarterPoint :
    (CircleTopology.Circle) :=
  quarterIntersection.val

def PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint :
    (CircleTopology.Circle) :=
  threeQuarterIntersection.val

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterPoint_coe :
    quarterPoint = ((1 / 4 : ℝ) : (CircleTopology.Circle)) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersection_component :
    CircleTopology.intersectionHomeomorph quarterIntersection =
      Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩ :=
  CircleTopology.intersectionHomeomorph.apply_symm_apply _

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection_component :
    CircleTopology.intersectionHomeomorph threeQuarterIntersection =
      Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩ :=
  CircleTopology.intersectionHomeomorph.apply_symm_apply _

def PeriodTorusHigherHomology.CirclePaths.quarterU :
    CircleTopology.arcU :=
  ⟨quarterPoint, quarterIntersection.property.1⟩

def PeriodTorusHigherHomology.CirclePaths.quarterV :
    CircleTopology.arcV :=
  ⟨quarterPoint, quarterIntersection.property.2⟩

def PeriodTorusHigherHomology.CirclePaths.threeQuarterU :
    CircleTopology.arcU :=
  ⟨threeQuarterPoint, threeQuarterIntersection.property.1⟩

def PeriodTorusHigherHomology.CirclePaths.threeQuarterV :
    CircleTopology.arcV :=
  ⟨threeQuarterPoint, threeQuarterIntersection.property.2⟩

def PeriodTorusHigherHomology.CirclePaths.uPath : Path quarterU threeQuarterU
    where
  toFun
    t :=
    CircleTopology.arcUHomeomorph.symm
      ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by
        have ht := t.property
        constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun :=
    CircleTopology.arcUHomeomorph.symm.continuous.comp
      ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
        (fun t => by
          change (1 / 4 : ℝ) + (t : ℝ) / 2 ∈ Set.Ioo (0 : ℝ) 1
          constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change
      (((1 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) :
          (CircleTopology.Circle)) =
        ((1 / 4 : ℝ) : (CircleTopology.Circle))
    norm_num
  target' := by
    apply Subtype.ext
    change
      (((1 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) :
          (CircleTopology.Circle)) =
        ((3 / 4 : ℝ) : (CircleTopology.Circle))
    norm_num

def PeriodTorusHigherHomology.CirclePaths.vPath : Path threeQuarterV quarterV
    where
  toFun
    t :=
    CircleTopology.arcVHomeomorph.symm
      ⟨(3 / 4 : ℝ) + (t : ℝ) / 2, by
        have ht := t.property
        constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun :=
    CircleTopology.arcVHomeomorph.symm.continuous.comp
      ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
        (fun t => by
          change (3 / 4 : ℝ) + (t : ℝ) / 2 ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2)
          constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change
      (((3 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) :
          (CircleTopology.Circle)) =
        ((3 / 4 : ℝ) : (CircleTopology.Circle))
    norm_num
  target' := by
    apply Subtype.ext
    change
      (((3 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) :
          (CircleTopology.Circle)) =
        ((1 / 4 : ℝ) : (CircleTopology.Circle))
    convert AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ) using 1
    norm_num

def PeriodTorusHigherHomology.CirclePaths.uCirclePath : Path quarterPoint threeQuarterPoint :=
  uPath.map continuous_subtype_val

def PeriodTorusHigherHomology.CirclePaths.vCirclePath : Path threeQuarterPoint quarterPoint :=
  vPath.map continuous_subtype_val

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.uCirclePath_apply (t : unitInterval) :
    uCirclePath t =
      (((1 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : (CircleTopology.Circle)) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.vCirclePath_apply (t : unitInterval) :
    vCirclePath t =
      (((3 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : (CircleTopology.Circle)) :=
  rfl

def PeriodTorusHigherHomology.CirclePaths.quarterLoop : Path quarterPoint quarterPoint
    where
  toFun t := (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (CircleTopology.Circle))
  continuous_toFun :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.add continuous_subtype_val)
  source' := by
    change
      (((1 / 4 : ℝ) + (0 : unitInterval) : ℝ) :
          (CircleTopology.Circle)) =
        _;
    simp
  target' := AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ)

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_apply (t : unitInterval) :
    quarterLoop t =
      (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (CircleTopology.Circle)) :=
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.uCirclePath_trans_vCirclePath :
    uCirclePath.trans vCirclePath = quarterLoop := by
  apply Path.ext
  funext t
  rw [Path.trans_apply]
  split_ifs <;> simp only [uCirclePath_apply, vCirclePath_apply, quarterLoop_apply]
  · congr 1
    ring
  · congr 1
    ring


@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterTranslation_zero :
    circleTranslation (1 / 4) (0 : (CircleTopology.Circle)) =
      quarterPoint := by simp only [circleTranslation_apply, add_zero, quarterPoint_coe]

theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_eq_translation :
    quarterLoop =
      (positiveLoop.map (circleTranslation (1 / 4)).continuous).cast quarterTranslation_zero.symm
        quarterTranslation_zero.symm := by
  apply Path.ext
  funext t
  change
    (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (CircleTopology.Circle)) =
      ((1 / 4 : ℝ) : (CircleTopology.Circle)) +
        ((t : ℝ) : (CircleTopology.Circle))
  exact AddCircle.coe_add (1 : ℝ) (1 / 4 : ℝ) (t : ℝ)

theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_homologyClass :
    SingularChains.loopHomologyClass quarterLoop = SingularChains.loopHomologyClass positiveLoop := by
  have hc :
    SingularChains.loopHomologyClass quarterLoop =
      SingularChains.loopHomologyClass (positiveLoop.map (circleTranslation (1 / 4)).continuous) :=
    by
    apply
      SingularChains.homologyToChainClass_injective
        (CircleTopology.Circle)
    rw [SingularChains.homologyToChainClass_loopHomologyClass,
      SingularChains.homologyToChainClass_loopHomologyClass, quarterLoop_eq_translation,
      SingularChains.pathClass_cast]
  exact hc.trans (loopHomologyClass_map_circleTranslation (1 / 4) positiveLoop)

theorem PeriodTorusHigherHomology.CirclePaths.boundaryOne_arcSum :
    SingularChains.boundaryOne (CircleTopology.Circle)
        (SingularChains.pathChain uCirclePath + SingularChains.pathChain vCirclePath) =
      0 := by
  rw [map_add, SingularChains.boundaryOne_pathChain, SingularChains.boundaryOne_pathChain]
  abel

def PeriodTorusHigherHomology.CirclePaths.arcSumCycle :
    SingularChains.Cycles1 (CircleTopology.Circle) :=
  SingularChains.mkCycle1 (CircleTopology.Circle)
    (SingularChains.pathChain uCirclePath + SingularChains.pathChain vCirclePath) boundaryOne_arcSum

theorem PeriodTorusHigherHomology.CirclePaths.arcSumCycle_class :
    SingularChains.cycleClass (CircleTopology.Circle) arcSumCycle =
      SingularChains.loopHomologyClass quarterLoop := by
  apply
    SingularChains.homologyToChainClass_injective (CircleTopology.Circle)
  rw [SingularChains.homologyToChainClass_cycleClass,
    SingularChains.homologyToChainClass_loopHomologyClass]
  change
    SingularChains.chainClass (CircleTopology.Circle)
        (SingularChains.pathChain uCirclePath + SingularChains.pathChain vCirclePath) =
      _
  rw [map_add, ← uCirclePath_trans_vCirclePath, SingularChains.pathClass_trans]
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.arcSumCycle_positiveLoop_class :
    SingularChains.cycleClass (CircleTopology.Circle) arcSumCycle =
      SingularChains.loopHomologyClass positiveLoop :=
  arcSumCycle_class.trans quarterLoop_homologyClass

def PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection (X : Type*)
    [TopologicalSpace X] :
    C(X,
      ↥(CircleTopology.productU X ∩
          CircleTopology.productV X)) :=
  ⟨fun x => ⟨(quarterPoint, x), quarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

def PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection (X : Type*)
    [TopologicalSpace X] :
    C(X,
      ↥(CircleTopology.productU X ∩
          CircleTopology.productV X)) :=
  ⟨fun x => ⟨(threeQuarterPoint, x), threeQuarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_component (X : Type*)
    [TopologicalSpace X] (x : X) :
    CircleTopology.productIntersectionHomotopyEquiv X
        (quarterIntersectionSection X x) =
      Sum.inl x := by
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib
          (CircleTopology.intersectionHomeomorph quarterIntersection,
            x)) =
      _
  rw [quarterIntersection_component]
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_comp (X : Type*)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionHomotopyEquiv X).toFun.comp
        (quarterIntersectionSection X) =
      ⟨Sum.inl, continuous_inl⟩ := by
  apply ContinuousMap.ext
  intro x
  exact quarterIntersectionSection_component X x

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_component
    (X : Type*) [TopologicalSpace X] (x : X) :
    CircleTopology.productIntersectionHomotopyEquiv X
        (threeQuarterIntersectionSection X x) =
      Sum.inr x := by
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib
          (CircleTopology.intersectionHomeomorph
              threeQuarterIntersection,
            x)) =
      _
  rw [threeQuarterIntersection_component]
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_comp (X : Type*)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionHomotopyEquiv X).toFun.comp
        (threeQuarterIntersectionSection X) =
      ⟨Sum.inr, continuous_inr⟩ := by
  apply ContinuousMap.ext
  intro x
  exact threeQuarterIntersectionSection_component X x


theorem PeriodTorusHigherHomology.positiveCircleCross_arcSum_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex ((CircleTopology.Circle) × X))
        (n + 1)
        (crossProductCycles (CircleTopology.Circle) X n
          CirclePaths.arcSumCycle b) := by
  have h :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (CircleTopology.Circle)) 1
        CirclePaths.arcSumCycle =
      SingularChains.loopHomologyClass CirclePaths.positiveLoop :=
    CirclePaths.arcSumCycle_positiveLoop_class
  change
    crossProductHomology (CircleTopology.Circle) X n
        (SingularChains.loopHomologyClass CirclePaths.positiveLoop)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) =
      _
  rw [← h]
  exact
    crossProductHomology_cycleClass (CircleTopology.Circle) X n
      CirclePaths.arcSumCycle b

theorem PeriodTorusHigherHomology.quarterIntersectionHomology_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.singularHomologyMap (CirclePaths.quarterIntersectionSection X) n
          a) =
      (a, 0) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CirclePaths.quarterIntersectionSection_comp]
  exact sumHomologyEquiv_inl X X n a

theorem PeriodTorusHigherHomology.threeQuarterIntersectionHomology_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.singularHomologyMap (CirclePaths.threeQuarterIntersectionSection X)
          n a) =
      (0, a) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CirclePaths.threeQuarterIntersectionSection_comp]
  exact sumHomologyEquiv_inr X X n a

def PeriodTorusHigherHomology.intersectionDifferenceCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularChains.singularComplex
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((CircleTopology.Circle) × X)))
      n :=
  SingularMayerVietoris.ModuleHomology.mapCycles
      (SingularChains.singularChainMap (CirclePaths.threeQuarterIntersectionSection X)) n b -
    SingularMayerVietoris.ModuleHomology.mapCycles
      (SingularChains.singularChainMap (CirclePaths.quarterIntersectionSection X)) n b

@[simp]
theorem PeriodTorusHigherHomology.intersectionDifferenceCycle_val (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    (intersectionDifferenceCycle X n b).1 =
      SingularChains.inducedChain (CirclePaths.threeQuarterIntersectionSection X) n b.1 -
        SingularChains.inducedChain (CirclePaths.quarterIntersectionSection X) n b.1 := by
  change
    (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularChains.singularChainMap (CirclePaths.threeQuarterIntersectionSection X)) n
            b).1 -
        (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularChains.singularChainMap (CirclePaths.quarterIntersectionSection X)) n b).1 =
      _
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val,
    SingularMayerVietoris.ModuleHomology.mapCycles_val]

theorem PeriodTorusHigherHomology.intersectionDifferenceCycle_class_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex
            (CircleTopology.productU X ∩ CircleTopology.productV X :
              Set ((CircleTopology.Circle) × X)))
          n (intersectionDifferenceCycle X n b)) =
      (-SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b,
        SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) := by
  rw [intersectionDifferenceCycle, map_sub, map_sub, ←
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, ←
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  change
    productIntersectionHomologyEquiv X n
          (SingularMayerVietoris.singularHomologyMap
            (CirclePaths.threeQuarterIntersectionSection X) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b)) -
        productIntersectionHomologyEquiv X n
          (SingularMayerVietoris.singularHomologyMap (CirclePaths.quarterIntersectionSection X) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b)) =
      _
  rw [threeQuarterIntersectionHomology_coordinates, quarterIntersectionHomology_coordinates]
  simp only [Prod.mk_sub_mk, zero_sub, sub_zero]

theorem PeriodTorusHigherHomology.quarterIntersectionSection_toU (X : Type) [TopologicalSpace X] :
    (CircleTopology.productIntersectionToU X).comp (CirclePaths.quarterIntersectionSection X) =
      ((CircleTopology.productUHomeomorph X).symm :
            C(CircleTopology.arcU × X, CircleTopology.productU X)).comp
        ((ContinuousMap.const X CirclePaths.quarterU).prodMk (ContinuousMap.id X)) :=
  rfl

theorem PeriodTorusHigherHomology.quarterIntersectionSection_toV (X : Type) [TopologicalSpace X] :
    (CircleTopology.productIntersectionToV X).comp (CirclePaths.quarterIntersectionSection X) =
      ((CircleTopology.productVHomeomorph X).symm :
            C(CircleTopology.arcV × X, CircleTopology.productV X)).comp
        ((ContinuousMap.const X CirclePaths.quarterV).prodMk (ContinuousMap.id X)) :=
  rfl

theorem PeriodTorusHigherHomology.threeQuarterIntersectionSection_toU (X : Type)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionToU X).comp
        (CirclePaths.threeQuarterIntersectionSection X) =
      ((CircleTopology.productUHomeomorph X).symm :
            C(CircleTopology.arcU × X, CircleTopology.productU X)).comp
        ((ContinuousMap.const X CirclePaths.threeQuarterU).prodMk (ContinuousMap.id X)) :=
  rfl

theorem PeriodTorusHigherHomology.threeQuarterIntersectionSection_toV (X : Type)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionToV X).comp
        (CirclePaths.threeQuarterIntersectionSection X) =
      ((CircleTopology.productVHomeomorph X).symm :
            C(CircleTopology.arcV × X, CircleTopology.productV X)).comp
        ((ContinuousMap.const X CirclePaths.threeQuarterV).prodMk (ContinuousMap.id X)) :=
  rfl


def PeriodTorusHigherHomology.uCrossChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.Chains (CircleTopology.productU X) (n + 1) :=
  SingularChains.inducedChain
    ((CircleTopology.productUHomeomorph X).symm :
      C(CircleTopology.arcU × X, CircleTopology.productU X))
    (n + 1)
    (crossProductEdge CircleTopology.arcU X n (SingularChains.pathChain CirclePaths.uPath) b.1)

def PeriodTorusHigherHomology.vCrossChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.Chains (CircleTopology.productV X) (n + 1) :=
  SingularChains.inducedChain
    ((CircleTopology.productVHomeomorph X).symm :
      C(CircleTopology.arcV × X, CircleTopology.productV X))
    (n + 1)
    (crossProductEdge CircleTopology.arcV X n (SingularChains.pathChain CirclePaths.vPath) b.1)

theorem PeriodTorusHigherHomology.uCrossChain_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    ((SingularChains.singularComplex (CircleTopology.productU X)).d (n + 1) n).hom
        (uCrossChain X n b) =
      SingularChains.inducedChain (CircleTopology.productIntersectionToU X) n
        (intersectionDifferenceCycle X n b).1 := by
  rw [uCrossChain, ← SingularChains.inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub]
  congr 1
  · have h :=
      congrArg (fun f => SingularChains.inducedChain f n b.1)
        (threeQuarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, SingularChains.inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h :=
      congrArg (fun f => SingularChains.inducedChain f n b.1) (quarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, SingularChains.inducedChain_comp,
      LinearMap.comp_apply] using h.symm

theorem PeriodTorusHigherHomology.vCrossChain_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    ((SingularChains.singularComplex (CircleTopology.productV X)).d (n + 1) n).hom
        (vCrossChain X n b) =
      -SingularChains.inducedChain (CircleTopology.productIntersectionToV X) n
          (intersectionDifferenceCycle X n b).1 := by
  rw [vCrossChain, ← SingularChains.inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub, neg_sub]
  congr 1
  · have h :=
      congrArg (fun f => SingularChains.inducedChain f n b.1) (quarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, SingularChains.inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h :=
      congrArg (fun f => SingularChains.inducedChain f n b.1)
        (threeQuarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, SingularChains.inducedChain_comp,
      LinearMap.comp_apply] using h.symm

theorem PeriodTorusHigherHomology.uCrossChain_inclusion (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.inducedChain (CircleTopology.productUInclusion X) (n + 1) (uCrossChain X n b) =
      crossProductEdge (CircleTopology.Circle) X n
        (SingularChains.pathChain CirclePaths.uCirclePath) b.1 := by
  have hi :
    (CircleTopology.productUInclusion X).comp
        ((CircleTopology.productUHomeomorph X).symm :
          C(CircleTopology.arcU × X, CircleTopology.productU X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
            C(CircleTopology.arcU, (CircleTopology.Circle))).prodMap
        (ContinuousMap.id X) :=
    rfl
  rw [uCrossChain, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp, hi,
    crossProductEdge_natural, SingularChains.inducedChain_id, LinearMap.id_apply,
    SingularChains.inducedChain_pathChain]
  rfl

theorem PeriodTorusHigherHomology.vCrossChain_inclusion (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.inducedChain (CircleTopology.productVInclusion X) (n + 1) (vCrossChain X n b) =
      crossProductEdge (CircleTopology.Circle) X n
        (SingularChains.pathChain CirclePaths.vCirclePath) b.1 := by
  have hi :
    (CircleTopology.productVInclusion X).comp
        ((CircleTopology.productVHomeomorph X).symm :
          C(CircleTopology.arcV × X, CircleTopology.productV X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
            C(CircleTopology.arcV, (CircleTopology.Circle))).prodMap
        (ContinuousMap.id X) :=
    rfl
  rw [vCrossChain, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp, hi,
    crossProductEdge_natural, SingularChains.inducedChain_id, LinearMap.id_apply,
    SingularChains.inducedChain_pathChain]
  rfl

theorem PeriodTorusHigherHomology.arcCrossChains_inclusion_sum (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.inducedChain (CircleTopology.productUInclusion X) (n + 1) (uCrossChain X n b) +
        SingularChains.inducedChain (CircleTopology.productVInclusion X) (n + 1)
          (vCrossChain X n b) =
      crossProductEdge (CircleTopology.Circle) X n
        (SingularChains.pathChain CirclePaths.uCirclePath +
          SingularChains.pathChain CirclePaths.vCirclePath)
        b.1 := by rw [uCrossChain_inclusion, vCrossChain_inclusion, map_add, LinearMap.add_apply]


def PeriodTorusHigherHomology.positiveCircleSmallCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularMayerVietoris.smallComplex (CircleTopology.productU X) (CircleTopology.productV X))
      (n + 1) :=
  twoChainSmallCycle (CircleTopology.productU X) (CircleTopology.productV X) n (uCrossChain X n b)
    (vCrossChain X n b) (intersectionDifferenceCycle X n b) (uCrossChain_boundary X n b)
    (vCrossChain_boundary X n b)

theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_val (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
            (CircleTopology.productV X))
          (n + 1) (positiveCircleSmallCycle X n b)).1 =
      crossProductEdge (CircleTopology.Circle) X n
        (SingularChains.pathChain CirclePaths.uCirclePath +
          SingularChains.pathChain CirclePaths.vCirclePath)
        b.1 :=
  (twoChainSmallCycle_ambient_val (CircleTopology.productU X) (CircleTopology.productV X) n
        (uCrossChain X n b) (vCrossChain X n b) (intersectionDifferenceCycle X n b)
        (uCrossChain_boundary X n b) (vCrossChain_boundary X n b)).trans
    (arcCrossChains_inclusion_sum X n b)

theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_eq (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
          (CircleTopology.productV X))
        (n + 1) (positiveCircleSmallCycle X n b) =
      crossProductCycles (CircleTopology.Circle) X n
        CirclePaths.arcSumCycle b := by
  apply Subtype.ext
  exact positiveCircleSmallCycle_ambient_val X n b

theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_class (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex ((CircleTopology.Circle) × X))
        (n + 1)
        (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
            (CircleTopology.productV X))
          (n + 1) (positiveCircleSmallCycle X n b)) =
      positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) :=
  by
  rw [positiveCircleSmallCycle_ambient_eq]
  exact (positiveCircleCross_arcSum_cycleClass X n b).symm

theorem PeriodTorusHigherHomology.circleConnecting_positiveCircleCross_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    circleMayerVietorisConnecting X n
        (positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
            b)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex
          (CircleTopology.productU X ∩ CircleTopology.productV X :
            Set ((CircleTopology.Circle) × X)))
        n (intersectionDifferenceCycle X n b) := by
  rw [← positiveCircleSmallCycle_ambient_class]
  exact
    connectingHomomorphism_twoChain (CircleTopology.productU X) (CircleTopology.productV X)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X) n (uCrossChain X n b) (vCrossChain X n b)
      (intersectionDifferenceCycle X n b) (uCrossChain_boundary X n b)
      (vCrossChain_boundary X n b)

theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross_cycleClass
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    circleBoundaryCoordinates X n
        (positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
            b)) =
      (-SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b,
        SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) := by
  change
    productIntersectionHomologyEquiv X n
        (circleMayerVietorisConnecting X n
          (positiveCircleCross X n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b))) =
      _
  rw [circleConnecting_positiveCircleCross_cycleClass]
  exact intersectionDifferenceCycle_class_coordinates X n b

theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundaryCoordinates X n (positiveCircleCross X n b) = (-b, b) := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) n
      b
  exact circleBoundaryCoordinates_positiveCircleCross_cycleClass X n c

@[simp]
theorem PeriodTorusHigherHomology.circleBoundary_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundary X n (positiveCircleCross X n b) = b := by
  rw [circleBoundary_apply, circleBoundaryCoordinates_positiveCircleCross]
  exact neg_neg b


@[simp]
theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProductHomologyEquiv X n (positiveCircleCross X n b) = (0, b) := by
  apply Prod.ext
  · exact circleProjection_positiveCircleCross X n b
  · exact circleBoundary_positiveCircleCross X n b

theorem PeriodTorusHigherHomology.positiveCircleCross_eq_symm (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    positiveCircleCross X n b = (circleProductHomologyEquiv X n).symm (0, b) := by
  apply (circleProductHomologyEquiv X n).injective
  rw [circleProductHomologyEquiv_positiveCircleCross, LinearEquiv.apply_symm_apply]

theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    (circleProductHomologyEquiv X n).symm a =
      circleSectionHomology X (n + 1) a.1 + positiveCircleCross X n a.2 := by
  apply (circleProductHomologyEquiv X n).injective
  rw [LinearEquiv.apply_symm_apply, map_add, circleProductHomologyEquiv_section,
    circleProductHomologyEquiv_positiveCircleCross]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem PeriodTorusHigherHomology.positiveCircleCross_naturality {X : Type} [TopologicalSpace X]
    {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        (positiveCircleCross X n b) =
      positiveCircleCross Y n (SingularMayerVietoris.singularHomologyMap f n b) := by
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
          ((circleProductHomologyEquiv X n).symm (0, b)) :=
      congrArg (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1))
        (positiveCircleCross_eq_symm X n b)
    _ =
        (circleProductHomologyEquiv Y n).symm
          (0, SingularMayerVietoris.singularHomologyMap f n b) := by
      simpa only [map_zero] using circleProductHomologyEquiv_symm_naturality f n (0, b)
    _ = _ :=
      (positiveCircleCross_eq_symm Y n (SingularMayerVietoris.singularHomologyMap f n b)).symm


end Mathoverflow1973

end
