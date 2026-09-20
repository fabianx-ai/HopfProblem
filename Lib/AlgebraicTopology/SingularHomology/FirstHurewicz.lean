/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension

/-!
# The first Hurewicz isomorphism

The edge-loop cochain of a family of base paths vanishes on boundaries, hence descends to an
inverse `inverseHurewiczMap` of the Hurewicz map `hurewiczMap : AbelianPi1 X b →ₗ[ℤ] SingularH1 X`.
For a path-connected space this gives the linear equivalence `firstHurewiczEquiv` between the
abelianised fundamental group and the first singular homology group, the surjectivity of
`loopHomologyClass`, and the transport `singularH1EquivOfPi1` along a presentation of the
fundamental group as a (multiplicative) abelian group.

The declarations live in the `SingularChains` namespace (the source used the `FirstHurewicz`
alias of that namespace).

## Tags

Hurewicz theorem, first homology, fundamental group
-/

open Set Function Filter Manifold Topology

universe u v

noncomputable section

theorem SingularChains.basedLoopClass_triangleFacePath {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath σ i) =
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r (simplexPath (σ.comp (simplexFace 1 i))) _ _

theorem SingularChains.edgeLoopCochain_boundaryTwo_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) :
    edgeLoopCochain r (boundaryTwo X (simplexChain X 2 σ)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeLoopCochain_simplex]
  change
    basedLoopClass r (simplexPath (σ.comp (simplexFace 1 0))) -
          basedLoopClass r (simplexPath (σ.comp (simplexFace 1 1))) +
        basedLoopClass r (simplexPath (σ.comp (simplexFace 1 2))) =
      0
  have he :=
    congrArg₂ (fun a c : AbelianPi1 X b => a + c)
      (congrArg₂ (fun a c : AbelianPi1 X b => a - c) (basedLoopClass_triangleFacePath r σ 0)
        (basedLoopClass_triangleFacePath r σ 1))
      (basedLoopClass_triangleFacePath r σ 2)
  exact
    he.symm.trans
      (basedLoopClass_triangle_boundary r (triangleEdge01 σ) (triangleEdge12 σ) (triangleEdge02 σ)
        (triangleEdges_homotopic σ))

theorem SingularChains.edgeLoopCochain_comp_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainMap_ext X 2
  intro σ
  exact edgeLoopCochain_boundaryTwo_simplex r σ

theorem SingularChains.edgeLoopCochain_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Chains X 2) : edgeLoopCochain r (boundaryTwo X c) = 0 :=
  LinearMap.congr_fun (edgeLoopCochain_comp_boundaryTwo r) c

def SingularChains.inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : SingularH1 X →ₗ[ℤ] AbelianPi1 X b :=
  homologyDescOfChain X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r)

@[simp]
theorem SingularChains.inverseHurewiczMap_cycleClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    inverseHurewiczMap r (cycleClass X c) = edgeLoopCochain r c.1 :=
  homologyDescOfChain_cycleClass X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r) c

@[simp]
theorem SingularChains.inverseHurewiczMap_loopHomologyClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    inverseHurewiczMap r (loopHomologyClass p) = loopClass p := by
  rw [loopHomologyClass, inverseHurewiczMap_cycleClass, loopCycle_val]
  exact edgeLoopCochain_loopSimplex r p

theorem SingularChains.inverseHurewiczMap_hurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : AbelianPi1 X b) : inverseHurewiczMap r (hurewiczMap b a) = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczMap_loopClass, inverseHurewiczMap_loopHomologyClass]

theorem SingularChains.hurewiczMap_inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : SingularH1 X) : hurewiczMap b (inverseHurewiczMap r a) = a := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X a
  apply homologyToChainClass_injective X
  rw [inverseHurewiczMap_cycleClass, homologyToChainClass_cycleClass]
  exact edgeClosure_cycle r c

def SingularChains.firstHurewiczEquivOfPaths {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X
    where
  toLinearMap := hurewiczMap b
  invFun := inverseHurewiczMap r
  left_inv := inverseHurewiczMap_hurewiczMap r
  right_inv := hurewiczMap_inverseHurewiczMap r

def SingularChains.firstHurewiczEquiv {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X :=
  firstHurewiczEquivOfPaths (PathConnectedSpace.somePath b)

@[simp]
theorem SingularChains.firstHurewiczEquiv_loopClass {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] (p : Path b b) :
    firstHurewiczEquiv b (loopClass p) = loopHomologyClass p :=
  hurewiczMap_loopClass b p

theorem SingularChains.loopHomologyClass_surjective {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : Function.Surjective (loopHomologyClass (x := b)) := by
  intro a
  obtain ⟨c, hc⟩ := (firstHurewiczEquiv b).surjective a
  obtain ⟨p, hp⟩ := loopClass_surjective c
  refine ⟨p, ?_⟩
  rw [← firstHurewiczEquiv_loopClass, hp, hc]

def SingularChains.singularH1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) : SingularH1 X ≃ₗ[ℤ] A :=
  (firstHurewiczEquiv b).symm.trans (abelianPi1EquivOfPi1 b e)

@[simp]
theorem SingularChains.singularH1EquivOfPi1_hurewiczFunction {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (g : FundamentalGroup X b) :
    singularH1EquivOfPi1 b e (hurewiczFunction b g) = (e g).toAdd := by
  change
    abelianPi1EquivOfPi1 b e
        ((firstHurewiczEquiv b).symm
          (firstHurewiczEquiv b (Additive.ofMul (Abelianization.of g)))) =
      _
  rw [LinearEquiv.symm_apply_apply, abelianPi1EquivOfPi1_of]

@[simp]
theorem SingularChains.singularH1EquivOfPi1_loopHomologyClass {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (p : Path b b) :
    singularH1EquivOfPi1 b e (loopHomologyClass p) = (e (loopQuotient p)).toAdd :=
  singularH1EquivOfPi1_hurewiczFunction b e (loopQuotient p)

end
