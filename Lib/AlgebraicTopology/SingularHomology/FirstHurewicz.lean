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

## Main definitions and results

* `SingularChains.inverseHurewiczMap` : the inverse of the Hurewicz map, built from the
  edge-loop cochain of a family of base paths.
* `SingularChains.firstHurewiczEquiv` : `π₁(X, b)^{ab} ≃ₗ[ℤ] H₁(X)` for path-connected `X`.
* `SingularChains.loopHomologyClass_surjective` : every degree-one homology class of a
  path-connected space is the class of a loop.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 2A.1 (`H₁(X) ≅ π₁(X)^{ab}` for
  path-connected `X`)

## Tags

Hurewicz theorem, first homology, fundamental group
-/

open Set Function Filter Manifold Topology

noncomputable section

/-- The based loop class of the `i`-th edge path of a singular `2`-simplex agrees with the
based loop class of the path traced by the `i`-th face of that simplex. -/
theorem SingularChains.basedLoopClass_triangleFacePath {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath σ i) =
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r (simplexPath (σ.comp (simplexFace 1 i))) _ _

/-- The edge-loop cochain vanishes on the boundary of a singular `2`-simplex: the three edge
loops of a `2`-simplex compose to a nullhomotopic loop, so their classes cancel in
`π₁(X, b)^{ab}`. -/
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

/-- The edge-loop cochain kills the degree-two boundary map, hence is a cocycle. -/
theorem SingularChains.edgeLoopCochain_comp_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainMap_ext X 2
  intro σ
  exact edgeLoopCochain_boundaryTwo_simplex r σ

/-- The edge-loop cochain vanishes on every boundary of a two-chain. -/
theorem SingularChains.edgeLoopCochain_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Chains X 2) : edgeLoopCochain r (boundaryTwo X c) = 0 :=
  LinearMap.congr_fun (edgeLoopCochain_comp_boundaryTwo r) c

/-- The edge-loop cochain of a family `r` of paths from the base point descends, being a
cocycle, to a linear map `H₁(X) →ₗ[ℤ] π₁(X, b)^{ab}`.  It is inverse to the Hurewicz map
(Hatcher, Theorem 2A.1). -/
def SingularChains.inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : SingularH1 X →ₗ[ℤ] AbelianPi1 X b :=
  homologyDescOfChain X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r)

/-- On the class of a one-cycle, the inverse Hurewicz map is the edge-loop cochain of the
underlying chain. -/
@[simp]
theorem SingularChains.inverseHurewiczMap_cycleClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    inverseHurewiczMap r (cycleClass X c) = edgeLoopCochain r c.1 :=
  homologyDescOfChain_cycleClass X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r) c

/-- The inverse Hurewicz map sends the homology class of a loop at the base point to the
class of that loop in `π₁(X, b)^{ab}`. -/
@[simp]
theorem SingularChains.inverseHurewiczMap_loopHomologyClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    inverseHurewiczMap r (loopHomologyClass p) = loopClass p := by
  rw [loopHomologyClass, inverseHurewiczMap_cycleClass, loopCycle_val]
  exact edgeLoopCochain_loopSimplex r p

/-- The inverse Hurewicz map is a left inverse of the Hurewicz map. -/
theorem SingularChains.inverseHurewiczMap_hurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : AbelianPi1 X b) : inverseHurewiczMap r (hurewiczMap b a) = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczMap_loopClass, inverseHurewiczMap_loopHomologyClass]

/-- The inverse Hurewicz map is a right inverse of the Hurewicz map. -/
theorem SingularChains.hurewiczMap_inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : SingularH1 X) : hurewiczMap b (inverseHurewiczMap r a) = a := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X a
  apply homologyToChainClass_injective X
  rw [inverseHurewiczMap_cycleClass, homologyToChainClass_cycleClass]
  exact edgeClosure_cycle r c

/-- A family `r` of paths from the base point `b` to every point of `X` makes the Hurewicz
map `π₁(X, b)^{ab} →ₗ[ℤ] H₁(X)` a linear equivalence. -/
def SingularChains.firstHurewiczEquivOfPaths {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X
    where
  toLinearMap := hurewiczMap b
  invFun := inverseHurewiczMap r
  left_inv := inverseHurewiczMap_hurewiczMap r
  right_inv := hurewiczMap_inverseHurewiczMap r

/-- **The first Hurewicz theorem** (Hatcher, Theorem 2A.1): for a path-connected space `X`
the Hurewicz map is a linear equivalence `π₁(X, b)^{ab} ≃ₗ[ℤ] H₁(X)`. -/
def SingularChains.firstHurewiczEquiv {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X :=
  firstHurewiczEquivOfPaths (PathConnectedSpace.somePath b)

/-- The first Hurewicz equivalence sends the class of a loop in `π₁(X, b)^{ab}` to the
homology class of that loop. -/
@[simp]
theorem SingularChains.firstHurewiczEquiv_loopClass {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] (p : Path b b) :
    firstHurewiczEquiv b (loopClass p) = loopHomologyClass p :=
  hurewiczMap_loopClass b p

/-- On a path-connected space every degree-one singular homology class is the class of a
loop based at a fixed point. -/
theorem SingularChains.loopHomologyClass_surjective {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : Function.Surjective (loopHomologyClass (x := b)) := by
  intro a
  obtain ⟨c, hc⟩ := (firstHurewiczEquiv b).surjective a
  obtain ⟨p, hp⟩ := loopClass_surjective c
  refine ⟨p, ?_⟩
  rw [← firstHurewiczEquiv_loopClass, hp, hc]

/-- A presentation `e` of the fundamental group of a path-connected space `X` as a
multiplicative abelian group `Multiplicative A` transports the first Hurewicz equivalence to
a linear equivalence `H₁(X) ≃ₗ[ℤ] A`. -/
def SingularChains.singularH1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) : SingularH1 X ≃ₗ[ℤ] A :=
  (firstHurewiczEquiv b).symm.trans (abelianPi1EquivOfPi1 b e)

/-- The transported equivalence sends the homology class of a fundamental-group element `g`
to the image of `g` under the given presentation. -/
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

/-- The transported equivalence sends the homology class of a loop to the image of its
fundamental-group class under the given presentation. -/
@[simp]
theorem SingularChains.singularH1EquivOfPi1_loopHomologyClass {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (p : Path b b) :
    singularH1EquivOfPi1 b e (loopHomologyClass p) = (e (loopQuotient p)).toAdd :=
  singularH1EquivOfPi1_hurewiczFunction b e (loopQuotient p)

end
