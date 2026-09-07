/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PLACEHOLDER (Fabian decides attribution)
-/
-- Reference copy of Mathlib PR fabianx-ai/mathlib4#4 (branch first-hurewicz-structure, commit 6a94f8af). Kept verbatim except for import paths.
module

public import Lib.AlgebraicTopology.Hurewicz.CycleClasses
public import Lib.AlgebraicTopology.Hurewicz.SimplexPaths
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The Hurewicz theorem in degree one

For a path-connected topological space `X` with basepoint `b`, singular first homology with
integer coefficients is the abelianization of the fundamental group:

* `AlgebraicTopology.Hurewicz.hurewiczEquiv` :
  `Additive (Abelianization (FundamentalGroup X b)) ≃ₗ[ℤ] SingularH1 X`.

The equivalence sends the class of a loop `p` to the homology class of the corresponding
singular one-simplex (`Hurewicz.loopHomologyClass`, see `hurewiczEquiv_loopClass`), and it is
natural in `X` (`SingularH1.map_loopHomologyClass`).

## Outline of the proof

This is the classical argument of [hatcher02], Theorem 2A.1, in five steps.

1. *Singular chains.*  A path `p` gives a singular one-simplex `pathSimplex p`, hence a
   one-chain `pathChain p`, which is a cycle when `p` is a loop (`loopCycle`). We use the
   concrete cycle interface of `Mathlib/AlgebraicTopology/Hurewicz/CycleClasses.lean` to speak
   about `H₁` through explicit cycles.
2. *Homotopies and concatenations are boundaries.*  Cutting the square of a path homotopy
   along its diagonal, and reparametrizing a concatenation over a triangle, produce explicit
   two-chains whose boundaries show: homotopic paths have equal classes modulo boundaries, and
   the class of `p.trans q` is the sum of the classes (`pathClass_homotopic`,
   `pathClass_trans`).
3. *The Hurewicz homomorphism.*  Step 2 makes `p ↦ loopHomologyClass p` a homomorphism from
   the fundamental group to the abelian group `H₁`, so it factors through the abelianization:
   `hurewiczHom : Additive (Abelianization (FundamentalGroup X b)) →ₗ[ℤ] SingularH1 X`.
4. *The inverse.*  Fix a path `r x` from the basepoint to each point of `X`. Every singular
   one-simplex `σ` becomes a loop `r (σ 0) · σ · (r (σ 1))⁻¹`, giving a map from one-chains to
   the abelianized fundamental group (`edgeLoopCochain`). The boundary of a singular
   two-simplex maps to zero because its three edges compose up to homotopy inside the simply
   connected 2-simplex (`triangleEdges_homotopic`), so the map descends to `H₁`
   (`inverseHurewiczHom`).
5. *The two maps are inverse.*  One composite is checked on loops; the other by computing the
   class of an arbitrary cycle modulo boundaries (`edgeClosure_cycle`), using that homology
   injects into one-chains modulo boundaries.

## Main definitions and results

* `AlgebraicTopology.SingularH1` : singular first homology with `ℤ` coefficients, with
  functorial action `SingularH1.map`.
* `AlgebraicTopology.Hurewicz.loopHomologyClass` : the homology class of a loop, with
  `loopHomologyClass_homotopic`, `loopHomologyClass_refl`, `loopHomologyClass_trans`,
  `loopHomologyClass_surjective`, and conjugation invariance `loopHomologyClass_conjugate`.
* `AlgebraicTopology.Hurewicz.hurewiczHom` : the Hurewicz homomorphism, defined for any
  basepoint of any space.
* `AlgebraicTopology.Hurewicz.hurewiczEquiv` : the Hurewicz isomorphism for a path-connected
  space.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 2A.1

## Tags

Hurewicz, singular homology, fundamental group, abelianization
-/

open Set Function Topology
open scoped CategoryTheory ContinuousMap

@[expose] public noncomputable section

namespace AlgebraicTopology
/-! ### Singular chains and singular first homology -/

namespace Hurewicz

/-- The singular chain complex of a topological space with integer coefficients: the chain
complex of its singular simplicial set. -/
abbrev singularComplex (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)

/-- The `n`-chains of the singular chain complex of `X`. -/
abbrev Chains (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (singularComplex X).X n

end Hurewicz

/-- The singular first homology of a topological space with integer coefficients, as a
`ℤ`-module.  Definitionally this is the singular homology functor
`AlgebraicTopology.singularHomologyFunctor` in degree one, evaluated at `ℤ` and `X`
(see `SingularH1.map_eq_singularHomologyFunctor_map`). -/
abbrev SingularH1 (X : Type) [TopologicalSpace X] :=
  ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)).homology 1

namespace Hurewicz

variable (X : Type) [TopologicalSpace X]

/-- A singular `n`-simplex of `X`: a continuous map from the standard `n`-simplex. -/
abbrev SingularSimplex (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X)

/-- A singular `n`-simplex, as an `n`-simplex of the singular simplicial set of `X`. -/
def simplexIndex (n : ℕ) (σ : SingularSimplex X n) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n))) :=
  ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n)))).symm σ

/-- The one-generator chain attached to a singular `n`-simplex. -/
def simplexChain (n : ℕ) (σ : SingularSimplex X n) : Chains X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) (simplexIndex X n σ)) 1

/-- The boundary map from one-chains to zero-chains. -/
abbrev boundaryOne : Chains X 1 →ₗ[ℤ] Chains X 0 :=
  (singularComplex X).d 1 0 |>.hom

/-- The boundary map from two-chains to one-chains. -/
abbrev boundaryTwo : Chains X 2 →ₗ[ℤ] Chains X 1 :=
  (singularComplex X).d 2 1 |>.hom

private theorem simplexIndex_face (n : ℕ) (σ : SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplexIndex X (n + 1) σ) =
      simplexIndex X n (σ.comp (simplexFace n i)) := by rfl

/-- The boundary of the chain of a singular simplex is the alternating sum of the chains of
its faces. -/
theorem boundary_simplex (n : ℕ) (σ : SingularSimplex X (n + 1)) :
    (singularComplex X).d (n + 1) n (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexChain X n (σ.comp (simplexFace n i)) := by
  have h :=
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d (R := ModuleCat.of ℤ ℤ)
      (simplexIndex X (n + 1) σ)
  let ev : (ModuleCat.of ℤ ℤ ⟶ Chains X n) →+ Chains X n :=
    { toFun := fun f ↦ f.hom 1
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have he := congrArg ev h
  rw [map_sum] at he
  simp only [map_zsmul, simplexIndex_face] at he
  exact he

/-- The boundary of a singular one-simplex: second vertex minus first vertex. -/
theorem boundaryOne_simplex (σ : SingularSimplex X 1) :
    boundaryOne X (simplexChain X 1 σ) =
      simplexChain X 0 (σ.comp (simplexFace 0 0)) -
        simplexChain X 0 (σ.comp (simplexFace 0 1)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg] using boundary_simplex X 0 σ

/-- The boundary of a singular two-simplex: the alternating sum of its three edges. -/
theorem boundaryTwo_simplex (σ : SingularSimplex X 2) :
    boundaryTwo X (simplexChain X 2 σ) =
      simplexChain X 1 (σ.comp (simplexFace 1 0)) - simplexChain X 1 (σ.comp (simplexFace 1 1)) +
        simplexChain X 1 (σ.comp (simplexFace 1 2)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using boundary_simplex X 1 σ

/-- Extend a function on singular `n`-simplices to a linear map on `n`-chains: the chains are
free on the simplices. -/
def chainLift (n : ℕ) {M : Type} [AddCommGroup M]
    [Module ℤ M] (f : SingularSimplex X n → M) : Chains X n →ₗ[ℤ] M :=
  (CategoryTheory.Limits.Sigma.desc
        (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n))) =>
          ModuleCat.ofHom
            (LinearMap.toSpanSingleton ℤ M
              (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) s)))) :
      Chains X n ⟶ ModuleCat.of ℤ M).hom

/-- `chainLift` extends the given function: on the chain of a simplex it returns the value on
that simplex. -/
@[simp]
theorem chainLift_simplex (n : ℕ) {M : Type}
    [AddCommGroup M] [Module ℤ M] (f : SingularSimplex X n → M) (σ : SingularSimplex X n) :
    chainLift X n f (simplexChain X n σ) = f σ := by
  have h :=
    CategoryTheory.Limits.Sigma.ι_desc
      (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n))) =>
        ModuleCat.ofHom
          (LinearMap.toSpanSingleton ℤ M
            (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) s))))
      (simplexIndex X n σ)
  have he := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M => g.hom 1) h
  change
    chainLift X n f (simplexChain X n σ) =
      (LinearMap.toSpanSingleton ℤ M
          (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) (simplexIndex X n σ))))
        1 at he
  simpa only [LinearMap.toSpanSingleton_apply_one, simplexIndex, Equiv.apply_symm_apply] using he

/-- Two linear maps on `n`-chains agree once they agree on the chains of singular
simplices. -/
theorem chainMap_ext (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M] {f g : Chains X n →ₗ[ℤ] M}
    (h : ∀ σ : SingularSimplex X n, f (simplexChain X n σ) = g (simplexChain X n σ)) : f = g := by
  have hcat : (ModuleCat.ofHom f : Chains X n ⟶ ModuleCat.of ℤ M) = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change
      f (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) =
        g (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
    have hs := h ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk (n))) s)
    simpa only [simplexChain, simplexIndex, Equiv.symm_apply_apply] using hs
  exact congrArg ModuleCat.Hom.hom hcat

/-! ### One-cycles and their homology classes

We specialize the concrete cycle interface of `CycleClasses.lean` to the singular chain
complex. `homologyToChainClass` injects `H₁` into one-chains modulo boundaries: two homology
classes are equal as soon as their representing cycles differ by an explicit boundary. -/

/-- The one-cycles of the singular chain complex of `X`. -/
abbrev Cycles1 :=
  ChainHomology.Cycle1 (singularComplex X)

/-- Pin the `ℤ`-module structure on one-cycles to the submodule instance: for `ℤ`, instance
search would otherwise find `AddCommGroup.toIntModule`, a defeq but syntactically different
route that the module system cannot reconcile across non-exposed definitions. -/
instance cycles1Module : Module ℤ (Cycles1 X) :=
  (LinearMap.ker ((singularComplex X).sc 1).g.hom).module

/-- The underlying one-chain of a one-cycle. -/
def cycleVal : Cycles1 X →ₗ[ℤ] Chains X 1 :=
  (LinearMap.ker ((singularComplex X).sc 1).g.hom).subtype

/-- Build a one-cycle from a one-chain with vanishing boundary. -/
def mkCycle1 (c : Chains X 1) (hc : boundaryOne X c = 0) : Cycles1 X :=
  ChainHomology.mkCycle1 (singularComplex X) c hc

/-- The underlying one-chain of a one-cycle has vanishing boundary. -/
theorem cycles1_boundary (c : Cycles1 X) : boundaryOne X c.1 = 0 := by
  have hc := c.2
  change ((singularComplex X).d 1 ((ComplexShape.down ℕ).next 1)).hom c.1 = 0 at hc
  have hn : (ComplexShape.down ℕ).next 1 = 0 := (ComplexShape.down ℕ).next_eq' (by simp)
  rw [hn] at hc
  exact hc

/-- The homology class of a singular one-cycle. -/
abbrev cycleClass : Cycles1 X →ₗ[ℤ] SingularH1 X :=
  (ChainHomology.cycleClass (singularComplex X)).hom

/-- Every singular first-homology class is the class of a one-cycle. -/
theorem cycleClass_surjective : Function.Surjective (cycleClass X) :=
  ChainHomology.cycleClass_surjective (singularComplex X)

/-- The boundary of a two-chain, as a one-cycle. -/
def boundaryCycle (b : Chains X 2) : Cycles1 X :=
  ChainHomology.boundaryCycle1 (singularComplex X) b

/-- The singular one-chains of `X` modulo boundaries of two-chains. -/
abbrev Opchains :=
  ChainHomology.Opchains (singularComplex X)

/-- The class of a singular one-chain modulo boundaries. -/
abbrev chainClass : Chains X 1 →ₗ[ℤ] Opchains X :=
  (ChainHomology.chainClass (singularComplex X)).hom

/-- Boundaries of two-chains vanish modulo boundaries. -/
theorem chainClass_boundary (b : Chains X 2) : chainClass X (boundaryTwo X b) = 0 :=
  ChainHomology.chainClass_boundary (singularComplex X) b

/-- Two one-chains agree modulo boundaries exactly when their difference is a boundary. -/
theorem chainClass_eq_iff (x y : Chains X 1) :
    chainClass X x = chainClass X y ↔ ∃ b : Chains X 2, boundaryTwo X b = x - y :=
  ChainHomology.chainClass_eq_iff (singularComplex X) x y

/-- The canonical injection of singular first homology into one-chains modulo boundaries. -/
abbrev homologyToChainClass : SingularH1 X →ₗ[ℤ] Opchains X :=
  (ChainHomology.homologyToChainClass (singularComplex X)).hom

/-- Singular first homology injects into one-chains modulo boundaries. -/
theorem homologyToChainClass_injective : Function.Injective (homologyToChainClass X) :=
  ChainHomology.homologyToChainClass_injective (singularComplex X)

/-- The injection into chains modulo boundaries sends the class of a cycle to the class of
its underlying one-chain. -/
theorem homologyToChainClass_cycleClass
    (c : Cycles1 X) : homologyToChainClass X (cycleClass X c) = chainClass X c.1 :=
  ChainHomology.homologyToChainClass_cycleClass (singularComplex X) c

/-- A linear map on one-cycles that kills boundaries descends to `H₁`. -/
def homologyDesc {M : Type} [AddCommGroup M]
    [Module ℤ M] (f : Cycles1 X →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryCycle X b) = 0) :
    SingularH1 X →ₗ[ℤ] M :=
  ChainHomology.homologyDesc (singularComplex X) f hf

/-- The map descended to homology agrees with the given map on classes of cycles. -/
@[simp]
theorem homologyDesc_cycleClass {M : Type} [AddCommGroup M] [Module ℤ M] (f : Cycles1 X →ₗ[ℤ] M)
    (hf : ∀ b : Chains X 2, f (boundaryCycle X b) = 0) (c : Cycles1 X) :
    homologyDesc X f hf (cycleClass X c) = f c :=
  ChainHomology.homologyDesc_cycleClass (singularComplex X) f hf c

/-- A linear map on all one-chains that kills boundaries descends to `H₁`. -/
def homologyDescOfChain {M : Type} [AddCommGroup M]
    [Module ℤ M] (f : Chains X 1 →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryTwo X b) = 0) :
    SingularH1 X →ₗ[ℤ] M :=
  homologyDesc X (f.comp (cycleVal X)) hf

/-- The map descended from all one-chains agrees with the given map on classes of cycles. -/
@[simp]
theorem homologyDescOfChain_cycleClass {M : Type}
    [AddCommGroup M] [Module ℤ M] (f : Chains X 1 →ₗ[ℤ] M)
    (hf : ∀ b : Chains X 2, f (boundaryTwo X b) = 0) (c : Cycles1 X) :
    homologyDescOfChain X f hf (cycleClass X c) = f c.1 :=
  homologyDesc_cycleClass X (f.comp (cycleVal X)) hf c

/-! ### Functoriality -/

/-- The map of singular chain complexes induced by a continuous map. -/
abbrev singularChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : singularComplex X ⟶ singularComplex Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)

/-- The map on singular `n`-chains induced by a continuous map. -/
abbrev inducedChain {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : Chains X n →ₗ[ℤ] Chains Y n :=
  ((singularChainMap f).f n).hom

end Hurewicz

/-- The map on singular first homology induced by a continuous map. -/
abbrev SingularH1.map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : SingularH1 X →ₗ[ℤ] SingularH1 Y :=
  (HomologicalComplex.homologyMap
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) 1).hom

/-- The identity map induces the identity on singular first homology. -/
@[simp]
theorem SingularH1.map_id {X : Type} [TopologicalSpace X] :
    SingularH1.map (ContinuousMap.id X) = LinearMap.id := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map_id
      (TopCat.of X)
  exact congrArg ModuleCat.Hom.hom h

/-- `SingularH1.map` is the action of the singular homology functor in degree one. -/
theorem SingularH1.map_eq_singularHomologyFunctor_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    SingularH1.map f =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).hom :=
  rfl

/-- Composition of continuous maps induces composition on singular first homology. -/
theorem SingularH1.map_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    SingularH1.map (g.comp f) = (SingularH1.map g).comp (SingularH1.map f) := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg ModuleCat.Hom.hom h

namespace Hurewicz

/-- The induced map on chains sends the chain of a simplex to the chain of the composed
simplex. -/
@[simp]
theorem inducedChain_simplex {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (σ : SingularSimplex X n) :
    inducedChain f n (simplexChain X n σ) = simplexChain Y n (f.comp σ) := by
  have h :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) (simplexIndex X n σ)
  have he := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ Chains Y n => g.hom 1) h
  change inducedChain f n (simplexChain X n σ) = simplexChain Y n (f.comp σ) at he
  exact he

/-- The induced map on chains commutes with the boundary maps. -/
theorem inducedChain_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (i j : ℕ) (c : Chains X i) :
    inducedChain f j (((singularComplex X).d i j).hom c) =
      ((singularComplex Y).d i j).hom (inducedChain f i c) :=
  congrArg (fun g : Chains X i ⟶ Chains Y j => g.hom c) ((singularChainMap f).comm i j).symm

/-- The identity map induces the identity on chains. -/
@[simp]
theorem inducedChain_id {X : Type} [TopologicalSpace X] (n : ℕ) :
    inducedChain (ContinuousMap.id X) n = LinearMap.id := by
  apply chainMap_ext X n
  intro σ
  simp only [inducedChain_simplex, LinearMap.id_apply]
  rfl

/-- Composition of continuous maps induces composition of chain maps. -/
theorem inducedChain_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    inducedChain (g.comp f) n = (inducedChain g n).comp (inducedChain f n) := by
  apply chainMap_ext X n
  intro σ
  simp only [LinearMap.comp_apply, inducedChain_simplex]
  rfl

/-- The map on one-cycles induced by a continuous map. -/
def inducedCycles {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Cycles1 X →ₗ[ℤ] Cycles1 Y :=
  (ChainHomology.mapCycles (singularChainMap f)).hom

/-- The induced map on cycles acts on underlying chains as the induced chain map. -/
@[simp]
theorem inducedCycles_val {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (c : Cycles1 X) : (inducedCycles f c).1 = inducedChain f 1 c.1 :=
  ChainHomology.mapCycles_val (singularChainMap f) c

end Hurewicz

/-- The induced map on homology sends the class of a cycle to the class of its image. -/
@[simp]
theorem SingularH1.map_cycleClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : Hurewicz.Cycles1 X) :
    SingularH1.map f (Hurewicz.cycleClass X c) =
      Hurewicz.cycleClass Y (Hurewicz.inducedCycles f c) :=
  Hurewicz.ChainHomology.homologyMap_cycleClass (Hurewicz.singularChainMap f) c

/-! ### The chains of points, paths, and homotopies

The boundary of the concatenation triangle and of the two homotopy half-squares are computed
here. A wrinkle from step 2 of the proof: the homotopy square contributes the constant
edges at the two endpoints, which are themselves boundaries of constant triangles
(`correctedHomotopyChain`). -/

namespace Hurewicz

variable {X : Type} [TopologicalSpace X]

/-- The zero-chain attached to a point. -/
def pointChain (x : X) : Chains X 0 :=
  simplexChain X 0 (ContinuousMap.const (Simplex 0) x)

/-- The one-chain attached to a path. -/
def pathChain {x y : X} (p : Path x y) : Chains X 1 :=
  simplexChain X 1 (pathSimplex p)

/-- The boundary of a path's one-chain: endpoint minus starting point. -/
theorem boundaryOne_pathChain {x y : X}
    (p : Path x y) : boundaryOne X (pathChain p) = pointChain y - pointChain x := by
  rw [pathChain, boundaryOne_simplex, pathSimplex_face_zero, pathSimplex_face_one]
  rfl

/-- The one-chain of a loop is a cycle. -/
theorem boundaryOne_loop {x : X} (p : Path x x) :
    boundaryOne X (pathChain p) = 0 := by rw [boundaryOne_pathChain, sub_self]

/-- The two-chain of the concatenation triangle of two composable paths. -/
def concatChain {x y z : X} (p : Path x y) (q : Path y z) : Chains X 2 :=
  simplexChain X 2 (concatSimplex p q)

/-- The boundary of the concatenation triangle: `q - p.trans q + p` on chains. -/
theorem boundaryTwo_concatChain {x y z : X} (p : Path x y) (q : Path y z) :
    boundaryTwo X (concatChain p q) = pathChain q - pathChain (p.trans q) + pathChain p := by
  rw [concatChain, boundaryTwo_simplex, concatSimplex_face_zero, concatSimplex_face_one,
    concatSimplex_face_two]
  rfl

/-- The one-chain of the constant edge at a point. -/
def constantEdgeChain (x : X) : Chains X 1 :=
  simplexChain X 1 (ContinuousMap.const (Simplex 1) x)

/-- The two-chain of the constant triangle at a point. -/
def constantTriangleChain (x : X) : Chains X 2 :=
  simplexChain X 2 (ContinuousMap.const (Simplex 2) x)

/-- The boundary of the constant triangle is the constant edge. -/
theorem boundaryTwo_constantTriangleChain (x : X) :
    boundaryTwo X (constantTriangleChain x) = constantEdgeChain x := by
  rw [constantTriangleChain, boundaryTwo_simplex]
  change constantEdgeChain x - constantEdgeChain x + constantEdgeChain x = _
  abel

/-- The chain of the constant path is the constant edge chain. -/
@[simp]
theorem pathChain_refl (x : X) : pathChain (Path.refl x) = constantEdgeChain x :=
  rfl

/-- The two-chain of a path homotopy: lower triangle minus upper triangle of its square. -/
def homotopyChain {x y : X} {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  simplexChain X 2 (homotopyLowerSimplex H) - simplexChain X 2 (homotopyUpperSimplex H)

/-- The boundary of the homotopy two-chain: the two paths' difference, corrected by the
constant edges at the endpoints. -/
theorem boundaryTwo_homotopyChain {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) =
      pathChain p - pathChain q + constantEdgeChain y - constantEdgeChain x := by
  rw [homotopyChain, map_sub, boundaryTwo_simplex, boundaryTwo_simplex,
    homotopyLowerSimplex_face_zero, homotopyLowerSimplex_face_one, homotopyLowerSimplex_face_two,
    homotopyUpperSimplex_face_zero, homotopyUpperSimplex_face_one, homotopyUpperSimplex_face_two]
  change
    constantEdgeChain y - simplexChain X 1 (homotopyDiagonalSimplex H) + pathChain p -
        (pathChain q - simplexChain X 1 (homotopyDiagonalSimplex H) + constantEdgeChain x) =
      _
  abel

/-- The homotopy two-chain, corrected by constant triangles so that its boundary is exactly
the difference of the two paths. -/
def correctedHomotopyChain {x y : X} {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  homotopyChain H - constantTriangleChain y + constantTriangleChain x

/-- Homotopic paths differ by an explicit boundary. -/
theorem boundaryTwo_correctedHomotopyChain {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (correctedHomotopyChain H) = pathChain p - pathChain q := by
  rw [correctedHomotopyChain, map_add, map_sub, boundaryTwo_homotopyChain,
    boundaryTwo_constantTriangleChain, boundaryTwo_constantTriangleChain]
  abel

/-! ### Loops in the abelianized fundamental group

Besides the class of a loop at the basepoint, we need the class of an arbitrary path closed
up through a chosen system of paths `r` from the basepoint (`basedLoopClass`): the loops
that the inverse Hurewicz map attaches to singular one-simplices. The key computation is
`basedLoopClass_triangle`: closed-up edges of a triangle add up correctly. -/

/-- The abelianized fundamental group of `X` at `b`, written additively. This is the source
of the Hurewicz homomorphism. -/
abbrev AbelianPi1 (X : Type*) [TopologicalSpace X] (b : X) :=
  Additive (Abelianization (FundamentalGroup X b))

/-- The class of a loop in the abelianized fundamental group. -/
def loopClass {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) : AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath ⟦p⟧))

/-- Every element of the abelianized fundamental group is the class of a loop. -/
theorem loopClass_surjective {X : Type*} [TopologicalSpace X] {b : X} :
    Function.Surjective (loopClass (b := b)) := by
  intro a
  obtain ⟨g, hg⟩ := Quotient.exists_rep a.toMul
  change Abelianization.of g = a.toMul at hg
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g
  have hp' : FundamentalGroup.fromPath ⟦p⟧ = g := hp
  refine ⟨p, ?_⟩
  rw [loopClass, hp', hg]
  rfl

private theorem mk_trans {X : Type*} [TopologicalSpace X] {b : X} (p q : Path b b) :
    FundamentalGroup.fromPath ⟦p.trans q⟧ =
      FundamentalGroup.fromPath ⟦q⟧ * FundamentalGroup.fromPath ⟦p⟧ :=
  rfl

private theorem mk_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    FundamentalGroup.fromPath ⟦p.symm⟧ = (FundamentalGroup.fromPath ⟦p⟧)⁻¹ :=
  rfl

/-- Homotopic loops have the same class in the abelianized fundamental group. -/
theorem loopClass_homotopic {X : Type*} [TopologicalSpace X] {b : X}
    {p q : Path b b} (h : p.Homotopic q) : loopClass p = loopClass q :=
  congrArg (fun g : FundamentalGroup X b => Additive.ofMul (Abelianization.of g))
    (Path.Homotopic.Quotient.eq.mpr h)

/-- The class of a concatenation of loops is the sum of the classes. -/
theorem loopClass_trans {X : Type*} [TopologicalSpace X] {b : X} (p q : Path b b) :
    loopClass (p.trans q) = loopClass p + loopClass q := by
  rw [loopClass, mk_trans, map_mul, ofMul_mul, add_comm]
  rfl

/-- The class of a reversed loop is the negative of the class. -/
@[simp]
theorem loopClass_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopClass p.symm = -loopClass p := by
  rw [loopClass, mk_symm, map_inv, ofMul_inv]
  rfl

/-- Close up a path into a loop at the basepoint, using a chosen system of paths `r` from the
basepoint to every point: the loop `(r x).trans (p.trans (r y).symm)`. -/
def basedLoop {X : Type*} [TopologicalSpace X] {b x y : X} (r : ∀ x : X, Path b x)
    (p : Path x y) : Path b b :=
  (r x).trans (p.trans (r y).symm)

/-- The closed-up element of the fundamental group of a path-homotopy class: conjugation to
the basepoint at the level of `Path.Homotopic.Quotient`, where the groupoid simp lemmas prove
its laws. -/
def basedLoopQuotient {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (P : Path.Homotopic.Quotient x y) : FundamentalGroup X b :=
  FundamentalGroup.fromPath
    ((Path.Homotopic.Quotient.mk (r x)).trans
      (P.trans (Path.Homotopic.Quotient.mk (r y)).symm))

@[simp]
theorem basedLoopQuotient_mk {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopQuotient r (Path.Homotopic.Quotient.mk p) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedLoop r p)) := by
  simp [basedLoopQuotient, basedLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]

/-- The class in the abelianized fundamental group of a path closed up at the basepoint.
This is the value of the inverse Hurewicz map on the corresponding singular one-simplex. -/
def basedLoopClass {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (basedLoopQuotient r (Path.Homotopic.Quotient.mk p)))

/-- The closed-up class of a path is the class of the closed-up loop. -/
theorem basedLoopClass_def {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r p = loopClass (basedLoop r p) := by
  rw [basedLoopClass, basedLoopQuotient_mk]
  rfl

/-- Homotopic paths have equal closed-up classes: the class only sees the path-homotopy
class of its argument. -/
theorem basedLoopClass_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    basedLoopClass r p = basedLoopClass r q :=
  congrArg (fun P ↦ Additive.ofMul (Abelianization.of (basedLoopQuotient r P)))
    (Path.Homotopic.Quotient.eq.mpr h)

private theorem basedLoopQuotient_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (P : Path.Homotopic.Quotient x y)
    (Q : Path.Homotopic.Quotient y z) :
    basedLoopQuotient r (P.trans Q) = basedLoopQuotient r Q * basedLoopQuotient r P := by
  simp only [basedLoopQuotient, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (r y)).symm
      (Path.Homotopic.Quotient.mk (r y)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The closed-up class of a concatenation is the sum of the closed-up classes. -/
theorem basedLoopClass_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p : Path x y) (q : Path y z) :
    basedLoopClass r (p.trans q) = basedLoopClass r p + basedLoopClass r q := by
  rw [basedLoopClass, Path.Homotopic.Quotient.mk_trans, basedLoopQuotient_trans, map_mul,
    ofMul_mul, add_comm]
  rfl

/-- Closing up a loop at the basepoint recovers its own class. -/
@[simp]
theorem basedLoopClass_loop {X : Type*} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) : basedLoopClass r p = loopClass p := by
  rw [basedLoopClass_def, basedLoop, loopClass_trans, loopClass_trans, loopClass_symm]
  abel

/-- Closed-up classes add along a homotopy-commuting triangle of paths. -/
theorem basedLoopClass_triangle {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₀₁ + basedLoopClass r p₁₂ = basedLoopClass r p₀₂ := by
  rw [← basedLoopClass_trans]
  exact basedLoopClass_homotopic r h

/-- The alternating sum of closed-up classes along a homotopy-commuting triangle vanishes,
in the orientation matching the boundary of a two-simplex. -/
theorem basedLoopClass_triangle_boundary {X : Type*} [TopologicalSpace X]
    {b x y z : X} (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₁₂ - basedLoopClass r p₀₂ + basedLoopClass r p₀₁ = 0 := by
  rw [← basedLoopClass_triangle r p₀₁ p₁₂ p₀₂ h]
  abel

/-! ### The class of a path modulo boundaries

`pathClass p` is the image of `pathChain p` in one-chains modulo boundaries. By the
two-chains of the previous sections it is homotopy invariant and additive under
concatenation. This is the computational engine for both directions of the theorem. -/

/-- The class of a path in one-chains modulo boundaries. -/
def pathClass {x y : X} (p : Path x y) : Opchains X :=
  chainClass X (pathChain p)

/-- A path homotopy makes the path classes modulo boundaries equal. -/
theorem pathClass_homotopy {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : pathClass p = pathClass q :=
  (chainClass_eq_iff X _ _).mpr ⟨correctedHomotopyChain H, boundaryTwo_correctedHomotopyChain H⟩

/-- Homotopic paths have the same class modulo boundaries. -/
theorem pathClass_homotopic {x y : X}
    {p q : Path x y} (h : p.Homotopic q) : pathClass p = pathClass q := by
  obtain ⟨H⟩ := h
  exact pathClass_homotopy H

/-- The constant path has class zero modulo boundaries. -/
@[simp]
theorem pathClass_refl (x : X) : pathClass (Path.refl x) = 0 := by
  change chainClass X (pathChain (Path.refl x)) = 0
  rw [pathChain_refl, ← boundaryTwo_constantTriangleChain]
  exact chainClass_boundary X _

/-- The class of a concatenation is the sum of the classes, modulo boundaries. -/
theorem pathClass_trans {x y z : X} (p : Path x y)
    (q : Path y z) : pathClass (p.trans q) = pathClass p + pathClass q := by
  have h := chainClass_boundary X (concatChain p q)
  rw [boundaryTwo_concatChain, map_add, map_sub] at h
  change pathClass q - pathClass (p.trans q) + pathClass p = 0 at h
  apply sub_eq_zero.mp
  calc
    pathClass (p.trans q) - (pathClass p + pathClass q) =
        -(pathClass q - pathClass (p.trans q) + pathClass p) := by abel
    _ = 0 := by rw [h, neg_zero]

/-- The class of a reversed path is the negative of the class, modulo boundaries. -/
@[simp]
theorem pathClass_symm {x y : X} (p : Path x y) : pathClass p.symm = -pathClass p := by
  have h := pathClass_homotopic (Path.Homotopic.trans_symm p)
  rw [pathClass_trans, pathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

@[simp]
private theorem pathClass_cast {x y : X} (p : Path x y)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : pathClass (p.cast hx hy) = pathClass p :=
  rfl

/-! ### The Hurewicz homomorphism -/

/-- The one-cycle attached to a loop. -/
def loopCycle {x : X} (p : Path x x) : Cycles1 X :=
  mkCycle1 X (pathChain p) (boundaryOne_loop p)

/-- The underlying one-chain of the cycle of a loop is the chain of the loop. -/
@[simp]
theorem loopCycle_val {x : X} (p : Path x x) : (loopCycle p).1 = pathChain p :=
  rfl

/-- The singular first-homology class of a loop. This is the underlying function of the
Hurewicz homomorphism. -/
def loopHomologyClass {x : X} (p : Path x x) : SingularH1 X :=
  cycleClass X (loopCycle p)

/-- Modulo boundaries, the homology class of a loop is the class of its chain. -/
@[simp]
theorem homologyToChainClass_loopHomologyClass
    {x : X} (p : Path x x) : homologyToChainClass X (loopHomologyClass p) = pathClass p := by
  rw [loopHomologyClass, homologyToChainClass_cycleClass]
  rfl

/-- Homotopic loops have the same homology class. -/
theorem loopHomologyClass_homotopic {x : X}
    {p q : Path x x} (h : p.Homotopic q) : loopHomologyClass p = loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass]
  exact pathClass_homotopic h

/-- The constant loop has homology class zero. -/
@[simp]
theorem loopHomologyClass_refl (x : X) : loopHomologyClass (Path.refl x) = 0 := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, pathClass_refl, map_zero]

/-- The homology class of a concatenation is the sum of the homology classes. Together with
`loopHomologyClass_homotopic` this makes the loop class a homomorphism on the fundamental
group. -/
theorem loopHomologyClass_trans {x : X} (p q : Path x x) :
    loopHomologyClass (p.trans q) = loopHomologyClass p + loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, map_add, homologyToChainClass_loopHomologyClass,
    homologyToChainClass_loopHomologyClass, pathClass_trans]

/-- The Hurewicz map on the fundamental group: the homology class of any representative
loop. -/
def hurewiczFunction (b : X) : FundamentalGroup X b → SingularH1 X :=
  Quotient.lift (fun p : Path b b => loopHomologyClass p)
    (fun _ _ h ↦ loopHomologyClass_homotopic h)

/-- A loop whose fundamental-group class is trivial has zero singular first-homology class. -/
theorem loopHomologyClass_eq_zero_of_mk_eq_one {b : X} (p : Path b b)
    (hp : FundamentalGroup.fromPath ⟦p⟧ = 1) : loopHomologyClass p = 0 := by
  have hz := congrArg (hurewiczFunction b) hp
  rw [FundamentalGroup.one_def] at hz
  change loopHomologyClass p = loopHomologyClass (Path.refl b) at hz
  rwa [loopHomologyClass_refl] at hz

/-- The Hurewicz map as a homomorphism of groups `π₁(X, b) →* H₁(X)`, the target written
multiplicatively. -/
def hurewiczPi1 (b : X) : FundamentalGroup X b →* Multiplicative (SingularH1 X) where
  toFun g := Multiplicative.ofAdd (hurewiczFunction b g)
  map_one' := congrArg Multiplicative.ofAdd (loopHomologyClass_refl b)
  map_mul' g h := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
    change
      Multiplicative.ofAdd (loopHomologyClass (q.trans p)) =
        Multiplicative.ofAdd (loopHomologyClass p + loopHomologyClass q)
    rw [loopHomologyClass_trans, add_comm]

/-- The Hurewicz homomorphism: the `ℤ`-linear map from the abelianized fundamental group to
singular first homology sending the class of a loop to the class of its one-simplex. It is
defined for every basepoint of every space; for a path-connected space it is an isomorphism
(`hurewiczEquiv`). -/
def hurewiczHom (b : X) : AbelianPi1 X b →ₗ[ℤ] SingularH1 X where
  toFun := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft
  map_add' := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using map_intCast_smul (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft ℤ ℤ n a

/-- The defining property of the Hurewicz homomorphism: it sends the class of a loop to its
homology class. -/
@[simp]
theorem hurewiczHom_loopClass (b : X)
    (p : Path b b) : hurewiczHom b (loopClass p) = loopHomologyClass p :=
  rfl

private theorem homologyToChainClass_hurewiczHom_loopClass
    (b : X) (p : Path b b) :
    homologyToChainClass X (hurewiczHom b (loopClass p)) = pathClass p := by
  rw [hurewiczHom_loopClass, homologyToChainClass_loopHomologyClass]

private theorem hurewiczHom_basedLoopClass {x y : X}
    (b : X) (r : ∀ a : X, Path b a) (p : Path x y) :
    homologyToChainClass X (hurewiczHom b (basedLoopClass r p)) =
      pathClass (r x) + pathClass p - pathClass (r y) := by
  change homologyToChainClass X (hurewiczHom b (loopClass (basedLoop r p))) = _
  rw [homologyToChainClass_hurewiczHom_loopClass]
  change pathClass ((r x).trans (p.trans (r y).symm)) = _
  rw [pathClass_trans, pathClass_trans, pathClass_symm]
  abel

/-! ### The inverse: the edge-loop cochain

After a handful of normalization lemmas relating a path to the path traced by its own
one-simplex, the edge-loop cochain sends each singular one-simplex to the class of its
closed-up loop, kills boundaries, and descends to homology. -/

private theorem basedLoopClass_cast {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) {x' y' : X} (hx : x' = x) (hy : y' = y) :
    basedLoopClass r (p.cast hx hy) = basedLoopClass r p := by
  cases hx
  cases hy
  rfl

private theorem simplexPath_pathSimplex_cast {x y : X} (p : Path x y) :
    simplexPath (pathSimplex p) =
      p.cast (pathSimplex_vertex_zero p) (pathSimplex_vertex_one p) := by
  apply Path.ext
  funext t
  change p (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t)) = p t
  rw [Homeomorph.apply_symm_apply]

@[simp]
private theorem basedLoopClass_simplexPath_pathSimplex
    {b x y : X} (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r (simplexPath (pathSimplex p)) = basedLoopClass r p := by
  rw [simplexPath_pathSimplex_cast, basedLoopClass_cast]

private theorem basedLoopClass_triangleFacePath {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath σ i) =
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r (simplexPath (σ.comp (simplexFace 1 i))) _ _

/-- The edge-loop cochain: given a system of paths `r` from the basepoint, send a singular
one-simplex `σ` to the class of the loop `r (σ 0) · σ · (r (σ 1))⁻¹` in the abelianized
fundamental group, extended linearly to one-chains. This is the chain-level inverse of the
Hurewicz homomorphism. -/
def edgeLoopCochain {b : X} (r : ∀ x : X, Path b x) : Chains X 1 →ₗ[ℤ] AbelianPi1 X b :=
  chainLift X 1 (fun σ => basedLoopClass r (simplexPath σ))

/-- The edge-loop cochain evaluates a singular one-simplex at its closed-up path class. -/
@[simp]
theorem edgeLoopCochain_simplex {b : X} (r : ∀ x : X, Path b x) (σ : SingularSimplex X 1) :
    edgeLoopCochain r (simplexChain X 1 σ) = basedLoopClass r (simplexPath σ) :=
  chainLift_simplex X 1 (fun σ => basedLoopClass r (simplexPath σ)) σ

/-- The edge-loop cochain evaluates a path's one-simplex at the path's closed-up class. -/
theorem edgeLoopCochain_pathSimplex {b x y : X} (r : ∀ x : X, Path b x) (p : Path x y) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = basedLoopClass r p := by
  rw [edgeLoopCochain_simplex, basedLoopClass_simplexPath_pathSimplex]

/-- The edge-loop cochain evaluates a loop's one-simplex at the loop's own class. -/
theorem edgeLoopCochain_loopSimplex {b : X} (r : ∀ x : X, Path b x) (p : Path b b) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = loopClass p := by
  rw [edgeLoopCochain_pathSimplex, basedLoopClass_loop]

private theorem edgeLoopCochain_boundaryTwo_simplex {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) :
    edgeLoopCochain r (boundaryTwo X (simplexChain X 2 σ)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeLoopCochain_simplex]
  rw [← basedLoopClass_triangleFacePath r σ 0, ← basedLoopClass_triangleFacePath r σ 1,
    ← basedLoopClass_triangleFacePath r σ 2]
  exact basedLoopClass_triangle_boundary r (triangleEdge01 σ) (triangleEdge12 σ)
    (triangleEdge02 σ) (triangleEdges_homotopic σ)

private theorem edgeLoopCochain_comp_boundaryTwo {b : X}
    (r : ∀ x : X, Path b x) : (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainMap_ext X 2
  intro σ
  exact edgeLoopCochain_boundaryTwo_simplex r σ

/-- The edge-loop cochain kills boundaries: the three edges of a singular two-simplex compose
up to path homotopy, so their alternating sum dies in the abelianized fundamental group. -/
theorem edgeLoopCochain_boundaryTwo {b : X}
    (r : ∀ x : X, Path b x) (c : Chains X 2) : edgeLoopCochain r (boundaryTwo X c) = 0 :=
  LinearMap.congr_fun (edgeLoopCochain_comp_boundaryTwo r) c

/-- The inverse Hurewicz map on homology, obtained by descending the edge-loop cochain. -/
def inverseHurewiczHom {b : X} (r : ∀ x : X, Path b x) : SingularH1 X →ₗ[ℤ] AbelianPi1 X b :=
  homologyDescOfChain X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r)

/-- The defining property of the inverse Hurewicz map: on the class of a cycle it evaluates
the edge-loop cochain. -/
@[simp]
theorem inverseHurewiczHom_cycleClass {b : X} (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    inverseHurewiczHom r (cycleClass X c) = edgeLoopCochain r c.1 :=
  homologyDescOfChain_cycleClass X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r) c

private def basePathChain {b : X} (r : ∀ x : X, Path b x) : Chains X 0 →ₗ[ℤ] Chains X 1 :=
  chainLift X 0 (fun σ => pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))))

@[simp]
private theorem basePathChain_pointChain {b : X}
    (r : ∀ x : X, Path b x) (x : X) : basePathChain r (pointChain x) = pathChain (r x) :=
  chainLift_simplex X 0 _ (ContinuousMap.const (Simplex 0) x)

private theorem edgeClosure_pathChain {b x y : X} (r : ∀ x : X, Path b x) (p : Path x y) :
    homologyToChainClass X (hurewiczHom b (edgeLoopCochain r (pathChain p))) =
      chainClass X (pathChain p) -
        chainClass X (basePathChain r (boundaryOne X (pathChain p))) := by
  have he : edgeLoopCochain r (pathChain p) = basedLoopClass r p :=
    edgeLoopCochain_pathSimplex r p
  rw [he, hurewiczHom_basedLoopClass, boundaryOne_pathChain, map_sub, basePathChain_pointChain,
    basePathChain_pointChain, map_sub]
  change
    pathClass (r x) + pathClass p - pathClass (r y) =
      pathClass p - (pathClass (r y) - pathClass (r x))
  abel

private theorem edgeClosure_chain_identity {b : X} (r : ∀ x : X, Path b x) :
    (homologyToChainClass X).comp ((hurewiczHom b).comp (edgeLoopCochain r)) =
      chainClass X - (chainClass X).comp ((basePathChain r).comp (boundaryOne X)) := by
  apply chainMap_ext X 1
  intro σ
  have h := edgeClosure_pathChain r (simplexPath σ)
  simpa only [pathChain, pathSimplex_simplexPath, LinearMap.comp_apply, LinearMap.sub_apply] using
    h

private theorem edgeClosure_cycle {b : X} (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    homologyToChainClass X (hurewiczHom b (edgeLoopCochain r c.1)) = chainClass X c.1 := by
  have h := LinearMap.congr_fun (edgeClosure_chain_identity r) c.1
  change
    homologyToChainClass X (hurewiczHom b (edgeLoopCochain r c.1)) =
      chainClass X c.1 - chainClass X (basePathChain r (boundaryOne X c.1)) at h
  simpa only [cycles1_boundary, map_zero, sub_zero] using h

/-- The inverse Hurewicz map sends a loop's homology class to the loop's class in the
abelianized fundamental group. -/
@[simp]
theorem inverseHurewiczHom_loopHomologyClass {b : X} (r : ∀ x : X, Path b x) (p : Path b b) :
    inverseHurewiczHom r (loopHomologyClass p) = loopClass p := by
  rw [loopHomologyClass, inverseHurewiczHom_cycleClass, loopCycle_val]
  exact edgeLoopCochain_loopSimplex r p

/-- The inverse Hurewicz map is a left inverse of the Hurewicz homomorphism. -/
theorem inverseHurewiczHom_hurewiczHom {b : X}
    (r : ∀ x : X, Path b x) (a : AbelianPi1 X b) : inverseHurewiczHom r (hurewiczHom b a) = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczHom_loopClass, inverseHurewiczHom_loopHomologyClass]

/-- The inverse Hurewicz map is a right inverse of the Hurewicz homomorphism: the class of
any cycle is recovered, by computing modulo boundaries. -/
theorem hurewiczHom_inverseHurewiczHom {b : X}
    (r : ∀ x : X, Path b x) (a : SingularH1 X) : hurewiczHom b (inverseHurewiczHom r a) = a := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X a
  apply homologyToChainClass_injective X
  rw [inverseHurewiczHom_cycleClass, homologyToChainClass_cycleClass]
  exact edgeClosure_cycle r c

/-! ### The Hurewicz isomorphism -/

/-- The Hurewicz isomorphism, given an explicit system of paths from the basepoint to every
point of the space. -/
def hurewiczEquivOfPaths {b : X} (r : ∀ x : X, Path b x) : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X where
  toLinearMap := hurewiczHom b
  invFun := inverseHurewiczHom r
  left_inv := inverseHurewiczHom_hurewiczHom r
  right_inv := hurewiczHom_inverseHurewiczHom r

/-- **The Hurewicz theorem in degree one**: for a path-connected space, singular first
homology with integer coefficients is the abelianized fundamental group. -/
def hurewiczEquiv (b : X) [PathConnectedSpace X] :
    Additive (Abelianization (FundamentalGroup X b)) ≃ₗ[ℤ] SingularH1 X :=
  hurewiczEquivOfPaths (PathConnectedSpace.somePath b)

/-- The Hurewicz isomorphism sends the class of a loop to its homology class. -/
@[simp]
theorem hurewiczEquiv_loopClass (b : X) [PathConnectedSpace X] (p : Path b b) :
    hurewiczEquiv b
        (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk p)))) =
      loopHomologyClass p :=
  hurewiczHom_loopClass b p

/-- The inverse Hurewicz isomorphism sends the homology class of a loop to its class in the
abelianized fundamental group. -/
@[simp]
theorem hurewiczEquiv_symm_loopHomologyClass {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] (p : Path b b) :
    (hurewiczEquiv b).symm (loopHomologyClass p) =
      Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk p))) := by
  rw [LinearEquiv.symm_apply_eq, hurewiczEquiv_loopClass]

/-- Every singular first-homology class of a path-connected space is the class of a loop. -/
theorem loopHomologyClass_surjective (b : X)
    [PathConnectedSpace X] : Function.Surjective (loopHomologyClass (x := b)) := by
  intro a
  obtain ⟨c, hc⟩ := (hurewiczEquiv b).surjective a
  obtain ⟨p, hp⟩ := loopClass_surjective c
  refine ⟨p, ?_⟩
  have hp' : Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath ⟦p⟧)) = c := by
    simpa only [loopClass] using hp
  calc
    loopHomologyClass p =
        hurewiczEquiv b (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath ⟦p⟧))) :=
      (hurewiczEquiv_loopClass b p).symm
    _ = hurewiczEquiv b c := congrArg (hurewiczEquiv b) hp'
    _ = a := hc

/-- To prove a statement about all singular first-homology classes of a path-connected space,
it suffices to prove it for classes of loops at a chosen basepoint. -/
@[elab_as_elim]
theorem singularH1_induction_on {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (b : X)
    {motive : SingularH1 X → Prop} (x : SingularH1 X)
    (h : ∀ p : Path b b, motive (loopHomologyClass p)) : motive x := by
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective b x
  exact h p

/-! ### Naturality and conjugation invariance -/

theorem pathSimplex_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (f : C(X, Y)) (p : Path x y) :
    pathSimplex (p.map f.continuous) = f.comp (pathSimplex p) :=
  rfl

/-- The induced chain map sends a path's chain to the image path's chain. -/
@[simp]
theorem inducedChain_pathChain {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (f : C(X, Y)) (p : Path x y) :
    inducedChain f 1 (pathChain p) = pathChain (p.map f.continuous) := by
  simp only [pathChain, inducedChain_simplex, pathSimplex_map]

/-- The induced map on cycles sends a loop's cycle to the image loop's cycle. -/
@[simp]
theorem inducedCycles_loopCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedCycles f (loopCycle p) = loopCycle (p.map f.continuous) := by
  apply Subtype.ext
  rw [inducedCycles_val, loopCycle_val, loopCycle_val, inducedChain_pathChain]

end Hurewicz

/-- Naturality of the loop class: a continuous map sends the class of a loop to the class of
its image loop. -/
@[simp]
theorem SingularH1.map_loopHomologyClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    SingularH1.map f (Hurewicz.loopHomologyClass p) =
      Hurewicz.loopHomologyClass (p.map f.continuous) := by
  rw [Hurewicz.loopHomologyClass, SingularH1.map_cycleClass, Hurewicz.inducedCycles_loopCycle]
  rfl

namespace Hurewicz

variable {X : Type} [TopologicalSpace X]

/-- Conjugating a loop by a change-of-basepoint path preserves its singular first-homology class. -/
theorem loopHomologyClass_conjugate {x b : X} (γ : Path x b) (p : Path x x) :
    loopHomologyClass (γ.symm.trans (p.trans γ)) = loopHomologyClass p := by
  apply homologyToChainClass_injective X
  simp only [homologyToChainClass_loopHomologyClass, pathClass_trans, pathClass_symm]
  abel

end Hurewicz

end AlgebraicTopology
