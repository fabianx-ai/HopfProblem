/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Singular cochains with additive coefficients

This is the additive dual of Mathlib's native integral singular-chain complex.  Pullback is
literal precomposition with the native singular-chain map.  Mathlib's chain homotopy attached to
a continuous homotopy proves homotopy invariance for every small abelian coefficient group.

## References

* [A. Hatcher, *Algebraic topology*][hatcher02], §3.1 (singular cochains `Hom(Cₙ(X), G)`
  and their homotopy invariance).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped ContinuousMap

namespace AlgebraicTopology.SingularCochains

universe u w

/-- Literal precomposition on additive homomorphisms. -/
def precompose (A : AddCommGrpCat.{w}) {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) : (N →+ A) →+ (M →+ A) where
  toFun φ := φ.comp f
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- The contravariant additive dual of an integral module.  The target is
`AddCommGrpCat.{max u w}`, not `AddCommGrpCat.{w}`: the additive homomorphisms out of an object of
`ModuleCat.{u} ℤ` into `A : AddCommGrpCat.{w}` form a type in `max u w`. -/
def moduleDual (A : AddCommGrpCat.{w}) :
    (ModuleCat.{u} ℤ)ᵒᵖ ⥤ AddCommGrpCat.{max u w} where
  obj M := AddCommGrpCat.of (M.unop →+ A)
  map f := AddCommGrpCat.ofHom (precompose A f.unop.hom.toAddMonoidHom)
  map_id _ := by
    apply AddCommGrpCat.hom_ext
    ext φ c
    rfl
  map_comp _ _ := by
    apply AddCommGrpCat.hom_ext
    ext φ c
    rfl

/-- Additive duality is an additive functor. -/
instance moduleDual_additive (A : AddCommGrpCat.{w}) : (moduleDual A).Additive where
  map_add := by
    intro M N f g
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply AddMonoidHom.ext
    intro c
    exact φ.map_add (f.unop.hom c) (g.unop.hom c)

/-- Contravariant additive duality on integral chain complexes. -/
def dualComplexFunctor (A : AddCommGrpCat.{w}) :
    (ChainComplex (ModuleCat.{u} ℤ) ℕ)ᵒᵖ ⥤
      CochainComplex AddCommGrpCat.{max u w} ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) ⋙
    (moduleDual A).mapHomologicalComplex (ComplexShape.down ℕ).symm

/-- Additive dual cochain complex of an integral chain complex.  Like `moduleDual`, it lands in
`AddCommGrpCat.{max u w}`, so for `u ≠ w` the resulting cochain complex lives in a larger universe
than `A` itself; at `u = 0` this is `AddCommGrpCat.{w}`. -/
def dualComplex (A : AddCommGrpCat.{w})
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  (dualComplexFunctor A).obj (op K)

/-- Contravariant dual of a chain map. -/
def dualMap (A : AddCommGrpCat.{w})
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) :
    dualComplex A L ⟶ dualComplex A K :=
  (dualComplexFunctor A).map f.op

/-- The dual of the identity chain map is the identity. -/
@[simp]
theorem dualMap_id (A : AddCommGrpCat.{w})
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    dualMap A (𝟙 K) = 𝟙 (dualComplex A K) := by
  exact (dualComplexFunctor A).map_id (op K)

/-- Additive duality is contravariantly functorial. -/
@[simp]
theorem dualMap_comp (A : AddCommGrpCat.{w})
    {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) :
    dualMap A (f ≫ g) = dualMap A g ≫ dualMap A f := by
  exact (dualComplexFunctor A).map_comp g.op f.op

/-- A chain homotopy dualizes to a cochain homotopy. -/
def dualHomotopy (A : AddCommGrpCat.{w})
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) :
    _root_.Homotopy (dualMap A f) (dualMap A g) :=
  (moduleDual A).mapHomotopy h.op

/-- Mathlib's integral singular-chain complex of `X`. -/
abbrev chains (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- Singular cochains with coefficients in `A`. -/
abbrev complex (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{w} ℕ := dualComplex A (chains X)

/-- Pullback on singular cochains. -/
def pullback {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{w}) (f : C(X, Y)) : complex Y A ⟶ complex X A :=
  dualMap A (((AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))

/-- Pullback along the identity map is the identity on singular cochains. -/
@[simp]
theorem pullback_id (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{w}) :
    pullback A (ContinuousMap.id X) = 𝟙 (complex X A) := by
  change dualMap A
    (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of X))) = _
  let F := (AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)
  exact (congrArg (dualMap A) (F.map_id (TopCat.of X))).trans
    (dualMap_id A (chains X))

/-- Pullback turns a composite of continuous maps into the composite of the pullbacks, in the
opposite order. -/
@[simp]
theorem pullback_comp {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : AddCommGrpCat.{w}) (f : C(X, Y)) (g : C(Y, Z)) :
    pullback A (g.comp f) = pullback A g ≫ pullback A f := by
  change dualMap A
      (((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom f ≫ TopCat.ofHom g)) = _
  let F := (AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)
  exact (congrArg (dualMap A) (F.map_comp (TopCat.ofHom f) (TopCat.ofHom g))).trans
    (dualMap_comp A (F.map (TopCat.ofHom f)) (F.map (TopCat.ofHom g)))

/-- Continuous homotopies induce cochain homotopies. -/
def pullbackHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{w}) {f g : C(X, Y)} (H : f.Homotopy g) :
    _root_.Homotopy (pullback A f) (pullback A g) :=
  dualHomotopy A (TopCat.Homotopy.singularChainComplexFunctorObjMap
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℤ ℤ))

/-- Homotopic maps induce equal maps on singular cohomology. -/
theorem homologyMap_eq_of_homotopy {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{w}) {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    HomologicalComplex.homologyMap (pullback A f) n =
      HomologicalComplex.homologyMap (pullback A g) n :=
  (pullbackHomotopy A H).homologyMap_eq n

/-- A topological homotopy equivalence induces a singular-cohomology isomorphism. -/
def homotopyEquivCohomologyIso {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{w}) (e : X ≃ₕ Y) (n : ℕ) :
    (complex Y A).homology n ≅ (complex X A).homology n :=
  ({
    hom := pullback A e.toFun
    inv := pullback A e.invFun
    homotopyHomInvId := by
      simpa only [pullback_comp, pullback_id] using
        pullbackHomotopy A (Classical.choice e.right_inv)
    homotopyInvHomId := by
      simpa only [pullback_comp, pullback_id] using
        pullbackHomotopy A (Classical.choice e.left_inv)
  } : _root_.HomotopyEquiv (complex Y A) (complex X A)).toHomologyIso n

/-- The cohomology isomorphism of a homotopy equivalence is induced by pullback along it. -/
@[simp]
theorem homotopyEquivCohomologyIso_hom {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{w}) (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivCohomologyIso A e n).hom =
      HomologicalComplex.homologyMap (pullback A e.toFun) n := rfl

end AlgebraicTopology.SingularCochains
