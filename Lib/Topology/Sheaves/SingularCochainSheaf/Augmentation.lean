/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.Sheaf
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Constant augmentation of the native singular-cochain sheaf

The augmentation is constructed directly from Mathlib's coproduct presentation of native
singular zero-chains.  It is natural under continuous maps and its coboundary is zero.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Simplicial

namespace TopCat.SingularCochainSheaf

/-- The native chain map induced by a continuous map. -/
abbrev chainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    AlgebraicTopology.SingularCochains.chains X ⟶
      AlgebraicTopology.SingularCochains.chains Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

/-- The singular simplicial set underlying a space. -/
abbrev singularSet (X : Type) [TopologicalSpace X] : SSet :=
  TopCat.toSSet.obj (TopCat.of X)

/-- Sum of coefficients in the literal coproduct model of singular zero-chains. -/
def rawChainAugmentation (X : Type) [TopologicalSpace X] :
    ((singularSet X).chainComplex (ModuleCat.of ℤ ℤ)).X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Sigma.desc (fun _ : (TopCat.toSSet.obj (TopCat.of X)) _⦋0⦌ =>
    𝟙 (ModuleCat.of ℤ ℤ))

/-- Sum of coefficients on the current native singular zero-chains. -/
abbrev chainAugmentation (X : Type) [TopologicalSpace X] :
    (AlgebraicTopology.SingularCochains.chains X).X 0 ⟶ ModuleCat.of ℤ ℤ :=
  rawChainAugmentation X

@[reassoc (attr := simp)]
theorem simplex_chainAugmentation (X : Type) [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋0⦌) :
    (singularSet X).ιChainComplex σ ≫ rawChainAugmentation X =
      𝟙 (ModuleCat.of ℤ ℤ) := by
  change Sigma.ι _ σ ≫ Sigma.desc (fun _ => 𝟙 (ModuleCat.of ℤ ℤ)) = _
  simp

/-- Sum of coefficients is natural under continuous maps. -/
@[reassoc]
theorem rawChainAugmentation_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
      (ModuleCat.of ℤ ℤ)).f 0 ≫ rawChainAugmentation Y = rawChainAugmentation X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [SSet.ι_chainComplexMap_f_assoc,
    simplex_chainAugmentation, simplex_chainAugmentation]

/-- Sum of coefficients is natural for the current native singular-chain map. -/
@[reassoc]
theorem chainAugmentation_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (chainMap f).f 0 ≫ chainAugmentation Y = chainAugmentation X :=
  rawChainAugmentation_naturality f

/-- The singular boundary in degree one has coefficient sum zero. -/
@[reassoc]
theorem rawBoundary_chainAugmentation (X : Type) [TopologicalSpace X] :
    ((singularSet X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫
      rawChainAugmentation X = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [SSet.ιChainComplex_d_assoc]
  simp

/-- The current native singular boundary in degree one has coefficient sum zero. -/
@[reassoc]
theorem boundary_chainAugmentation (X : Type) [TopologicalSpace X] :
    (AlgebraicTopology.SingularCochains.chains X).d 1 0 ≫ chainAugmentation X = 0 :=
  rawBoundary_chainAugmentation X

/-- The additive map sending an integer to its multiple of `a`. -/
def integerMultiple (A : AddCommGrpCat.{0}) (a : A) : ℤ →+ A where
  toFun n := n • a
  map_zero' := zero_zsmul a
  map_add' m n := add_zsmul a m n

/-- The constant native zero-cochain with value `a`. -/
def constantCochain (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) :
    A →+ (AlgebraicTopology.SingularCochains.complex X A).X 0 where
  toFun a := (integerMultiple A a).comp (chainAugmentation X).hom.toAddMonoidHom
  map_zero' := by
    apply AddMonoidHom.ext
    intro c
    change ((chainAugmentation X).hom c : ℤ) • (0 : A) = 0
    exact zsmul_zero _
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    change ((chainAugmentation X).hom c : ℤ) • (a + b) =
      ((chainAugmentation X).hom c : ℤ) • a + ((chainAugmentation X).hom c : ℤ) • b
    exact zsmul_add _ _ _

/-- Constant zero-cochains have zero coboundary. -/
theorem constantCochain_d_zero (X : Type) [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (a : A) :
    (AlgebraicTopology.SingularCochains.complex X A).d 0 1
      (constantCochain X A a) = 0 := by
  apply AddMonoidHom.ext
  intro c
  change integerMultiple A a
      ((chainAugmentation X).hom
        (((AlgebraicTopology.SingularCochains.chains X).d 1 0).hom c)) = 0
  have h := ConcreteCategory.congr_hom (boundary_chainAugmentation X) c
  dsimp at h
  rw [h]
  exact (integerMultiple A a).map_zero

/-- Pullback preserves the constant native zero-cochain. -/
theorem pullback_constant {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (f : C(X, Y)) (a : A) :
    (AlgebraicTopology.SingularCochains.pullback A f).f 0
      (constantCochain Y A a) = constantCochain X A a := by
  apply AddMonoidHom.ext
  intro c
  change integerMultiple A a
      ((chainAugmentation Y).hom ((chainMap f).f 0 c)) =
    integerMultiple A a ((chainAugmentation X).hom c)
  exact congrArg (integerMultiple A a)
    (ConcreteCategory.congr_hom (chainAugmentation_naturality f) c)

/-- The canonical augmentation from the constant presheaf. -/
def presheafAugmentation (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    TopCat.ConstantSheaf.presheaf X A ⟶ presheaf X A 0 where
  app U := AddCommGrpCat.ofHom (constantCochain U.unop A)
  naturality _ _ i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact (pullback_constant A ((Opens.toTopCat X).map i.unop).hom a).symm

/-- The presheaf augmentation followed by the native differential is zero. -/
@[reassoc]
theorem presheafAugmentation_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    presheafAugmentation X A ≫ differential X A 0 1 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact constantCochain_d_zero U.unop A a

/-- The genuine constant sheaf augments the sheafified native cochain complex. -/
def sheafAugmentation (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    TopCat.ConstantSheaf.sheaf X A ⟶ sheaf X A 0 :=
  (sheafification X).map (presheafAugmentation X A)

/-- The sheaf augmentation followed by the sheafified differential is zero. -/
@[reassoc]
theorem sheafAugmentation_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    sheafAugmentation X A ≫ sheafDifferential X A 0 1 = 0 := by
  exact ((sheafification X).map_comp
    (presheafAugmentation X A) (differential X A 0 1)).symm.trans
      ((congrArg (sheafification X).map (presheafAugmentation_d X A)).trans
        ((sheafification X).map_zero _ _))

/-- The native augmented sheaf complex in degrees zero and one. -/
abbrev initialComplex (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (sheafAugmentation X A) (sheafDifferential X A 0 1)
    (sheafAugmentation_d X A)

end TopCat.SingularCochainSheaf
