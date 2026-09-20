/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Basic
public import Mathlib.Topology.Sets.Opens

/-!
# Native singular-cochain generators

Native singular cochains are determined freely by their values on singular simplices.  This
module supplies the generator-level construction, extensionality, the open-subspace simplex,
and the pullback evaluation lemma.

## References

* [A. Hatcher, *Algebraic topology*][hatcher02], §3.1 (a cochain is a function on singular
  simplices, `Hom(⨁_σ ℤ, A) ≅ ∏_σ A`); compare `Finsupp.lhom_ext` in Mathlib.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace
open scoped Simplicial


namespace AlgebraicTopology.SingularCochains

/-- Native additive singular cochains in degree `n`. -/
abbrev Cochains (X : Type) [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ) :=
  ((AlgebraicTopology.SingularCochains.chains X).X n : Type) →+ A

/-- Restrict a singular simplex to an open set containing its image. -/
def simplexInOpen {X : Type} [TopologicalSpace X] (n : ℕ)
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n)
    (U : Opens X) (hsigma : Set.range sigma ⊆ U) :
    TopCat.SingularSmallChains.SingularSimplex U n where
  toFun z := ⟨sigma z, hsigma (Set.mem_range_self z)⟩
  continuous_toFun := sigma.continuous.subtype_mk _

/-- The restricted simplex has the same underlying point map as the original one. -/
@[simp]
theorem simplexInOpen_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n)
    (U : Opens X) (hsigma : Set.range sigma ⊆ U)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (simplexInOpen n sigma U hsigma z : X) = sigma z := rfl


/-- Pullback evaluated on a native simplex is evaluation on its image simplex. -/
theorem pullback_simplex {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (f : C(X, Y)) (n : ℕ)
    (c : Cochains Y A n)
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n) :
    (show Cochains X A n from
      (AlgebraicTopology.SingularCochains.pullback A f).f n c)
        (TopCat.SingularSmallChains.simplexChain X n sigma) =
      c (TopCat.SingularSmallChains.simplexChain Y n (f.comp sigma)) := by
  change c
      (((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f n)
          (TopCat.SingularSmallChains.simplexChain X n sigma)) = _
  exact congrArg c (ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)
      (TopCat.SingularSmallChains.simplexIndex X n sigma)) 1)


/-- Native cochains are determined by their values on singular simplices. -/
theorem cochain_ext {X : Type} [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ) {c d : Cochains X A n}
    (h : ∀ sigma : TopCat.SingularSmallChains.SingularSimplex X n,
      c (TopCat.SingularSmallChains.simplexChain X n sigma) =
        d (TopCat.SingularSmallChains.simplexChain X n sigma)) : c = d := by
  apply AddMonoidHom.ext
  have he : TopCat.SingularSmallChains.addHomToIntLinearMap c =
      TopCat.SingularSmallChains.addHomToIntLinearMap d := by
    apply TopCat.SingularSmallChains.chainMap_ext X n
    exact h
  intro z
  exact LinearMap.congr_fun he z


/-- Extend arbitrary simplex values to a native singular cochain. -/
def cochainFromValues {X : Type} [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ)
    (value : TopCat.SingularSmallChains.SingularSimplex X n → A) :
    Cochains X A n :=
  (TopCat.SingularSmallChains.chainLift X n value).toAddMonoidHom

/-- The cochain extending a family of values takes exactly those values on singular simplices. -/
@[simp]
theorem cochainFromValues_simplex {X : Type} [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ)
    (value : TopCat.SingularSmallChains.SingularSimplex X n → A)
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n) :
    cochainFromValues A n value
        (TopCat.SingularSmallChains.simplexChain X n sigma) = value sigma :=
  TopCat.SingularSmallChains.chainLift_simplex X n value sigma

end AlgebraicTopology.SingularCochains
