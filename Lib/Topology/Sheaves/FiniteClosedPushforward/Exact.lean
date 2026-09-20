/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.FiniteClosedPushforward
public import Lib.Topology.Sheaves.AddCommGrpPushforward
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Exactness of finite closed-map pushforward

For a finite map `f : X → Y` (here: a closed map with finite fibres and Hausdorff source) the
pushforward functor `f_*` on sheaves of abelian groups is exact, because `(f_*F)_y = ⊕_{x ∈ f⁻¹(y)}
F_x` (Hartshorne, *Algebraic Geometry*, II Ex. 1.19 and III Ex. 8.2; Iversen, *Cohomology of
Sheaves*, II).

Independently of finiteness, `f_*` preserves injective objects because its left adjoint `f^{-1}` is
exact, hence preserves monomorphisms (Hartshorne III Prop. 2.4 and its proof).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace TopCat.FiniteClosedPushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The inverse-image functor `f^{-1}` on sheaves of abelian groups is left exact: it preserves
finite limits. -/
theorem pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
  change PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{0}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat.{0}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- For any continuous map, `f_*` preserves injective sheaves, since its left adjoint `f^{-1}` is
exact (Hartshorne III Prop. 2.4). -/
theorem pushforward_preservesInjectiveObjects :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).PreservesInjectiveObjects := by
  let _ := pullback_preservesFiniteLimits f
  let _ := preservesMonomorphisms_of_preservesLimitsOfShape
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)

variable [T2Space X] (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

include hf hfinite

/-- For a finite closed map, `f_*` is exact: it takes exact short complexes of sheaves of abelian
groups to exact short complexes (Hartshorne II Ex. 1.19). -/
theorem pushforward_exact
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.Exact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f)).Exact := by
  classical
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f))).mpr
  intro y
  let K := TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y
  let e₁ := pushforwardStalkEquiv f hf S.X₁ y (hfinite y)
  let e₂ := pushforwardStalkEquiv f hf S.X₂ y (hfinite y)
  let e₃ := pushforwardStalkEquiv f hf S.X₃ y (hfinite y)
  apply (((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f)).map K).ab_exact_iff).mpr
  intro s hs
  have hzero : e₃ (K.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map S.g) s) = 0 :=
    (congrArg e₃ hs).trans e₃.map_zero
  have hker (x : f ⁻¹' {y}) :
      (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x.val).map S.g (e₂ s x) = 0 :=
    (pushforwardStalkEquiv_naturality f hf S.g y (hfinite y) s x).symm.trans
      (congrFun hzero x)
  have hlocal (x : f ⁻¹' {y}) :
      ∃ u, (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x.val).map S.f u = e₂ s x := by
    have hexact := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x.val
    exact ((S.map (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x.val)).ab_exact_iff.mp hexact)
      (e₂ s x) (hker x)
  choose u hu using hlocal
  refine ⟨e₁.symm u, ?_⟩
  apply e₂.injective
  funext x
  exact (pushforwardStalkEquiv_naturality f hf S.f y (hfinite y)
    (e₁.symm u) x).trans
      ((congrArg ((TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x.val).map S.f)
        (congrFun (e₁.apply_symm_apply u) x)).trans (hu x))

/-- For a finite closed map, `f_*` preserves finite limits and finite colimits. -/
theorem pushforward_preservesFiniteLimitsAndColimits :
    PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) ∧
      PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).exact_tfae.out 1 3).mp
    (pushforward_exact f hf hfinite)

/-- For a finite closed map, `f_*` preserves finite colimits; in particular it is right exact. -/
theorem pushforward_preservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) :=
  (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).2

/-- For a finite closed map, `f_*` takes short exact sequences of sheaves to short exact
sequences. -/
theorem pushforward_shortExact
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f)).ShortExact := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact hS.map_of_exact (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f)

end TopCat.FiniteClosedPushforward
