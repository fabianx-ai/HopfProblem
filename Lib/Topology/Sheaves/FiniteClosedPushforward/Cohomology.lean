/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorComparison
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup
public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
public import Lib.Topology.Sheaves.FiniteClosedPushforward.Exact

/-!
# Cohomology of finite closed-map pushforwards

For a finite map `f : X → Y` (here: a closed map with finite fibres and Hausdorff source) the
pushforward `f_*` is exact and preserves injective objects, so `H^n(X, F) ≅ H^n(Y, f_*F)` in every
degree (Hartshorne, *Algebraic Geometry*, III Ex. 8.1 (Leray); Iversen, *Cohomology of
Sheaves*, II).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace TopCat.FiniteClosedPushforward

variable {X Y : TopCat.{u}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The canonical map `H^n(X, F) → H^n(Y, f_*F)` induced by a finite closed map `f`. -/
def cohomologyForward (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F n →+
      CategoryTheory.Sheaf.H.{u}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact Ext.ExactFunctorComparison.map
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f) F n

/-- For a finite closed map the comparison `H^n(X, F) → H^n(Y, f_*F)` is bijective in every
degree (Hartshorne III Ex. 8.1 (Leray)). -/
theorem cohomologyForward_bijective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Bijective (cohomologyForward f hf hfinite F n) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  let _ := pushforward_preservesInjectiveObjects f
  exact Ext.ExactFunctorComparison.map_bijective
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
    (TopCat.ConstantSheaf.integralPushforwardHom_comp_bijective f) F n

/-- For a finite closed map, `H^n(Y, f_*F) ≅ H^n(X, F)` as additive groups in every degree
(Hartshorne III Ex. 8.1 (Leray)). -/
def cohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n ≃+
      CategoryTheory.Sheaf.H.{u} F n :=
  (AddEquiv.ofBijective (cohomologyForward f hf hfinite F n)
    (cohomologyForward_bijective f hf hfinite F n)).symm

/-- The inverse of the cohomology equivalence is the forward comparison map. -/
@[simp] theorem cohomologyEquiv_symm_apply
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{u} F n) :
    (cohomologyEquiv f hf hfinite F n).symm e =
      cohomologyForward f hf hfinite F n e := rfl

/-- The forward comparison map is a left inverse of the cohomology equivalence. -/
theorem cohomologyForward_equiv
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n) :
    cohomologyForward f hf hfinite F n (cohomologyEquiv f hf hfinite F n e) = e :=
  (cohomologyEquiv f hf hfinite F n).symm_apply_apply e

/-- The comparison `H^n(X, F) → H^n(Y, f_*F)` is natural in the coefficient sheaf `F`. -/
theorem cohomologyForward_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (g : F ⟶ G)
    (n : ℕ) (e : CategoryTheory.Sheaf.H.{u} F n) :
    cohomologyForward f hf hfinite G n (CategoryTheory.Sheaf.H.map g n e) =
      CategoryTheory.Sheaf.H.map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) n
        (cohomologyForward f hf hfinite F n e) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact @Ext.ExactFunctorComparison.map_naturality
    (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} Y) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (TopCat.Sheaf.pushforwardAdditive f)
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
    (pushforward_preservesFiniteColimits f hf hfinite)
    _ _ _ _
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
    g n e

/-- The cohomology equivalence `H^n(Y, f_*F) ≅ H^n(X, F)` is natural in the coefficient
sheaf `F`. -/
theorem cohomologyEquiv_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (g : F ⟶ G)
    (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n) :
    cohomologyEquiv f hf hfinite G n
        (CategoryTheory.Sheaf.H.map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) n e) =
      CategoryTheory.Sheaf.H.map g n
        (cohomologyEquiv f hf hfinite F n e) := by
  apply (cohomologyForward_bijective f hf hfinite G n).injective
  exact (cohomologyForward_equiv f hf hfinite G n
    (CategoryTheory.Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) n e)).trans
      ((congrArg (CategoryTheory.Sheaf.H.map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) n)
          (cohomologyForward_equiv f hf hfinite F n e).symm).trans
        (cohomologyForward_naturality f hf hfinite g n
          (cohomologyEquiv f hf hfinite F n e)).symm)

end TopCat.FiniteClosedPushforward
