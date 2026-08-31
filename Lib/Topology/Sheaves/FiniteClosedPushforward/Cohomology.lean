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

For a closed map with finite fibres and Hausdorff source, additive sheaf pushforward is exact and
preserves injective objects. The native map from the integral constant sheaf into the pushforward
of the integral constant sheaf therefore induces an additive equivalence on Ext-defined sheaf
cohomology in every degree.

This is the textbook finite-map cohomology comparison. It does not identify a higher direct-image
stalk with fibre cohomology and makes no general proper-base-change claim.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.FiniteClosedPushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The canonical Ext-defined cohomology map from a sheaf to its finite closed pushforward. -/
def cohomologyForward (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} F n →+
      CategoryTheory.Sheaf.H.{0}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F) n := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact Ext.ExactFunctorComparison.map
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{0} ℤ)) f) F n

/-- The finite closed pushforward cohomology map is bijective in every degree. -/
theorem cohomologyForward_bijective (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    Function.Bijective (cohomologyForward f hf hfinite F n) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  let _ := pushforward_preservesInjectiveObjects f
  exact Ext.ExactFunctorComparison.map_bijective
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{0} ℤ)) f)
    (TopCat.ConstantSheaf.integralPushforwardHom_comp_bijective f) F n

/-- Finite closed pushforward does not change integral sheaf cohomology. -/
def cohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F) n ≃+
      CategoryTheory.Sheaf.H.{0} F n :=
  (AddEquiv.ofBijective (cohomologyForward f hf hfinite F n)
    (cohomologyForward_bijective f hf hfinite F n)).symm

@[simp] theorem cohomologyEquiv_symm_apply
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{0} F n) :
    (cohomologyEquiv f hf hfinite F n).symm e =
      cohomologyForward f hf hfinite F n e := rfl

/-- The forward comparison after its inverse is the identity. -/
theorem cohomologyForward_equiv
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{0}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F) n) :
    cohomologyForward f hf hfinite F n (cohomologyEquiv f hf hfinite F n e) = e :=
  (cohomologyEquiv f hf hfinite F n).symm_apply_apply e

/-- Naturality of the canonical forward comparison in the coefficient sheaf. -/
theorem cohomologyForward_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (g : F ⟶ G)
    (n : ℕ) (e : CategoryTheory.Sheaf.H.{0} F n) :
    cohomologyForward f hf hfinite G n (CategoryTheory.Sheaf.H.map g n e) =
      CategoryTheory.Sheaf.H.map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map g) n
        (cohomologyForward f hf hfinite F n e) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact @Ext.ExactFunctorComparison.map_naturality
    (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{0} Y) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) (TopCat.Sheaf.pushforwardAdditive f)
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
    (pushforward_preservesFiniteColimits f hf hfinite)
    _ _ _ _
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{0} ℤ)) f)
    g n e

/-- The inverse cohomology equivalence is natural in the coefficient sheaf. -/
theorem cohomologyEquiv_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (g : F ⟶ G)
    (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{0}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F) n) :
    cohomologyEquiv f hf hfinite G n
        (CategoryTheory.Sheaf.H.map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map g) n e) =
      CategoryTheory.Sheaf.H.map g n
        (cohomologyEquiv f hf hfinite F n e) := by
  apply (cohomologyForward_bijective f hf hfinite G n).injective
  exact (cohomologyForward_equiv f hf hfinite G n
    (CategoryTheory.Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map g) n e)).trans
      ((congrArg (CategoryTheory.Sheaf.H.map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map g) n)
          (cohomologyForward_equiv f hf hfinite F n e).symm).trans
        (cohomologyForward_naturality f hf hfinite g n
          (cohomologyEquiv f hf hfinite F n e)).symm)

end TopCat.FiniteClosedPushforward
