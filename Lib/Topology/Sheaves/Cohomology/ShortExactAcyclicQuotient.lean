/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ShortExactAcyclicQuotient
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup

/-!
# Degree-two sheaf cohomology across an acyclic quotient

This specializes the textbook degree-two Ext comparison to additive sheaves.
For `0 ⟶ F ⟶ G ⟶ Q ⟶ 0`, vanishing of `H¹(Q)` and `H²(Q)` makes the
literal cohomology map `H²(F) ⟶ H²(G)` an additive equivalence.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian TopologicalSpace

namespace TopCat.SheafCohomology

variable {X : TopCat.{0}}

/-- A compact interface for the two consecutive vanishings needed by the
degree-two acyclic-quotient comparison.  For a finite sum of skyscraper
sheaves these fields are the standard positive-degree acyclicity theorem. -/
structure AcyclicInDegreesOneTwo
    (Q : TopCat.Sheaf AddCommGrpCat.{0} X) : Prop where
  hOne : Subsingleton (CategoryTheory.Sheaf.H.{0} Q 1)
  hTwo : Subsingleton (CategoryTheory.Sheaf.H.{0} Q 2)

/-- The literal degree-two map induced by the first arrow of a short exact
sequence is bijective when its quotient has zero cohomology in degrees one
and two. -/
theorem hTwoMap_bijective_of_subsingleton_quotient
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₃ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₃ 2)] :
    Function.Bijective (CategoryTheory.Sheaf.H.map.{0} S.f 2) := by
  let P :=
    (constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  change Function.Bijective
    ((CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp P (add_zero 2))
  exact CategoryTheory.Abelian.Ext.postcomp_f_two_bijective_of_subsingleton_quotient P hS

/-- Canonical degree-two sheaf-cohomology equivalence induced by the
subobject inclusion. -/
def hTwoEquivMiddleOfSubsingletonQuotient
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₃ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₃ 2)] :
    CategoryTheory.Sheaf.H.{0} S.X₁ 2 ≃+
      CategoryTheory.Sheaf.H.{0} S.X₂ 2 :=
  AddEquiv.ofBijective (CategoryTheory.Sheaf.H.map.{0} S.f 2)
    (hTwoMap_bijective_of_subsingleton_quotient hS)

/-- Bundled version of the degree-two comparison. -/
def hTwoEquivMiddleOfAcyclicQuotient
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) (hQ : AcyclicInDegreesOneTwo S.X₃) :
    CategoryTheory.Sheaf.H.{0} S.X₁ 2 ≃+
      CategoryTheory.Sheaf.H.{0} S.X₂ 2 := by
  let _ := hQ.hOne
  let _ := hQ.hTwo
  exact hTwoEquivMiddleOfSubsingletonQuotient hS

@[simp]
theorem hTwoEquivMiddleOfSubsingletonQuotient_apply
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₃ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₃ 2)]
    (x : CategoryTheory.Sheaf.H.{0} S.X₁ 2) :
    hTwoEquivMiddleOfSubsingletonQuotient hS x =
      CategoryTheory.Sheaf.H.map.{0} S.f 2 x :=
  rfl

end TopCat.SheafCohomology

end
