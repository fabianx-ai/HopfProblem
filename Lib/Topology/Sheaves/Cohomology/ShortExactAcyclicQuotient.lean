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

For a short exact sequence `0 ⟶ F ⟶ G ⟶ Q ⟶ 0` of abelian sheaves, vanishing of `H¹(Q)` and
`H²(Q)` makes the induced cohomology map `H²(F) ⟶ H²(G)` an additive equivalence.  This is the
degree-two window of the long exact cohomology sequence (Hartshorne, *Algebraic Geometry*,
III.1.1A), specialised from the `Ext` form in
`Lib.Algebra.Homology.DerivedCategory.Ext.ShortExactAcyclicQuotient` to abelian sheaves.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian TopologicalSpace

namespace TopCat.SheafCohomology

variable {X : TopCat.{0}}

/-- A sheaf is acyclic in degrees one and two when both `H¹` and `H²` vanish.  This is the
hypothesis of the degree-two comparison below. -/
structure AcyclicInDegreesOneTwo
    (Q : TopCat.Sheaf AddCommGrpCat.{0} X) : Prop where
  /-- The degree-one cohomology of `Q` vanishes. -/
  hOne : Subsingleton (CategoryTheory.Sheaf.H.{0} Q 1)
  /-- The degree-two cohomology of `Q` vanishes. -/
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

/-- The degree-two comparison equivalence is the map induced by the subobject inclusion. -/
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
