/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ShortExactDegreeOne
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup

/-!
# Degree-one sheaf cohomology from a short exact sequence

For a short exact sequence `0 ⟶ F ⟶ G ⟶ Q ⟶ 0` of abelian sheaves with `H¹(G) = 0`, the group
`H¹(F)` vanishes exactly when the map on global sections `G(X) ⟶ Q(X)` is surjective.  This is
the low-degree portion of the long exact cohomology sequence (Hartshorne, *Algebraic Geometry*,
III.1.1A; Godement, *Topologie algébrique et théorie des faisceaux*, II.4), specialised from the
`Ext` form in `Lib.Algebra.Homology.DerivedCategory.Ext.ShortExactDegreeOne` to abelian sheaves
and the top open.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.SheafCohomology

variable {X : TopCat.{0}}

/-- Surjectivity in degree-zero sheaf cohomology is exactly surjectivity on sections over the
top open. -/
theorem hZeroMap_surjective_iff_globalSections_surjective
    {G Q : TopCat.Sheaf AddCommGrpCat.{0} X} (g : G ⟶ Q) :
    Function.Surjective (CategoryTheory.Sheaf.H.map.{0} g 0) ↔
      Function.Surjective (g.hom.app (op (⊤ : Opens X))) := by
  let eG := CategoryTheory.Sheaf.H.equiv₀.{0} G
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  let eQ := CategoryTheory.Sheaf.H.equiv₀.{0} Q
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  constructor
  · intro h q
    obtain ⟨x, hx⟩ := h (eQ.symm q)
    refine ⟨eG x, ?_⟩
    calc
      g.hom.app (op (⊤ : Opens X)) (eG x) =
          eQ (CategoryTheory.Sheaf.H.map.{0} g 0 x) :=
        CategoryTheory.Sheaf.H.equiv₀_naturality
          (show IsTerminal (⊤ : Opens X) from isTerminalTop) g x
      _ = eQ (eQ.symm q) := congrArg eQ hx
      _ = q := eQ.apply_symm_apply q
  · intro h q
    obtain ⟨s, hs⟩ := h (eQ q)
    refine ⟨eG.symm s, ?_⟩
    apply eQ.injective
    calc
      eQ (CategoryTheory.Sheaf.H.map.{0} g 0 (eG.symm s)) =
          g.hom.app (op (⊤ : Opens X)) (eG (eG.symm s)) :=
        (CategoryTheory.Sheaf.H.equiv₀_naturality
          (show IsTerminal (⊤ : Opens X) from isTerminalTop) g (eG.symm s)).symm
      _ = g.hom.app (op (⊤ : Opens X)) s :=
        congrArg (g.hom.app (op (⊤ : Opens X))) (eG.apply_symm_apply s)
      _ = eQ q := hs

/-- Low-degree exactness criterion: if the middle sheaf of a short exact sequence has zero `H¹`,
then the subsheaf has zero `H¹` exactly when the quotient map is onto on global sections. -/
theorem subsingleton_hOne_iff_globalSections_surjective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₁ 1) ↔
      Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) := by
  let P :=
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))
  let _ : Subsingleton (CategoryTheory.Abelian.Ext.{0} P S.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)›
  have hExt := CategoryTheory.Abelian.Ext.subsingleton_ext_one_iff_postcomp_g_zero_surjective
    P hS
  change
    Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₁ 1) ↔
      Function.Surjective (CategoryTheory.Sheaf.H.map.{0} S.g 0) at hExt
  exact hExt.trans (hZeroMap_surjective_iff_globalSections_surjective S.g)

end TopCat.SheafCohomology
