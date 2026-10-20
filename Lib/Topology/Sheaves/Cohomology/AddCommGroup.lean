/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Additive group structure on sheaf cohomology

## Main results

* `CategoryTheory.Sheaf.instAddCommGroupH`: `CategoryTheory.Sheaf.H F n` is an additive
  commutative group, for a sheaf of abelian groups `F` on a topological space.

## Implementation notes

This is **not** a new theorem.  `CategoryTheory.Sheaf.H F n` is by definition the `Ext`-group
`CategoryTheory.Abelian.Ext _ F n` (Mathlib,
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`, where `H` is an `abbrev`), and the
group structure is Mathlib's `CategoryTheory.Abelian.Ext.instAddCommGroup`
(`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`).  The proof term below is that
instance and nothing else.

The declaration exists only to make that instance available for sheaves whose type is spelled
`TopCat.Sheaf`.  `Sheaf.H` is stated for the site-level `CategoryTheory.Sheaf J C`, while
Mathlib's `TopCat.Sheaf C X` is a non-reducible `def` for
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`
(`Mathlib/Topology/Sheaves/Sheaf.lean`).  At instance transparency the unifier therefore cannot
identify the two, `AddCommGroup (Sheaf.H F n) =?= AddCommGroup (Ext _ _ _)` fails for
`F : TopCat.Sheaf AddCommGrpCat X`, and Mathlib's instance does not fire: removing this
registration and calling Mathlib's instance at the use sites makes `Lib` fail with
`failed to synthesize Add (Sheaf.H Q 0)` in
`Lib/Topology/Sheaves/Cohomology/ShortExactDegreeOne.lean` and in
`Lib/Topology/Sheaves/FiniteClosedPushforward/Cohomology.lean`; that attempt is recorded in
`Lib/reports/round-7/names/RECEIPT.md`.  Nothing upstream is at fault: the same goal is
synthesized by Mathlib's instance alone as soon as the sheaf is typed as
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`, or `TopCat.Sheaf` is made
locally reducible.  Until `Lib` switches its sheaves to the site-level spelling this file is
load-bearing and must not be deleted.

The declaration is universe-polymorphic: `X : TopCat.{u}` with `AddCommGrpCat.{u}`
coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace CategoryTheory.Sheaf

/-- `Sheaf.H F n`, the degree-`n` cohomology of a sheaf of abelian groups on a topological
space, is an additive commutative group: it is an `Ext`-group, so this is Mathlib's
`CategoryTheory.Abelian.Ext.instAddCommGroup`, registered here for a sheaf whose type is
spelled `TopCat.Sheaf`. -/
instance instAddCommGroupH {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{u} F n) :=
  Ext.instAddCommGroup

end CategoryTheory.Sheaf
