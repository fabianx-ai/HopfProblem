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
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`), and the group structure is Mathlib's
`CategoryTheory.Abelian.Ext.instAddCommGroup`
(`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean`).  The proof term below is
that instance and nothing else.

The declaration exists only to register it under the `Sheaf.H` head symbol.  Typeclass
resolution does not see through `Sheaf.H` to `Ext` in this development: removing this
registration and calling Mathlib's instance at the use sites makes `Lib` fail with
`failed to synthesize Add (Sheaf.H Q 0)` in
`Lib/Topology/Sheaves/Cohomology/ShortExactDegreeOne.lean` and in
`Lib/Topology/Sheaves/FiniteClosedPushforward/Cohomology.lean`; that attempt is recorded in
`Lib/reports/round-7/names/RECEIPT.md`.  Closing the gap is an upstream change to `Sheaf.H`,
so until then this file is load-bearing and must not be deleted.

The universes are fixed at `TopCat.{0}` and `AddCommGrpCat.{0}` because that is the only shape
used downstream; nothing in the statement depends on the restriction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

/-- `Sheaf.H F n`, the degree-`n` cohomology of a sheaf of abelian groups on a topological
space, is an additive commutative group: it is an `Ext`-group, so this is Mathlib's
`CategoryTheory.Abelian.Ext.instAddCommGroup` registered under the `Sheaf.H` head symbol. -/
instance instAddCommGroupH {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) :=
  Ext.instAddCommGroup

end CategoryTheory.Sheaf
