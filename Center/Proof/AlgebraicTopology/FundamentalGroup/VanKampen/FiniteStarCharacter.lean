/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Finset.Basic

/-!
# Finite-stage character induction for the star-attachment argument

Proof-specific: this is `Finset.induction_on` repackaged with a dependent predicate, in the shape
the project's star-attachment argument consumes it (an application supplies its group character,
surjectivity, regular-restriction invariant, local compatibility and basepoint rebasing inside
`Character` and `attach`).  Nothing about fundamental groups, van Kampen or characters occurs in
the statement, so it is not a library theorem; the reusable content is Mathlib's
`Finset.induction_on`.

Moved out of `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` by the
round-8 D-file pass (`Lib/reports/round-7/judgement/d-files.md`).
-/

noncomputable section

namespace FundamentalGroup.VanKampen

/-- Every finite attachment stage inherits an abstract character invariant from the empty stage.

`attach` is the only geometry-facing input: an application supplies there its two-open-cover
compatibility proof, its restriction invariant, and its basepoint rebase.  Thus the induction
itself depends on no concrete star, chart, residual group, or framing parameter. -/
theorem exists_stageCharacter {ι : Type*} [DecidableEq ι]
    (Basepoint : Finset ι → Type*)
    (Character : (s : Finset ι) → Basepoint s → Prop)
    (empty : ∀ x : Basepoint ∅, Character ∅ x)
    (previousBasepoint : ∀ (s : Finset ι) (_i : ι), Basepoint s)
    (attach : ∀ (s : Finset ι) (i : ι) (_hi : i ∉ s) (x : Basepoint (insert i s)),
      Character s (previousBasepoint s i) → Character (insert i s) x)
    (s : Finset ι) (x : Basepoint s) : Character s x := by
  induction s using Finset.induction_on with
  | empty => exact empty x
  | @insert i s hi ih =>
      exact attach s i hi x (ih (previousBasepoint s i))

end FundamentalGroup.VanKampen
