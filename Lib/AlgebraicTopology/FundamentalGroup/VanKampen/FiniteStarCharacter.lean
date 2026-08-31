/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Data.Finset.Basic

/-!
# Finite-stage character induction

This module contains only the finite combinatorial induction used by a star-attachment argument.
The `Character` predicate is deliberately abstract: an application packages its actual group
character, surjectivity, regular-restriction invariant, local compatibility, and basepoint rebasing
inside it.  Consequently this owner contains no chart, centre-family, puncture, or residual-group
data.
-/

@[expose] public noncomputable section

namespace Mathoverflow1973.FundamentalGroup.VanKampen

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

end Mathoverflow1973.FundamentalGroup.VanKampen
