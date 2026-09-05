/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.RepresentedOpenProjectiveDimension
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Projective-dimension propagation across two open sets

The Mayer--Vietoris short exact sequence of represented-open sheaves gives the standard
dimension bound for a union: a bound `< n` on the intersection and bounds `< n + 1` on the two
opens imply a bound `< n + 1` on their union.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.Abelian

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}}

/-- Mayer--Vietoris raises the projective-dimension bound by at most one when two opens are
united. -/
theorem hasProjectiveDimensionLT_freeOpen_sup (U V : Opens X) (n : ℕ)
    (hUV : HasProjectiveDimensionLT (freeOpen (U ⊓ V)) n)
    (hU : HasProjectiveDimensionLT (freeOpen U) (n + 1))
    (hV : HasProjectiveDimensionLT (freeOpen V) (n + 1)) :
    HasProjectiveDimensionLT (freeOpen (U ⊔ V)) (n + 1) := by
  let S := Opens.mayerVietorisSquare U V
  apply S.shortComplex_shortExact.hasProjectiveDimensionLT_X₃ n hUV
  let _ := hU
  let _ := hV
  change HasProjectiveDimensionLT (freeOpen U ⊞ freeOpen V) (n + 1)
  exact inferInstance

end TopCat.Sheaf.OpenRestriction
