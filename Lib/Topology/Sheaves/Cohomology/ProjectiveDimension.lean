/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Sheaf cohomology and projective dimension

Mathlib defines integral sheaf cohomology as Ext from the constant integral sheaf, with Ext
derived in the coefficient variable. Therefore uniform vanishing of the cohomology of every
abelian sheaf in degrees at least `n` is exactly the Ext-vanishing statement that the integral
unit sheaf has projective dimension less than `n`.

This is only an Ext-vanishing formulation. It neither bounds the injective dimension of the
coefficient sheaves nor asserts the existence of a finite resolution by projective sheaves.

The notion used is Mathlib's `CategoryTheory.Abelian.HasProjectiveDimensionLT`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace TopCat.Sheaf

/-- The integral unit sheaf has projective dimension less than `n` exactly when every abelian
coefficient sheaf has trivial integral sheaf cohomology in every degree at least `n`.

Here `CategoryTheory.Sheaf.H F a` is definitionally
`Ext (TopCat.ConstantSheaf.integralSheaf X) F a`, so Ext is derived in the coefficient
variable `F`. -/
theorem integralSheaf_hasProjectiveDimensionLT_iff_cohomology_subsingleton
    (X : TopCat.{u}) (n : ℕ) :
    HasProjectiveDimensionLT (TopCat.ConstantSheaf.integralSheaf X) n ↔
      ∀ (F : TopCat.Sheaf AddCommGrpCat.{u} X) (a : ℕ), n ≤ a →
        Subsingleton (CategoryTheory.Sheaf.H.{u} F a) := by
  constructor
  · intro h F a ha
    let _ : HasProjectiveDimensionLT (TopCat.ConstantSheaf.integralSheaf X) n := h
    exact HasProjectiveDimensionLT.subsingleton
      (TopCat.ConstantSheaf.integralSheaf X) n a ha F
  · intro h
    apply HasProjectiveDimensionLT.mk
    intro a ha F e
    exact (h F a ha).elim e 0

end TopCat.Sheaf
