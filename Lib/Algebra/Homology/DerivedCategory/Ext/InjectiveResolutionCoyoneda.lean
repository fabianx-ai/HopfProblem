/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Ext from the representable complex of an injective resolution

If `I` is an injective resolution of `F`, the degree-`n` homology of the explicit complex
`Hom(X, I•)` computes `Extⁿ(X,F)`.  This file packages that comparison for the integer-graded
extension `I.cochainComplex`, including degree zero.

The construction is a direct composition of the single-source Hom-complex isomorphism,
Mathlib's Hom-complex homology comparison, and Mathlib's injective-resolution Ext comparison.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], Theorem 2.7.6.
* [R. Hartshorne, *Algebraic geometry*][hartshorne77], Chapter III, §1 (`Ext` computed from an
  injective resolution).

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.InjectiveResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {F : C} (I : InjectiveResolution F)

/-- Homology of the explicit integer-graded complex `Hom(X,I•)` is `Extⁿ(X,F)` in every
natural degree. -/
def coyonedaHomologyExtAddEquiv (X : C) (n : ℕ) :
    (CochainComplex.HomComplex.coyonedaComplex X I.cochainComplex).homology (n : ℤ) ≃+
      Ext X F n :=
  (CochainComplex.HomComplex.fromSingleHomologyIso X I.cochainComplex (n : ℤ))
      |>.symm.addCommGroupIsoToAddEquiv |>.trans
    (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex (n : ℤ)) |>.trans
    (I.extAddEquivCohomologyClass (X := X) (Y := F) (n := n)).symm

end CategoryTheory.InjectiveResolution
