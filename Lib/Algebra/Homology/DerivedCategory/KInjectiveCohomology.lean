/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Cohomology computed by a K-injective complex

For a K-injective integer-graded cochain complex `K`, this file identifies morphisms in the
derived category from a single object `X[0]` to a shift of `Q(K)` with the homology of the
explicit representable complex `Hom(X, K•)`.

The result is stated as an equivalence rather than an additive equivalence because Mathlib's
current `CohomologyClass.equivOfIsKInjective` and `SmallShiftedHom.equiv` APIs expose plain
equivalences.  All intermediate homology comparisons are additive.

## References

* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein88].
* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §§10.4–10.7 (K-injective
  complexes compute derived Hom).

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Morphisms from `X[0]` to the shift `Q(K)[n]` are computed by degree-`n` cohomology of the
explicit complex `Hom(X, K•)` whenever `K` is K-injective. -/
def homEquivCoyonedaHomologyOfIsKInjective (X : C) (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsKInjective]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ
      ((CochainComplex.singleFunctor C 0).obj X) K] :
    ((singleFunctor C 0).obj X ⟶ (Q.obj K)⟦n⟧) ≃
      (CochainComplex.HomComplex.coyonedaComplex X K).homology n := by
  let e₁ := (SmallShiftedHom.equiv
    (HomologicalComplex.quasiIso C (.up ℤ)) Q
      (X := (CochainComplex.singleFunctor C 0).obj X) (Y := K) (m := n)).symm
  let e₂ :=
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
      (K := (CochainComplex.singleFunctor C 0).obj X) (L := K) (n := n) |>.symm
  let e₃ := (CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor C 0).obj X) K n).symm.toEquiv
  let e₄ := (CochainComplex.HomComplex.fromSingleHomologyIso X K n)
    |>.addCommGroupIsoToAddEquiv.toEquiv
  exact e₁.trans (e₂.trans (e₃.trans e₄))

end DerivedCategory
