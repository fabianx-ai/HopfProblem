/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The Hom complex from a single object

For an object `X` and an integer-graded cochain complex `K`, this file packages the elementary
identification between the internal Hom complex from `X[0]` to `K` and the explicit complex
whose degree-`n` term is `Hom(X, Kⁿ)` and whose differential is postcomposition by `d_K`.

Mathlib already supplies the degreewise equivalence as `Cochain.fromSingleEquiv`.  The bridge
here records its compatibility with the differentials, and hence also the induced homology
isomorphism.  No derived-category or application-specific hypothesis is involved.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The explicit representable cochain complex associated to `K`: its degree-`n` object is
`Hom(X, Kⁿ)` and its differential is postcomposition by the differential of `K`. -/
def coyonedaComplex (X : C) (K : CochainComplex C ℤ) :
    CochainComplex AddCommGrpCat.{v} ℤ where
  X n := AddCommGrpCat.of (X ⟶ K.X n)
  d i j := AddCommGrpCat.ofHom
    { toFun := fun f => f ≫ K.d i j
      map_zero' := by simp
      map_add' := by intros; simp }
  shape i j hij := by
    apply AddCommGrpCat.ext
    intro f
    change f ≫ K.d i j = 0
    rw [K.shape i j hij, comp_zero]
  d_comp_d' i j k hij hjk := by
    apply AddCommGrpCat.ext
    intro f
    change (f ≫ K.d i j) ≫ K.d j k = 0
    rw [Category.assoc, K.d_comp_d i j k, comp_zero]

/-- In each degree, cochains from the single complex `X[0]` are morphisms `X ⟶ Kⁿ`. -/
def fromSingleXIso (X : C) (K : CochainComplex C ℤ) (n : ℤ) :
    (HomComplex ((singleFunctor C 0).obj X) K).X n ≅ (coyonedaComplex X K).X n :=
  (Cochain.fromSingleEquiv (K := K) (X := X) (zero_add n)).toAddCommGrpIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom complex from `X[0]` is the explicit representable complex `Hom(X, K•)`. -/
def fromSingleIso (X : C) (K : CochainComplex C ℤ) :
    HomComplex ((singleFunctor C 0).obj X) K ≅ coyonedaComplex X K :=
  HomologicalComplex.Hom.isoOfComponents
    (fromSingleXIso X K)
    (fun i j hij => by
      apply AddCommGrpCat.ext
      intro α
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective α i (zero_add i)
      simp only [ConcreteCategory.comp_apply]
      change Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk f (zero_add i)) ≫
          K.d i j =
        Cochain.fromSingleEquiv (zero_add j)
          (δ i j (Cochain.fromSingleMk f (zero_add i)))
      rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
      simp)

/-- The induced identification on cohomology. -/
def fromSingleHomologyIso (X : C) (K : CochainComplex C ℤ) (n : ℤ) :
    (HomComplex ((singleFunctor C 0).obj X) K).homology n ≅
      (coyonedaComplex X K).homology n :=
  HomologicalComplex.homologyMapIso (fromSingleIso X K) n

end CochainComplex.HomComplex
