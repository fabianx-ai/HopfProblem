/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolution

/-!
# Finite degree-two and degree-three views of an acyclic resolution

These structures retain the original finite API.  The connecting-isomorphism engine is owned by
`AcyclicResolution`; the compatibility module shows that these finite staircases are the first two
specializations of the indexed all-degree construction.

## References

* [R. Hartshorne, *Algebraic geometry*][hartshorne77], Chapter III, Proposition 1.2A
  (an acyclic resolution computes the derived functors); here degrees two and three.
* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §2.4.

-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

set_option genSizeOf false in
/-- An augmented resolution exact through degree two, presented as its degree-one truncation and
one further exact differential. -/
structure AcyclicResolutionH2 where
  trunc : AcyclicResolutionH1 (C := C)
  X₄ : C
  d₂ : trunc.complex.X₃ ⟶ X₄
  zero₂ : trunc.complex.g ≫ d₂ = 0
  exact₂ : (ShortComplex.mk trunc.complex.g d₂ zero₂).Exact

namespace AcyclicResolutionH2

variable (R : AcyclicResolutionH2 (C := C))

/-- The once-shifted augmented resolution. -/
def tail : AcyclicResolutionH1 (C := C) where
  F := R.trunc.cycles
  complex := ShortComplex.mk R.trunc.complex.g R.d₂ R.zero₂
  ι := kernel.ι R.trunc.complex.g
  zero := kernel.condition _
  initial_exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  exact := R.exact₂
  mono_ι := inferInstance

variable (P : C)

/-- The degree-two finite staircase comparison. -/
def extTwoIso
    [Subsingleton (Ext P R.trunc.complex.X₁ 1)]
    [Subsingleton (Ext P R.trunc.complex.X₁ 2)]
    [Subsingleton (Ext P R.trunc.complex.X₂ 1)] :
    AddCommGrpCat.of (Ext P R.trunc.F 2) ≅
      ((R.tail).extZeroComplex P).homology := by
  let _ : Subsingleton (Ext P (R.tail).complex.X₁ 1) :=
    ‹Subsingleton (Ext P R.trunc.complex.X₂ 1)›
  exact (connectingIso P R.trunc.first_shortExact 1).symm ≪≫
    (R.tail).extOneIso P

end AcyclicResolutionH2

set_option genSizeOf false in
/-- An augmented resolution exact through degree three. -/
structure AcyclicResolutionH3 extends AcyclicResolutionH2 (C := C) where
  X₅ : C
  d₃ : toAcyclicResolutionH2.X₄ ⟶ X₅
  zero₃ : toAcyclicResolutionH2.d₂ ≫ d₃ = 0
  exact₃ : (ShortComplex.mk toAcyclicResolutionH2.d₂ d₃ zero₃).Exact

namespace AcyclicResolutionH3

variable (R : AcyclicResolutionH3 (C := C))

/-- The once-shifted degree-two resolution. -/
def tail : AcyclicResolutionH2 (C := C) where
  trunc := R.toAcyclicResolutionH2.tail
  X₄ := R.X₅
  d₂ := R.d₃
  zero₂ := R.zero₃
  exact₂ := R.exact₃

variable (P : C)

/-- The degree-three finite staircase comparison. -/
def extThreeIso
    [Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₁ 2)]
    [Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₁ 3)]
    [Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₂ 1)]
    [Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₂ 2)]
    [Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₃ 1)] :
    AddCommGrpCat.of (Ext P R.toAcyclicResolutionH2.trunc.F 3) ≅
      ((R.tail).tail.extZeroComplex P).homology := by
  let _ : Subsingleton (Ext P (R.tail).trunc.complex.X₁ 1) :=
    ‹Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₂ 1)›
  let _ : Subsingleton (Ext P (R.tail).trunc.complex.X₁ 2) :=
    ‹Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₂ 2)›
  let _ : Subsingleton (Ext P (R.tail).trunc.complex.X₂ 1) :=
    ‹Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₃ 1)›
  exact
    (connectingIso P R.toAcyclicResolutionH2.trunc.first_shortExact 2).symm ≪≫
      (R.tail).extTwoIso P

end AcyclicResolutionH3

end CategoryTheory.Abelian.Ext
