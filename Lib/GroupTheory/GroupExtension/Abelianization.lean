/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.GroupTheory.Abelianization.SemidirectProduct
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Abelianization of split group extensions

This file identifies the abelianization of a split group extension with the product of the
abelianization of the quotient and the coinvariants of the induced action on the abelianization of
the kernel.

It is a direct corollary of `GroupExtension.Splitting.semidirectProductMulEquiv` and
`SemidirectProduct.abelianizationMulEquiv`.

## References

* [Kenneth S. Brown, *Cohomology of Groups*][brown1982], Ch. VII §6, Cor. VII.6.4 (the
  low-degree Lyndon–Hochschild–Serre sequence, whence `H₁` of a split extension).
-/

@[expose] public section

universe u v w

namespace GroupExtension.Splitting

noncomputable section

variable {K : Type u} {E : Type v} {Q : Type w} [Group K] [Group E] [Group Q]
variable {S : GroupExtension K E Q}

/-- The abelianization of a split extension is the product of the quotient's abelianization and
the coinvariants of the induced action on the kernel's abelianization. -/
noncomputable def abelianizationMulEquiv (s : S.Splitting) :
    Abelianization E ≃*
      Abelianization Q ×
        Multiplicative (SemidirectProduct.AbelianizationCoinvariants s.conjAct) :=
  s.semidirectProductMulEquiv.symm.abelianizationCongr.trans
    (SemidirectProduct.abelianizationMulEquiv s.conjAct)

end


end GroupExtension.Splitting
