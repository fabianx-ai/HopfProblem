/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Evaluating a cochain homotopy on a cocycle

A chain homotopy `h : Homotopy f g` between maps of cochain complexes of abelian groups makes
`f` and `g` differ by an explicit coboundary on cocycles: on a cocycle `x` in degree `n + 1`,
`f x = d (h x) + g x`.  This is the elementwise form of the statement that homotopic maps agree
on cohomology (Hatcher, *Algebraic Topology*, Proposition 2.21; `HomotopyEquiv.quasiIso`).

## References

* [A. Hatcher, *Algebraic topology*][hatcher02], Proposition 2.21.
* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §1.4 (chain homotopies).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex

/-- Evaluation of a cochain homotopy on a positive-degree cocycle: if `h` is a homotopy
between `f` and `g` and `x` is a cocycle in degree `n + 1`, then
`f x = d (h x) + g x`. -/
theorem homotopy_on_cocycle_succ {K L : CochainComplex AddCommGrpCat.{u} ℕ}
    {f g : K ⟶ L} (h : _root_.Homotopy f g) (n : ℕ) (x : K.X (n + 1))
    (hx : K.d (n + 1) (n + 2) x = 0) :
    f.f (n + 1) x =
      L.d n (n + 1) (h.hom (n + 1) n x) + g.f (n + 1) x := by
  have he := h.comm (n + 1)
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at he
  have hx' := congrArg (fun k : K.X (n + 1) ⟶ L.X (n + 1) => k x) he
  change f.f (n + 1) x = h.hom (n + 2) (n + 1) (K.d (n + 1) (n + 2) x) +
    L.d n (n + 1) (h.hom (n + 1) n x) + g.f (n + 1) x at hx'
  simpa only [hx, map_zero, zero_add] using hx'

end CochainComplex
