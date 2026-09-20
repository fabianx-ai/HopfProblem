/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Centralizers from monodromy in a principal-cover fibre

If a loop acts by the same deck transformation `a` at two points `e`, `e'` of one fibre of a
principal (normal) covering, then the deck transformation `h` carrying `e` to `e'` commutes with
`a`: the monodromy of a loop and the deck group interact through conjugation.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §1.3 (deck transformations of a normal
  covering and the monodromy action of the fundamental group on a fibre, Prop. 1.39).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

namespace IsQuotientCoveringMap

universe uG uE uX

variable {G : Type uG} {E : Type uE} {X : Type uX}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E] {p : E → X}

/-- If a loop acts at `e` and at `h • e` by the same deck transformation `a`, then `a` and `h`
commute. -/
theorem commute_of_monodromy_eq_toPermFiber
    (hp : IsQuotientCoveringMap p G) {x : X}
    (e : p ⁻¹' {x}) (gamma : FundamentalGroup X x) (a h : G)
    (he : hp.isCoveringMap.monodromy gamma e = hp.toPermFiber x a e)
    (hhe : hp.isCoveringMap.monodromy gamma (hp.toPermFiber x h e) =
      hp.toPermFiber x a (hp.toPermFiber x h e)) :
    Commute a h := by
  have hcomm := hp.monodromy_toPermFiber
    (g := h) (γ := gamma) (e := e)
  rw [he] at hcomm
  have heq :
      hp.toPermFiber x a (hp.toPermFiber x h e) =
        hp.toPermFiber x h (hp.toPermFiber x a e) :=
    hhe.symm.trans hcomm
  apply hp.toPermFiber_ext x e
  simpa only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply] using heq

/-- If a loop acts by the same deck transformation `a` at two points `e`, `e'` of one fibre, then
`a` commutes with the deck transformation carrying `e` to `e'`. -/
theorem commute_fiberEquivGroup_of_monodromy_eq
    (hp : IsQuotientCoveringMap p G) {x : X}
    (e e' : p ⁻¹' {x}) (gamma : FundamentalGroup X x) (a : G)
    (he : hp.isCoveringMap.monodromy gamma e = hp.toPermFiber x a e)
    (he' : hp.isCoveringMap.monodromy gamma e' = hp.toPermFiber x a e') :
    Commute a (hp.fiberEquivGroup e e') := by
  let h := hp.fiberEquivGroup e e'
  apply hp.commute_of_monodromy_eq_toPermFiber e gamma a h he
  have hbase : hp.toPermFiber x h e = e' := by
    apply Subtype.ext
    exact hp.fiberEquivGroup_smul_self e
  simpa only [hbase] using he'

end IsQuotientCoveringMap
