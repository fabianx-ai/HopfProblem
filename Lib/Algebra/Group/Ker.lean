/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Kernel inclusion and constancy on fibres

Mathlib packages descent along a surjective group homomorphism as
`MonoidHom.liftOfSurjective`, whose data is a homomorphism `g` subject to `f.ker ≤ g.ker`
(`Mathlib/Algebra/Group/Subgroup/Basic.lean`).  The elementary translation between that
kernel inclusion and constancy of `g` on the fibres of `f` is not stated there; this file
supplies the direction that is used when an overlap character descends across a surjective
filling map.

## Main results

* `MonoidHom.apply_eq_apply_of_ker_le`: if `f.ker ≤ g.ker` then `f a = f b` implies
  `g a = g b`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

namespace MonoidHom

/-- A kernel inclusion makes a homomorphism constant on the fibres of another one: if every
element killed by `f` is killed by `g`, then `g` takes equal values on any two elements with
the same image under `f`. -/
theorem apply_eq_apply_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hker : f.ker ≤ g.ker) (a b : A) (hab : f a = f b) :
    g a = g b := by
  have hk : a * b⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv, hab, mul_inv_cancel]
  have hg := hker hk
  rw [MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv] at hg
  exact eq_of_mul_inv_eq_one hg

end MonoidHom
