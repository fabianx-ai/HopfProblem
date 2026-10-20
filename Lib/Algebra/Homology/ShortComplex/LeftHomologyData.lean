/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Homology data from exact kernel and cokernel presentations

Mathlib builds `ShortComplex.LeftHomologyData` from a limit kernel fork
(`LeftHomologyData.ofIsLimitKernelFork`) and a colimit cokernel cofork
(`LeftHomologyData.ofIsColimitCokernelCofork`).  This file combines the two: in an abelian
category, a factorization `S.f = a ≫ i` with `i` a monomorphism, `p` an epimorphism and the two
short complexes `K ⟶ X₂ ⟶ X₃` and `X₁ ⟶ K ⟶ H` exact already exhibits `H` as the homology of `S`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exact kernel and cokernel presentations produce actual left homology data. -/
def leftHomologyDataOfExact (S : ShortComplex C) {K H : C}
    (i : K ⟶ S.X₂) (a : S.X₁ ⟶ K) (p : K ⟶ H)
    (wi : i ≫ S.g = 0) (wa : a ≫ i = S.f) (wp : a ≫ p = 0)
    (hi : (ShortComplex.mk i S.g wi).Exact)
    (hp : (ShortComplex.mk a p wp).Exact) [Mono i] [Epi p] :
    S.LeftHomologyData := by
  let hk : IsLimit (KernelFork.ofι i wi) := hi.fIsKernel
  have hfac : hk.lift (KernelFork.ofι S.f S.zero) = a := by
    apply (cancel_mono i).mp
    exact (Fork.IsLimit.lift_ι hk).trans wa.symm
  refine
    { K := K
      H := H
      i := i
      π := p
      wi := wi
      hi := hk
      wπ := by rw [hfac]; exact wp
      hπ := ?_ }
  apply CokernelCofork.IsColimit.ofπ'
  intro Z k hk'
  exact CokernelCofork.IsColimit.desc' hp.gIsCokernel k (by
    change a ≫ k = 0
    exact (congrArg (fun l => l ≫ k) hfac).symm.trans hk')

end CategoryTheory.ShortComplex
