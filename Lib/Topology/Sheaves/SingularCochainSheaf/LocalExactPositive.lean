/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains.PositivePrimitives
public import Lib.Topology.Homotopy.OpenNullhomotopy
public import Lib.Topology.Sheaves.SingularCochainSheaf.LocalKernels

/-!
# Positive-degree local exactness of native singular cochains

On a locally contractible space, every positive-degree native cocycle acquires a primitive after
shrinking to a nullhomotopic neighborhood.  Exactness then passes through genuine sheafification
by the local-kernel criterion.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

open AlgebraicTopology.SingularCochains

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

private theorem exists_restriction_primitive_succ
    (hLC : LocallyContractibleSpace X) (n : ℕ)
    (U : Opens X) (x : X) (hx : x ∈ U)
    (c : (AlgebraicTopology.SingularCochains.complex U A).X (n + 1))
    (hc : (AlgebraicTopology.SingularCochains.complex U A).d
      (n + 1) (n + 2) c = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V)
      (b : (AlgebraicTopology.SingularCochains.complex V A).X n),
      (AlgebraicTopology.SingularCochains.complex V A).d n (n + 1) b =
        (presheaf X A (n + 1)).map (homOfLE hVU).op c := by
  obtain ⟨V, hVU, hxV, hf⟩ :=
    TopCat.exists_open_nullhomotopic_inclusion X hLC U x hx
  obtain ⟨b, hb⟩ := nullhomotopic_pullback_closed_succ A
    ((Opens.toTopCat X).map (homOfLE hVU)).hom hf n c hc
  exact ⟨V, hVU, hxV, b, hb⟩

/-- The sheafified native singular-cochain complex is exact in every positive degree. -/
theorem complexSheaf_exactAt_succ (hLC : LocallyContractibleSpace X) (n : ℕ) :
    (complexSheaf X A).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))]
  let S := (complex X A).sc' n (n + 1) (n + 2)
  change (S.map (sheafification X)).Exact
  apply sheafify_exact_of_local_kernels S
  intro U x hx c hc
  exact exists_restriction_primitive_succ X A hLC n U x hx c hc

end TopCat.SingularCochainSheaf
