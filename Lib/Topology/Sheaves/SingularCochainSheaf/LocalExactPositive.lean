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
# Exactness of the sheafified singular-cochain complex in positive degrees

On a locally contractible space the complex of sheafified singular cochains `𝒮^•(·; A)` is exact
in every positive degree: a cocycle acquires a primitive after shrinking to a neighbourhood whose
inclusion is nullhomotopic, and exactness passes to the sheafification because it can be checked
on local kernel lifts.  Together with exactness at `𝒮^0` this says that `𝒮^•(·; A)` is a
resolution of the constant sheaf `A_X` (Bredon, *Sheaf Theory* III.1; Warner, *Foundations of
Differentiable Manifolds and Lie Groups* 5.31).

## Main results

* `TopCat.SingularCochainSheaf.complexSheaf_exactAt_succ`
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

/-- On a locally contractible space the sheafified singular-cochain complex is exact at `𝒮^{n+1}`
for every `n` (Bredon, *Sheaf Theory* III.1). -/
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
