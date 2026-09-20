/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Homotopy.OpenNullhomotopy
public import Lib.Topology.Sheaves.SingularCochainSheaf.LocalKernels
public import Lib.Topology.Sheaves.SingularCochainSheaf.PrimitivesH1

/-!
# Exactness of the sheafified singular-cochain complex through degree one

On a locally contractible space the augmented complex of sheafified singular cochains
`0 → A_X → 𝒮^0 → 𝒮^1 → ⋯` is exact at `𝒮^0` and at `𝒮^1`.  This is the low-degree part of Bredon,
*Sheaf Theory* III.1 (see also Warner, *Foundations of Differentiable Manifolds and Lie Groups*
5.31): a cocycle acquires a primitive after shrinking to a neighbourhood whose inclusion is
nullhomotopic.

## Main results

* `TopCat.SingularCochainSheaf.initialComplex_exact`
* `TopCat.SingularCochainSheaf.complexSheaf_exactAt_one`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

private theorem exists_restriction_constant (hLC : LocallyContractibleSpace X)
    (U : Opens X) (x : X) (hx : x ∈ U)
    (c : (AlgebraicTopology.SingularCochains.complex U A).X 0)
    (hc : (AlgebraicTopology.SingularCochains.complex U A).d 0 1 c = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (a : A),
      (presheafAugmentation X A).app (op V) a =
        (presheaf X A 0).map (homOfLE hVU).op c := by
  obtain ⟨V, hVU, hxV, hf⟩ := TopCat.exists_open_nullhomotopic_inclusion X hLC U x hx
  obtain ⟨a, ha⟩ := nullhomotopic_pullback_closed_zero A
    ((Opens.toTopCat X).map (homOfLE hVU)).hom hf c hc
  exact ⟨V, hVU, hxV, a, ha.symm⟩

private theorem exists_restriction_primitive_one (hLC : LocallyContractibleSpace X)
    (U : Opens X) (x : X) (hx : x ∈ U)
    (c : (AlgebraicTopology.SingularCochains.complex U A).X 1)
    (hc : (AlgebraicTopology.SingularCochains.complex U A).d 1 2 c = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V)
      (b : (AlgebraicTopology.SingularCochains.complex V A).X 0),
      (AlgebraicTopology.SingularCochains.complex V A).d 0 1 b =
        (presheaf X A 1).map (homOfLE hVU).op c := by
  obtain ⟨V, hVU, hxV, hf⟩ := TopCat.exists_open_nullhomotopic_inclusion X hLC U x hx
  obtain ⟨b, hb⟩ := nullhomotopic_pullback_closed_one A
    ((Opens.toTopCat X).map (homOfLE hVU)).hom hf c hc
  exact ⟨V, hVU, hxV, b, hb⟩

/-- On a locally contractible space the constant sheaf `A_X` is the kernel of the first
coboundary `𝒮^0 → 𝒮^1`, i.e. the augmented complex is exact at `𝒮^0`. -/
theorem initialComplex_exact (hLC : LocallyContractibleSpace X) :
    (initialComplex X A).Exact := by
  let S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X) :=
    ShortComplex.mk (presheafAugmentation X A) (differential X A 0 1)
      (presheafAugmentation_d X A)
  change (S.map (sheafification X)).Exact
  apply sheafify_exact_of_local_kernels S
  intro U x hx c hc
  exact exists_restriction_constant X A hLC U x hx c hc

/-- On a locally contractible space the sheafified singular-cochain complex is exact at `𝒮^1`. -/
theorem complexSheaf_exactAt_one (hLC : LocallyContractibleSpace X) :
    (complexSheaf X A).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  let S := (complex X A).sc' 0 1 2
  change (S.map (sheafification X)).Exact
  apply sheafify_exact_of_local_kernels S
  intro U x hx c hc
  exact exists_restriction_primitive_one X A hLC U x hx c hc

end TopCat.SingularCochainSheaf
