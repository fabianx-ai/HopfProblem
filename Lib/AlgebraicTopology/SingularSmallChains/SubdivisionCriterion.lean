/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.HomologicalComplex.ChainCycleLift
public import Lib.AlgebraicTopology.SingularSmallChains.Projective

/-!
# The minimal subdivision API for cover-small chains

Only four geometric facts about subdivision are needed: it commutes with boundaries, its homotopy
gives the cycle identity, every finite chain eventually becomes cover-small, and the homotopy
preserves cover-small chains.  These facts imply that the literal cover-small inclusion is a
quasi-isomorphism and hence, by projectivity, a chain-homotopy equivalence.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Set

namespace TopCat.SingularSmallChains

/-- Exactly the four chain-level consequences of barycentric subdivision needed by the
cover-small theorem. -/
structure SubdivisionData {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X) where
  subdivision (k n : ℕ) :
    (AlgebraicTopology.SingularCochains.chains X).X n →ₗ[ℤ]
      (AlgebraicTopology.SingularCochains.chains X).X n
  homotopy (k n : ℕ) :
    (AlgebraicTopology.SingularCochains.chains X).X n →ₗ[ℤ]
      (AlgebraicTopology.SingularCochains.chains X).X (n + 1)
  subdivision_boundary (k n : ℕ)
      (b : (AlgebraicTopology.SingularCochains.chains X).X (n + 1)) :
    (AlgebraicTopology.SingularCochains.chains X).d (n + 1) n (subdivision k (n + 1) b) =
      subdivision k n ((AlgebraicTopology.SingularCochains.chains X).d (n + 1) n b)
  homotopy_boundary_of_cycle (k n : ℕ)
      (c : (AlgebraicTopology.SingularCochains.chains X).X n)
      (hc : (AlgebraicTopology.SingularCochains.chains X).d n (n - 1) c = 0) :
    (AlgebraicTopology.SingularCochains.chains X).d (n + 1) n (homotopy k n c) =
      c - subdivision k n c
  eventually_small (n : ℕ)
      (c : (AlgebraicTopology.SingularCochains.chains X).X n) :
    ∃ k, subdivision k n c ∈ submodule U n
  homotopy_small (k n : ℕ)
      (c : (AlgebraicTopology.SingularCochains.chains X).X n)
      (hc : c ∈ submodule U n) : homotopy k n c ∈ submodule U (n + 1)

/-- The four subdivision facts prove that the literal cover-small inclusion is a
quasi-isomorphism. -/
theorem inclusion_quasiIso_of_subdivisionData
    {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X)
    (data : SubdivisionData U) : QuasiIso (inclusion U) := by
  apply HomologicalComplex.ChainCycleLift.quasiIso_of_injective_chain_conditions
    (inclusion U)
  · exact inclusion_f_injective U
  · intro n c hc
    obtain ⟨k, hk⟩ := data.eventually_small n c
    refine ⟨⟨data.subdivision k n c, hk⟩, data.homotopy k n c, ?_⟩
    exact data.homotopy_boundary_of_cycle k n c hc
  · intro n c hc b hb
    have hc' : (AlgebraicTopology.SingularCochains.chains X).d n (n - 1) c.1 = 0 :=
      congrArg Subtype.val hc
    have hb' : (AlgebraicTopology.SingularCochains.chains X).d (n + 1) n b = c.1 := by
      simpa only [inclusion_f_apply] using hb
    obtain ⟨k, hk⟩ := data.eventually_small (n + 1) b
    refine ⟨⟨data.subdivision k (n + 1) b + data.homotopy k n c.1,
      (submodule U (n + 1)).add_mem hk (data.homotopy_small k n c.1 c.2)⟩, ?_⟩
    apply Subtype.ext
    change (AlgebraicTopology.SingularCochains.chains X).d (n + 1) n
      (data.subdivision k (n + 1) b + data.homotopy k n c.1) = c.1
    rw [map_add, data.subdivision_boundary, hb',
      data.homotopy_boundary_of_cycle k n c.1 hc']
    rw [← add_sub_assoc, add_comm, add_sub_cancel_right]

/-- Consequently the same literal inclusion is the forward map of a chain-homotopy
equivalence. -/
def inclusionHomotopyEquivOfSubdivisionData
    {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X)
    (data : SubdivisionData U) :
    HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X) :=
  inclusionHomotopyEquivOfQuasiIso U (inclusion_quasiIso_of_subdivisionData U data)

@[simp]
theorem inclusionHomotopyEquivOfSubdivisionData_hom
    {X : Type} [TopologicalSpace X] {I : Type} (U : I → Set X)
    (data : SubdivisionData U) :
    (inclusionHomotopyEquivOfSubdivisionData U data).hom = inclusion U := rfl

end TopCat.SingularSmallChains
