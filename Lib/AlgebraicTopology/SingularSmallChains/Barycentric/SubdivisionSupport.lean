/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.ArbitraryCoverMesh
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.RealizationSupport
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.Subdivision

/-! # Eventual cover-smallness of native barycentric subdivision -/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Set

namespace TopCat.SingularSmallChains.Barycentric

variable {X : Type} [TopologicalSpace X] {I : Type}

/-- Native barycentric subdivision preserves cover-small chains for an arbitrary family. -/
theorem subdivision_mem_small (U : I → Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ TopCat.SingularSmallChains.submodule U n) :
    subdivision X k n c ∈ TopCat.SingularSmallChains.submodule U n := by
  apply singularLinearMap_mem_of_small U n (subdivision X k n)
    (TopCat.SingularSmallChains.submodule U n) c hc
  intro sigma hsigma
  rw [subdivision_simplex]
  exact realizedChain_mem_small U n n sigma hsigma _

/-- Every singular simplex eventually subdivides into chains small for an arbitrary open cover
of its image. -/
theorem eventually_subdivision_simplex_mem_small (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (n : ℕ)
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n)
    (hcover : range sigma ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∀ k ≥ N,
      subdivision X k n (TopCat.SingularSmallChains.simplexChain X n sigma) ∈
        TopCat.SingularSmallChains.submodule U n := by
  obtain ⟨N, hN⟩ :=
    ArbitraryCover.simplex_formalSubdivision_eventually_small U sigma hU hcover
  refine ⟨N, ?_⟩
  intro k hk
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U n n sigma
  intro v hv
  exact hN k hk (formalSimplex (stdVertices n)) v hv

/-- A uniform subdivision stage works for the finite simplex support of every native chain; the
open cover itself may be infinite. -/
theorem eventually_subdivision_mem_small (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)
    (n : ℕ) (c : Chains X n) :
    ∃ N : ℕ, ∀ k ≥ N,
      subdivision X k n c ∈ TopCat.SingularSmallChains.submodule U n := by
  classical
  have hc : ∀ sigma ∈
      (TopCat.SingularSmallChains.chainsEquivFinsupp X n c).support,
      range sigma ⊆ ⋃ i, U i := by
    intro sigma hsigma
    rw [hcover]
    exact subset_univ _
  obtain ⟨N, hN⟩ := ArbitraryCover.finite_family_formalSubdivision_eventually_small U
    (TopCat.SingularSmallChains.chainsEquivFinsupp X n c).support hU hc
  refine ⟨N, ?_⟩
  intro k hk
  apply singularLinearMap_mem_of_support n (subdivision X k n)
    (TopCat.SingularSmallChains.submodule U n) c
  intro sigma hsigma
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U n n sigma
  intro v hv
  exact hN k hk sigma hsigma (formalSimplex (stdVertices n)) v hv

end TopCat.SingularSmallChains.Barycentric
