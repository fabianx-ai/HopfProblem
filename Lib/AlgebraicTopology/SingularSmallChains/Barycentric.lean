/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.HomotopySupport
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.SubdivisionSupport
public import Lib.AlgebraicTopology.SingularSmallChains.SubdivisionCriterion

/-!
# The cover-small chain theorem by barycentric subdivision

For every arbitrary open cover, the literal inclusion of cover-small native singular chains is
a quasi-isomorphism and a chain-homotopy equivalence.  The proof uses the actual barycentric
subdivision operator, its carrier-preserving homotopy, compact-simplex mesh contraction, and the
finite support of native chains.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Set

namespace TopCat.SingularSmallChains.Barycentric

variable {X : Type} [TopologicalSpace X] {I : Type}

/-- The actual barycentric operators supply the minimal subdivision data for every open cover. -/
def subdivisionData (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) : TopCat.SingularSmallChains.SubdivisionData U where
  subdivision := subdivision X
  homotopy := subdivisionHomotopy X
  subdivision_boundary := subdivision_boundary
  homotopy_boundary_of_cycle := subdivisionHomotopy_boundary_of_cycle
  eventually_small n c := by
    obtain ⟨N, hN⟩ := eventually_subdivision_mem_small U hU hcover n c
    exact ⟨N, hN N le_rfl⟩
  homotopy_small := subdivisionHomotopy_mem_small U

/-- The literal cover-small inclusion is a quasi-isomorphism for every arbitrary open cover. -/
theorem inclusion_quasiIso (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) :
    QuasiIso (TopCat.SingularSmallChains.inclusion U) :=
  TopCat.SingularSmallChains.inclusion_quasiIso_of_subdivisionData U
    (subdivisionData U hU hcover)

/-- The same literal inclusion is the forward map of a chain-homotopy equivalence. -/
def smallChainHomotopyEquiv (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) :
    HomotopyEquiv (TopCat.SingularSmallChains.complex U)
      (AlgebraicTopology.SingularCochains.chains X) :=
  TopCat.SingularSmallChains.inclusionHomotopyEquivOfSubdivisionData U
    (subdivisionData U hU hcover)

@[simp]
theorem smallChainHomotopyEquiv_hom (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) :
    (smallChainHomotopyEquiv U hU hcover).hom = TopCat.SingularSmallChains.inclusion U := rfl

end TopCat.SingularSmallChains.Barycentric
