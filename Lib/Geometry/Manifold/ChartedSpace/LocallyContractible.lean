/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Homotopy.LocallyContractible
public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Strong local contractibility of charted spaces

A charted space modeled on a strongly locally contractible space is strongly locally contractible.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

/-- A charted space modeled on a strongly locally contractible space is strongly locally
contractible. -/
theorem chartedSpaceStronglyLocallyContractible (H M : Type*)
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [StronglyLocallyContractibleSpace H] :
    StronglyLocallyContractibleSpace M := by
  apply StronglyLocallyContractibleSpace.of_open_neighborhoods
  intro x
  let e := (chartAt H x).symm
  refine ⟨⟨e.target, e.open_target⟩, mem_chart_source H x, ?_⟩
  let : StronglyLocallyContractibleSpace e.source :=
    e.open_source.stronglyLocallyContractibleSpace
  exact e.toHomeomorphSourceTarget.symm.isOpenEmbedding.stronglyLocallyContractibleSpace
