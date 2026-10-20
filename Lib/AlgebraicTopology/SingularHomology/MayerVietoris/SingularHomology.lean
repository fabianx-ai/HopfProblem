/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyLongExact

/-!
# Singular homology

`SingularMayerVietoris.SingularHomology Y n` is the `n`-th integral singular homology module
`H_n(Y; ℤ)` of a topological space `Y`: the `n`-th homology of the singular chain complex
`SingularChains.singularComplex Y` (Hatcher, *Algebraic Topology*, §2.1; cf. Mathlib's
`AlgebraicTopology.singularChainComplexFunctor`).  A continuous map `f : C(Y, Z)` induces
`singularHomologyMap f n : H_n Y →ₗ[ℤ] H_n Z`, the homology map of the chain map
`SingularChains.singularChainMap f`; in degree `1` it is `SingularChains.inducedHomology f`.

These two abbreviations are the library's definition of singular homology; the remaining
modules of this directory build the Mayer–Vietoris sequence for it.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-- The singular homology module of a space. -/
abbrev SingularMayerVietoris.SingularHomology (Y : Type) [TopologicalSpace Y] (n : ℕ) :=
  (SingularChains.singularComplex Y).homology n

/-- The homology map induced by a continuous map. -/
abbrev SingularMayerVietoris.singularHomologyMap {Y Z : Type} [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) (n : ℕ) :
    SingularHomology Y n →ₗ[ℤ] SingularHomology Z n :=
  homologyLinearMap (SingularChains.singularChainMap f) n

/-- The induced map in degree `n + 1` formulation. -/
@[simp]
theorem SingularMayerVietoris.singularHomologyMap_one {Y Z : Type} [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) :
    singularHomologyMap f 1 = SingularChains.inducedHomology f :=
  rfl
