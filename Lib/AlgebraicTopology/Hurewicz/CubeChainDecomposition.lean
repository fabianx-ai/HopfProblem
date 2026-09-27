/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.StandardPrism
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PermutationInsertion
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.CubeChain
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.IntervalSplit
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Concatenation
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.KuhnDecomposition
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Cycle

/-!
# The fundamental cube chain and its Kuhn decomposition

This module re-exports the singular chain of a based `n`-cube and its decomposition into
the `n!` simplices of the Kuhn (Freudenthal) triangulation,
`Hurewicz.cubeChain_eq_sum_simplices`, together with the cycle property
`Hurewicz.cubeChain_boundary` and the homology class `Hurewicz.cubeHomologyClass`
(Hatcher, *Algebraic Topology*, §3.B for the cross product, §4.2 for the Hurewicz map).

The development lives in the following modules, in dependency order.

* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization`: the prisms
  `Δ¹ × (Kuhn cell)` of the `(n + 1)`-cube, their realization by a cube map, and the
  bad-prism submodule (`Hurewicz.CubeSubdivision`).
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.StandardPrism`: the shuffle
  decomposition of the prism, the prism discrepancy, and the vanishing of the oriented
  realization on bad terms.
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PermutationInsertion`: insertion of
  an index into a permutation, its sign, and the identification of the shuffle simplices
  with the Kuhn cells of the `(n + 1)`-cube.
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.CubeChain`: the fundamental cube
  chain, the cube chain of a based cube, the currying recursion, and the low degrees.
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.IntervalSplit`: the scaled cube and
  the splitting of the interval chain.
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Concatenation`: the cube chain of a
  concatenation `GenLoop.transAt 0 p q` up to boundaries and a constant term.
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.KuhnDecomposition`: the identity
  `cubeChain p = ∑ e, cubeOrientation e • simplexChain (p ∘ cubeSimplex e)`.
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Cycle`: the cube chain is a cycle;
  the cube cycle and the cube homology class.
-/
