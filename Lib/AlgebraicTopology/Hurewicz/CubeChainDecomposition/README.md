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

## Modules

This directory replaces the former facade module `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Concatenation`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.CubeChain`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.Cycle`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.IntervalSplit`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.KuhnDecomposition`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PermutationInsertion`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.PrismRealization`
* `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.StandardPrism`
