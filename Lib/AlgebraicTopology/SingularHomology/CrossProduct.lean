/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Multilinear
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Formal
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Affine
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Chain
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.HomologyDescent
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Homology
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Swap
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Associator
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Naturality

/-!
# The singular cross product

For topological spaces `X` and `Y` (in `Type`), the cross product of singular chains over `ℤ` and
the induced bilinear map on homology

* `SingularHomology.crossProductHomology X Y n :
  (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
  (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
  (SingularChains.singularComplex (X × Y)).homology (n + 1)`,

with its naturality, graded commutativity and associativity.  This is Hatcher's cross product
`H_p(X) ⊗ H_q(Y) → H_{p+q}(X × Y)` (Hatcher, *Algebraic Topology*, §3.B) with the left degree
fixed to `p = 1` (and `p = 2` where the left factor is itself a product), which is not the
general statement.

This module only imports the pieces of the construction:

* `CrossProduct.Multilinear` — `ℤ`-bilinear and trilinear plumbing, lifts of simplex-wise maps
  to chains, and the two `Module ℤ` instances used as local instances throughout.
* `CrossProduct.Formal` — the formal cross products of a point, an edge and a triangle with a
  simplex (the triangulations of `Δᵖ × Δ^q`, `p ≤ 2`) and their Leibniz laws.
* `CrossProduct.Affine` — affine simplices and affine chain maps in products `Δᵖ × Δ^q` and
  `Δᵖ × (Δ^q × Δʳ)` of standard simplices.
* `CrossProduct.Chain` — the chain-level cross products in left degrees `0`, `1`, `2`
  (`SingularHomology.crossProductEdge`, `.crossProductTriangle`) and the Leibniz rule.
* `CrossProduct.HomologyDescent` — descending a map on cycles to homology.
* `CrossProduct.Homology` — `SingularHomology.crossProductHomology` and its degenerations at `n = 0`.
* `CrossProduct.Swap` — graded commutativity, and the left-degree-two product
  `SingularHomology.crossProductHomologyTwoOne`.
* `CrossProduct.Associator` — associativity and cyclicity of the triple product of `1`-classes.
* `CrossProduct.Naturality` — naturality of the homology cross product.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.B

## Tags

singular homology, cross product, Künneth
-/
