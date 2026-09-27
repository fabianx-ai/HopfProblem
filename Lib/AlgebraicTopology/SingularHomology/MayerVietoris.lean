/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyLongExact
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.BiprodSequence
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.ChainSequence
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallHomology
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.AffineSimplex
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalChains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalSubdivision
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Subdivision
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Support
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Mesh
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallSimplices
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence

/-!
# The Mayer–Vietoris theorem for singular homology

For two open sets `U`, `V` covering `X`, the singular chain complexes fit into a short exact
sequence `0 → C(U ∩ V) → C(U) ⊞ C(V) → C^{U,V}(X) → 0`, the inclusion of the `(U, V)`-small
chains `C^{U,V}(X)` into `C(X)` is a quasi-isomorphism (the small simplices theorem, Hatcher,
*Algebraic Topology*, Proposition 2.21), and the induced long exact sequence in homology is the
Mayer–Vietoris sequence (Hatcher, §2.2).  This module re-exports the development, split by topic
into the modules of `Lib/AlgebraicTopology/SingularHomology/MayerVietoris/`:

* `SingularHomology` — the definition of singular homology: `SingularHomology Y n = H_n(Y; ℤ)`
  and `singularHomologyMap f n`;
* `HomologyLongExact`, `BiprodSequence` — the long exact homology sequence of a short exact
  sequence of chain complexes of `ℤ`-modules (`homologyLinearMap`, `connectingMap`,
  `exact_at_leftHomology`, …) and its form with a biproduct as middle term;
* `SmallChains`, `ChainSequence`, `SmallHomology` — supported and `(U, V)`-small chains
  (`smallComplex`, `smallInclusion`), the short exact sequence `chainSequence` with
  `chainSequence_shortExact`, and its homology sequence (`small_exact_at_*`);
* `AffineSimplex`, `FormalChains`, `FormalSubdivision`, `Subdivision` — affine simplices,
  formal (linear) chains with cone and boundary, barycentric subdivision of formal chains with
  its chain homotopy to the identity, and the subdivision `subdivision X k n` of singular chains
  with `subdivisionHomotopy`;
* `Support`, `Mesh`, `SmallSimplices` — supports of formal chains, the mesh estimate
  `meshFactor n = n/(n+1)` with the Lebesgue number `exists_lebesgue_number_two`, and the
  small simplices theorem `smallInclusion_quasiIso` with `smallHomologyEquiv`;
* `Sequence` — the Mayer–Vietoris sequence: `leftHomologyMap`, `rightHomologyMap`,
  `connectingHomomorphism`, and its exactness `exact_at_intersection`, `exact_at_pair`,
  `exact_at_ambient`.

All declarations live in the namespace `SingularMayerVietoris`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1 Proposition 2.21 and §2.2

## Tags

Mayer–Vietoris, barycentric subdivision, small simplices, long exact sequence
-/
