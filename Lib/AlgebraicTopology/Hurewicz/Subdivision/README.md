# Subdivision of based cubes into simplex classes

This module re-exports the subdivision of a based `n`-cube into the based simplices of
its Kuhn (Freudenthal) cells, culminating in
`Hurewicz.NativeSubdivision.nativeCubeSubdivision_class`:
`Additive.ofMul ⟦p⟧ = ∑ e : Perm (Fin n), cubeOrientation e • basedSimplexClass (nativeBasedCubeSimplex p hp e)`
for an internally based cube `p`, a step of this development's proof of the Hurewicz theorem
(statement: Hatcher, *Algebraic Topology*, Theorem 4.32).

The development lives in the following modules, in dependency order.

* `Lib.AlgebraicTopology.Hurewicz.Subdivision.SimplexQuotient`: the simplex as a quotient
  of the cube by prefix minima (`Hurewicz.SimplexGeometry`), based simplices and their
  classes.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.CubeClass`: the class `nativeClass` of a based
  cube, the quarter turn, coordinate permutations and their sign, internally based cubes
  and the linear homotopy on a common flat.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.InsertPermutation`: the bijection
  `Perm (Fin n) × Fin (n + 1) ≃ Perm (Fin (n + 1))` by insertion of the last index.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.ChamberChart`: charts of the ordered
  chambers, their cut sequences, and the inserted chart.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.Slicing`: slicing a based cube between two
  cuts and the additivity of the class under slicing.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.ExtendedChamber`: chamber charts extended to
  a larger cube and the insertion sum.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.DuffyMap`: the Duffy cube and the ordered
  Duffy chart of a chamber.
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.SubdivisionClass`: the Kuhn cells of a based
  cube as based simplices and the subdivision identity.

## Modules

This directory replaces the former facade module `Lib.AlgebraicTopology.Hurewicz.Subdivision` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.AlgebraicTopology.Hurewicz.Subdivision.ChamberChart`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.CubeClass`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.DuffyMap`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.ExtendedChamber`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.InsertPermutation`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.SimplexQuotient`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.Slicing`
* `Lib.AlgebraicTopology.Hurewicz.Subdivision.SubdivisionClass`
