# The prism operator and the degree-two Hurewicz theorem

This module re-exports the pieces of the former monolithic file, which are now the modules of
`Lib.AlgebraicTopology.Hurewicz.PrismOperator.*`:

* `CrossProductPoint`: degree-zero cross products with a point chain are pushforwards along
  the insertions.
* `HurewiczMap`: the square chain of a based square and the Hurewicz map
  `Hurewicz.DegreeTwo.hurewiczMap : Additive (π_ 2 X x) →ₗ[ℤ] H_2 X`.
* `MapGenLoop`: postcomposition of generalized loops by a continuous map.
* `Basic`: the prism operator `∂P + P∂ = H₁# - H₀#` (Hatcher, Thm 2.10) and its
  simplex-family version for face-compatible homotopies.
* `VertexEdgeStraightening`: straightening vertices and edges of singular simplices in a simply
  connected space, coherently with faces.
* `BasedTriangle`: based triangles, their `π_2`-classes, and the normalized `2`-cycle.
* `SquareRotation`: a quarter-turn rotation of a based square preserves its class.
* `BasedTetrahedron`: based tetrahedra, quadrilateral fillings, cyclic symmetry of based triangles.
* `SquareSubdivision`: subdividing a based square along the diagonal splits its class.
* `TetrahedronRelation`: the alternating sum of the face classes of a based tetrahedron vanishes.
* `TwoTriangles`: the square chain is the difference of two singular triangles.
* `HurewiczInverse`: the inverse map `H_2 X → Additive (π_ 2 X x)` and
  `hurewiczMap ∘ hurewiczInverse = id`.
* `NormalizedSquare`: a based square is homotopic to a pair of based triangles glued along the
  diagonal.
* `SubdivisionTriangleClass`: the class of a glued pair of based triangles and
  `hurewiczInverse ∘ hurewiczMap = id`.
* `DegreeTwo`: the degree-two Hurewicz theorem
  `Hurewicz.degreeTwoLinearEquiv : Additive (π_ 2 X x) ≃ₗ[ℤ] H_2 X` (Hatcher, Thm 4.32).
* `ComposeHomotopies`: composition of simplex-indexed homotopy families.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorems 2.10 and 4.32.

## Tags

Hurewicz, prism operator, simplex, homotopy, simply connected

## Modules

This directory replaces the former facade module `Lib.AlgebraicTopology.Hurewicz.PrismOperator` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTetrahedron`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.BasedTriangle`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.Basic`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.ComposeHomotopies`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.CrossProductPoint`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.DegreeTwo`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.MapGenLoop`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.NormalizedSquare`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareRotation`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.SquareSubdivision`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.SubdivisionTriangleClass`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.TetrahedronRelation`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.TwoTriangles`
* `Lib.AlgebraicTopology.Hurewicz.PrismOperator.VertexEdgeStraightening`
