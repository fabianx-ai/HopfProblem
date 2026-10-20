# Cells of the subdivided boundary of the three-cube

The mesh-`h` subdivision of `∂[-1,1]³` (`h = 2 / N`) has three kinds of cells: the vertices (boundary
points with lattice coordinates), the edges joining a vertex to its successor in one coordinate
direction, and the squares spanned by two coordinate directions.  This module collects their
geometry, in the pieces

* `Lattice`: the uniform mesh of `[-1, 1]` and the mesh interval containing a point;
* `Cells`: the three cell families, uniqueness of presentations, relative interiors of squares,
  endpoints of edges, finiteness;
* `Faces`: the face of the cube containing a square, boundary containment criteria, squares as
  coordinate rectangles;
* `Coverage`: every boundary point lies in a square;
* `RelInterior`: relative interiors of distinct squares are disjoint;
* `SquareBoundary`: the boundary of a square is the union of its four edges;
* `Separation`: distance estimates between vertices and between edges.

This is the cubical cell structure underlying the proof that `dim Iⁿ ≤ n` by thickening the
cells of a fine subdivision.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV

## Modules

This directory replaces the former facade module `Lib.Topology.Dimension.CubeBoundaryThreeCells` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Topology.Dimension.CubeBoundaryThreeCells.Cells`
* `Lib.Topology.Dimension.CubeBoundaryThreeCells.Coverage`
* `Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces`
* `Lib.Topology.Dimension.CubeBoundaryThreeCells.Lattice`
* `Lib.Topology.Dimension.CubeBoundaryThreeCells.RelInterior`
* `Lib.Topology.Dimension.CubeBoundaryThreeCells.Separation`
* `Lib.Topology.Dimension.CubeBoundaryThreeCells.SquareBoundary`
