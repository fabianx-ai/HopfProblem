REFS = """## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/"""

DOCS['Lattice'] = """/-!
# The uniform mesh of `[-1, 1]`

For `N > 0` and `h = 2 / N`, the mesh lattice `lattice N h` is the set of points `-1 + k h` with
`0 ≤ k ≤ N`.  It lies in `[-1, 1]`, contains both endpoints, has exactly `N + 1` points, distinct
points are at least `h` apart, and every lattice point `t ≤ 1 - h` has the successor `t + h`.

Every `t ∈ [-1, 1]` lies in a mesh interval `[a, a + h]` whose lower endpoint `a` is a lattice point
different from `1`: take `a = -1 + k h` with `k = min ⌊(t + 1) / h⌋ (N - 1)` (the floor index,
clipped so that `t = 1` falls into the last interval).

This is the one-dimensional subdivision from which the cubical subdivision of `∂[-1,1]³` is built.

""" + REFS

DOCS['Cells'] = """/-!
# Vertices, edges and squares of the subdivided boundary of the three-cube

The mesh-`h` subdivision of `∂[-1,1]³ ⊆ ℝ³` (`h = 2 / N`) has three families of cells:

* `vertices N h`: boundary points all of whose coordinates are mesh lattice points;
* `edges N h`: segments `[v, v + h e_j]` from a vertex `v` with `v j ≤ 1 - h` lying in the boundary;
* `squares N h`: squares `v + [0, h] e_j + [0, h] e_k`, `j < k`, from a vertex with room in both
  directions, lying in the boundary.

For positive mesh a cell determines its presentation: the initial vertex is the unique
coordinatewise lower corner of the cell, and the directions are the coordinates that vary on it.
Hence the relative interior `squareRelInterior` of a square and the endpoint set `edgeEndpoints`
of an edge, defined through a chosen presentation, agree with the ones of every presentation.
Each of the three families is finite, and the endpoints of an edge are vertices.

""" + REFS

DOCS['Faces'] = """/-!
# Mesh cells in the faces of the three-cube

A mesh square `v + [0, h] e_j + [0, h] e_k` of `∂[-1,1]³` keeps its third coordinate `i` fixed;
it lies in the boundary if and only if `|v i| = 1`, and then it lies in the face `{x | x i = v i}`,
which is the unique face containing it.  Likewise an edge lies in the boundary as soon as one of
its two fixed coordinates is `±1`.  The closed and relative-open squares are the coordinate
rectangles `{x i = v i, x j ∈ [v j, v j + h], x k ∈ [v k, v k + h]}` (open intervals for the
relative interior); `square_coordinate_description` collects this for every member of
`squares N h`.

""" + REFS

DOCS['Coverage'] = """/-!
# Every boundary point of the three-cube lies in a mesh square

A point `x` of `∂[-1,1]³` has a coordinate `x i = ±1`; keeping it and replacing the other two
coordinates by the lower endpoints of their mesh intervals gives a vertex from which a mesh square
containing `x` starts (`exists_square_mem`).

""" + REFS

DOCS['RelInterior'] = """/-!
# Relative interiors of distinct mesh squares are disjoint

Two mesh squares of `∂[-1,1]³` whose relative interiors meet are equal
(`square_eq_of_relInterior_inter_nonempty`): a common relative-interior point determines the fixed
coordinate, the two moving directions, and, since distinct open mesh intervals with lattice lower
endpoints are disjoint, the lower corner.

""" + REFS

DOCS['SquareBoundary'] = """/-!
# The boundary of a mesh square is the union of its four edges

A point of a mesh square of `∂[-1,1]³` outside its relative interior lies on one of the four sides
`[v, v + h e_j]`, `[v, v + h e_k]`, `[v + h e_k, v + h e_k + h e_j]`, `[v + h e_j, v + h e_j + h e_k]`,
and all four sides are mesh edges (`square_boundary_edges`).

""" + REFS

DOCS['Separation'] = """/-!
# Separation of mesh vertices and mesh edges

In the mesh-`h` subdivision of `∂[-1,1]³`:

* distinct vertices are at least `h` apart in the maximum norm, hence in the Euclidean norm
  (`vertex_separation`);
* two distinct edges with a common endpoint `w` meet only in `w`, and for points `p, p'` on them
  `‖p - w‖ ≤ ‖p - p'‖` (`edge_common_endpoint_geometry`), because their directions are distinct
  signed coordinate unit vectors with nonpositive inner product;
* two distinct edges without a common endpoint are at least `h` apart
  (`edge_dist_ge_mesh_of_no_common_endpoint`).

These estimates let the cells be thickened to open sets of which only cells of different
dimensions can meet.

""" + REFS
