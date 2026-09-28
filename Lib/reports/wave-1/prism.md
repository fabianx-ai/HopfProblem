# Wave 1 receipt — `prism`: `Lib/AlgebraicTopology/Hurewicz/PrismOperator.lean`

Base `lib/integration` at `e669bc93`; branch `wave1/prism`; commits listed at the end.
Verdict of `Lib/reports/round-7/judgement/monoliths.md`: C (two subjects in one file; the general prism
operator carried the `DegreeTwo.SimplyConnected` name; universe 0). Twins: Hatcher, *Algebraic
Topology*, Thm 2.10 (prism operator) and Thm 4.32 at `n = 2` (degree-two Hurewicz theorem).

## The cut

Every declaration of the base file (455 ranged declaration units, 464 ranged constants counting
structure fields and constructors) was moved verbatim by `split_module.py` — one run per piece against
the base file, stay set = all constants except the piece's, receipts `prism/receipt_<Piece>.json` — into
`Lib/AlgebraicTopology/Hurewicz/PrismOperator/<Piece>.lean`; `PrismOperator.lean` is a facade that
imports the sixteen pieces. Line numbers are those of the base file; "unit lines" count the moved
declaration units (docstrings, attributes and `… in` prefixes included; context lines excluded).

| piece | lines moved | declarations | textbook topic |
|---|---|---|---|
| `CrossProductPoint` | 67–118, 707–718 (59 unit lines, 4 units) | `crossProductTriangle_zero_eq_zeroRight`, `crossProductTriangle_point_right`, `crossProductEdge_point_right`, `crossPoint_left` | degree-zero cross products with a point chain are the insertion pushforwards (boundary terms `H₀#`, `H₁#` of Hatcher, Thm 2.10) |
| `HurewiczMap` | 118–620, 658–697 (481 unit lines, 52 units) | `Remaining` … `squareHomologyClass_transAt`, `hurewiczFunction` … `hurewiczMap_representative` | the square chain of a based square, the Hurewicz map `π_2 → H_2` (Hatcher, §4.2) |
| `MapGenLoop` | 621–656 (32 unit lines, 5 units) | `mapGenLoop`, `_val`, `_const`, `_homotopic`, `_transAt` | functoriality of based loops (Hatcher, §4.1) |
| `Basic` | 703–706, 719–992 (256 unit lines, 20 units) | `timeSlice` … `straightenedTwoCycle_class` (now `Hurewicz.Prism.*`) | the prism operator, `∂P + P∂ = H₁# − H₀#` (Hatcher, Thm 2.10); simplex-family version |
| `VertexEdgeStraightening` | 996–1593 (545 unit lines, 54 units; 60 constants with the 5 fields and the constructor of `VertexHomotopyData`) | `VertexHomotopyData` … `extendCoherentSimplexHomotopy_face` | straightening vertices and edges coherently (Hatcher, Thm 4.32, proof) |
| `BasedTriangle` | 1597–1937 (304 unit lines, 38 units) | `triangleBoundary` … `normalizedTwoCycle_class` | based triangles, the normalized `2`-cycle (Hatcher, Thm 4.32, proof) |
| `BasedTetrahedron` | 1941–2219, 2555–2793 (478 unit lines, 38 units) | `tetrahedronOneSkeleton` … `tetrahedronShiftedQuadrilateralLoop_diagonal`, `tetrahedronQuadrilateralB` … `basedTriangleClass_cyclic` | based tetrahedra, quadrilateral fillings, cyclic symmetry of based triangles |
| `SquareRotation` | 2220–2554 (300 unit lines, 36 units) | `quarterTurn` … `rotatedSquareLoop_class` | a quarter turn of a based square preserves its `π_2`-class (cf. Hatcher, §4.1) |
| `SquareSubdivision` | 2797–3350 (500 unit lines, 55 units; 58 constants with the 3 constructors of `SubdivisionSameSide`) | `SubdivisionSquare` … `subdivision_additiveClass` | diagonal subdivision of a based square splits its class (Hatcher, Thm 4.32, proof) |
| `TetrahedronRelation` | 3354–3570 (204 unit lines, 14 units) | `tetrahedronQuadrilateralA_lower` … `normalizedTriangle_boundary_relation` | alternating face sum of a based tetrahedron vanishes (Hatcher, Thm 4.32, proof) |
| `TwoTriangles` | 3576–3874 (242 unit lines, 28 units) | `squareAffineTriangle` … `squareChain_basedTriangleLoop` | the square chain is the difference of two singular triangles |
| `HurewiczInverse` | 3878–4145 (242 unit lines, 25 units) | `basedTriangleCycle` … `hurewiczMap_hurewiczInverse` | the inverse map on `H_2`, `h ∘ h⁻¹ = id` (Hatcher, Thm 4.32, surjectivity) |
| `NormalizedSquare` | 4149–4619 (439 unit lines, 33 units) | `lowerSquareTriangle_verticesBased` … `squareNormalization_homotopic` | a based square is homotopic to two based triangles glued along the diagonal |
| `SubdivisionTriangleClass` | 4623–5034 (376 unit lines, 37 units) | `subdivisionUpperPositiveSquareTriangle` … `hurewiczInverse_comp_hurewiczMap` | class of a glued pair of based triangles, `h⁻¹ ∘ h = id` (Hatcher, Thm 4.32, injectivity) |
| `DegreeTwo` | 5038–5059 (21 unit lines, 2 units) | `degreeTwoLinearEquiv`, `hurewiczPi2Equiv` | the degree-two Hurewicz theorem (Hatcher, Thm 4.32, `n = 2`) |
| `ComposeHomotopies` | 5064–5300 (223 unit lines, 14 units) | `cylinderHomotopy` … `extendCoherentSimplexHomotopy_const` | composition of simplex-indexed homotopy families |

The auditors' suggestion (`PrismOperator.lean` = the prism section, `DegreeTwo.lean` = the rest,
`composeSimplexHomotopies` into `Straightening.lean`) was refined: the 4,000-line `n = 2` argument
is cut along its labelled sections; `composeSimplexHomotopies` stays a piece of this module because
`Straightening.lean` is a consumer of the facade (moving the lemmas there would make the facade
import its own consumer).

Context handling: the tool writes context (the original module docstring, `open`, `noncomputable
section`, the `/-! ### -/` section headers) to every output; in each piece the header was replaced by
the piece's imports and a new module docstring, section headers without a declaration of the piece
were removed, and the four headers that named another section were retitled. `open Set Function
Filter Manifold Topology` became `open Set Function Topology` (`Filter`, `Manifold` unused; build
green). Imports: each piece imports the pieces it uses (from the dump's `uses`) and, from the
original list `SimplexCube`, `HomotopyExtension`, `CrossProduct`, `CrossInsert`, those it uses
directly (`CrossProduct` is being split by another agent; its facade is imported); the two pieces
using only Mathlib (`SquareRotation`, `SquareSubdivision`) import `Mathlib`, `MapGenLoop` imports
`Mathlib.Topology.Homotopy.HomotopyGroup`. The list was not minimized by trial builds.

Verbatimness: `prism/receipt_<Piece>.json` records the SHA-256 of every moved unit; a script
(`verify.py`, in the coordinator scratch) recomputed the hashes on the base file and checked that
each unit text occurs in its piece, that the 455 declaration names occur exactly once over the
pieces, and that no declaration was left behind; `envdiff` (below) confirms the environment.

## `Hopf/Proof` moves

None. The file contains no project material (no dimension-6 hypotheses, no `Hemisphere.Sphere 2`,
no `mo1973`, no W4W1 index machinery); every declaration is general algebraic topology at the
level of Hatcher, Chapters 2 and 4. Closure argument: nothing moved, so nothing to close.
`Lib/AxiomAudit.lean` has no probe of this module.

## Renames (commit 2)

`Hurewicz.DegreeTwo.SimplyConnected.<n>` → `Hurewicz.Prism.<n>` for the 20 declarations of the prism
section (`prism/rename.txt`, lines `<new> <old>`): `timeSlice`, `inducedChain_timeSlice`,
`prismOperator`, `prismOperator_apply`, `prismOperator_boundary`, `prismOperator_domain`,
`simplexPrism`, `prismOperator_simplex`, `simplexPrism_boundary`, `simplexEndpointOperator`,
`simplexEndpointOperator_simplex`, `simplexPrismOperator`, `simplexPrismOperator_simplex`,
`FaceCompatibleHomotopies`, `timeSlice_face`, `simplexEndpointOperator_boundary`,
`simplexPrismOperator_boundary`, `simplexEndpointOperator_zero`, `straightenedTwoCycle`,
`straightenedTwoCycle_class`. Consumers updated: `Lib/AlgebraicTopology/Hurewicz/{CubeGluing,
Degree, Straightening}.lean` (84 qualified references), `Hopf/LibShims.lean` (the 20 names moved
from `export Hurewicz.DegreeTwo.SimplyConnected (…)` to a new `export Hurewicz.Prism (…)` in the same
namespace `SecondHurewicz.SimplyConnected`, so every `SecondHurewicz.SimplyConnected.<n>` alias is
unchanged; the alias `SecondHurewicz.SimplyConnected.simplexPrism.eq_1` re-pointed). No `mo1973`
names existed in the file at the base revision (the audit's seven had been renamed earlier).

## Universe lifts (commit 3)

`{X : Type}` → `{X : Type*}` (binder only, proofs unchanged), checked by
`lake env lean prism/lift_examples.lean` (one `example := @c.{0,…}` per constant, all accepted):

| constant | example at `u = 0` |
|---|---|
| `Hurewicz.DegreeTwo.SimplyConnected.squareTriangles_diagonal` | `example := @Hurewicz.DegreeTwo.SimplyConnected.squareTriangles_diagonal.{0}` |
| `Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_outerFace` | `example := @Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_outerFace.{0}` |
| `Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_outerFace` | `example := @Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_outerFace.{0}` |
| `Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerSquareTriangle_based` | `example := @Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerSquareTriangle_based.{0}` |
| `Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based` | `example := @Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based.{0}` |
| `Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based` | `example := @Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based.{0}` |
| `Hurewicz.homotopyTrans_compContinuousMap` (`{A B X}`) | `example := @Hurewicz.homotopyTrans_compContinuousMap.{0, 0, 0}` |
| `Hurewicz.homotopyTrans_const` (`{A X}`) | `example := @Hurewicz.homotopyTrans_const.{0, 0}` |
| `Hurewicz.homotopyTrans_congr` (`{A X}`) | `example := @Hurewicz.homotopyTrans_congr.{0, 0}` |
| `Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlendMap` (`{Y}`) | `example := @Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlendMap.{0}` |

Why not more: `SingularChains.Chains (X : Type)`, `SingularChains.SingularSimplex (X : Type)` and
`SingularHomology.crossInsertLeft {X Y : Type}` pin every chain-level statement (the whole prism
section, the Hurewicz map, the inverse) at universe 0; lifting a definition that occurs in the
statements of other declarations (`BasedTriangle`, `basedTriangleLoop`, `mapGenLoop`, …) would change
the type hashes of those declarations (levels are hashed) — `mapGenLoop` in particular occurs in
statements of `Naturality.lean` and `Hopf/Proof/…/DegreeSix.lean` — so only theorems and the one
definition used solely inside proofs were lifted.

## Docstrings

Computed over the sixteen pieces: 455 declarations, 2 `private`, 453 with a docstring, 0 missing
(the base file already had one on every declaration; none was written or changed). Every piece has
a module docstring stating the mathematics and the textbook result.

## Build lines

BUILD_LINES

## envdiff

ENVDIFF

## Left

LEFT

## Commits

COMMITS
