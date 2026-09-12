# Lane C report — the Hurewicz theorem in every degree

**Lane:** `lib/C-hurewicz` (base `721fc82`; toolchain `leanprover/lean4:v4.33.0`).
**Ledger/textbook:** `Lib/docs/C.md` (Axis 1–5; Stage-2 review incorporated in `f42b9e6`).

## The generalized statement

For `2 ≤ n`, `X` simply connected, `x : X`, with `Subsingleton (π_ k X x)` for
`2 ≤ k < n` (i.e. `X` is `(n-1)`-connected): the Hurewicz map
`Additive (π_ n X x) ≃ₗ[ℤ] SingularHomology X n` is a `ℤ`-linear equivalence.
The textbook proof (`Lib/docs/C.md`, §§1–15) is the cube-triangulation proof:
straightening/normalization tower (§8), the Kuhn decomposition
`[p] = Σ_σ sign(σ)·[p ∘ cubeSimplex σ]` (§9–10), the prism operator (§6), the
cross product (§3), the homotopy-extension property of `(Δⁿ, ∂Δⁿ)` (§5), and the
cell-filling / Hopf-degree inputs.

## What landed

Baselines (bytes verbatim except import lines and the noted renames; each with its
source range on the pre-move HEAD, byte count, and SHA-256 in the commit message):

| Commit | Module | Decls | Source on |
|---|---|---|---|
| `4b9b9d7` | `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` | 96 | `527ac35` |
| `4d4cdc7` | `Lib/AlgebraicTopology/Hurewicz/SimplexCube.lean` | 47 | `527ac35` |
| `63b933a` | `Lib/AlgebraicTopology/Hurewicz/HomotopyExtension.lean` | 87 | `4d4cdc7` |
| `f6ef77a` | `Lib/AlgebraicTopology/Hurewicz/CubeTriangulation.lean` | 72 | `63b933a` |
| `b42417b` | `Lib/AlgebraicTopology/Hurewicz/PrismOperator.lean` | 440 | `f6ef77a` |
| `7633126` | `Lib/AlgebraicTopology/Hurewicz/Subdivision.lean` | 228 | `b42417b` |
| `aa3f112` | `Lib/AlgebraicTopology/Hurewicz/CubeGluing.lean` | 127 | `7633126` |
| `2cb2ca5` | `Lib/AlgebraicTopology/Hurewicz/Degree.lean` | 53 | `aa3f112` |
| `75a473c` | `Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean` | 75 | `2cb2ca5` |
| `8611afa` | (composition machinery into `PrismOperator.lean`) | 11 | `2cb2ca5`-era |

Renames applied at baseline (all lane-A-landed names): `FirstHurewicz. →
SingularChains.`, `PeriodTorusHigherHomology.crossInsertLeft →
SingularHomology.crossInsertLeft`. Four misnamed generic theorems moved along
with their consuming blocks and noted in the commit bodies
(`PeriodTorusLineBundle.ChernCocycle.simplexFace_comp`, `singularSimplex_face_face`;
`PeriodTorusHigherHomology.formalBoundary_edge_simplex`,
`formalPointCrossProduct_edge_boundary`,
`formalPointCrossProduct_mem_supported`,
`formalEdgeCrossProduct_mem_supported`).

New mathematics (the lane's two generalizations, both flagged in the ledger):

- **G1** (`4238402`, `CubeChainDecomposition.lean`): the Kuhn decomposition at
  every degree, `HigherHurewicz.cubeChain_eq_sum_simplices`, by induction with
  the prism identity at the step. New apparatus: the general-`n` uncurrying
  `cubeCoordinates`, the recursive `fundamentalCubeChain`, `cubeChain`,
  `curryLoop`, the recursion `cubeChain_succ`, the prism identification
  `evalLeft_crossProductEdge_intervalChain_simplex` (general form of the pinned
  `intervalTetrahedronChain_eq_prismCubeRealization`), base cases at `n = 0, 1, 2`
  (the degree-2 case recovering `SecondHurewicz.squareChain_two_triangles` via the
  vertex identifications of the permutation simplices).
- **G2** (`59ec7f8`, `Straightening.lean`): the normalization tower at every
  degree. `HigherHurewicz.TowerPair` (bundled consecutive storeys), the
  edge-straightening tower, `vertexEdgeHomotopy` (the general vertex+edge
  storey), `NormalizationState` (augmented family + next normalization +
  zeros + face compatibility + both endpoint properties, all seven invariants
  propagated), `normalizationStep`, `normalizationBaseTwo`,
  `normalizationTower` (driven by `hpi : ∀ j, 2 ≤ j → j ≤ k+2 →
  Subsingleton (π_ j X x)`), and the public `normalizationHomotopy (n)` with
  `normalizationHomotopy_zero` and `normalizationHomotopy_endpoint` (the
  endpoint is based at `x` on the boundary).

## Consumers re-routed

`Hopf/Hurewicz.lean` imports the new modules; the moved names keep their
`HigherHurewicz.*` / `SecondHurewicz.*` spellings so every consumer elaborates
unchanged. The two renamed lane-A prefixes go through the existing
`Hopf/LibShims.lean` re-export block (8 `FirstHurewicz.*` aliases added for the
`triangleEdge*`/`simplexFace_vertex` facts that moved to `SingularChains.*`).
`Hopf/Hurewicz.lean`: 20,871 → 9,632 lines.

## Gates

- `lake build` (full project, 8,822 jobs): green; wall 2m20s warm.
- Comparator (`lake exe comparator comparator/config.json`, run with
  `COMPARATOR_LANDRUN=<passthrough>` since `landrun` is absent on this box):
  `lean4export` + nanoda kernel + Lean default kernel all accept
  `Mathoverflow1973.mathoverflow_1973`; axioms `[propext, Classical.choice,
  Quot.sound]` only. Wall 17m35s.
- Census (`scripts/lib_stock_census.py`): 5,024 → 3,927 (ratchet lowered and
  committed). The `HigherHurewicz` prefix is now absent from `Hopf/`.
- `#print axioms` on the lane's key declarations (`cubeChain_eq_sum_simplices`,
  `cubeChain_eq_sum_simplices_step`, `cubeChain_succ`, `fundamentalCubeChain`,
  `straightenedCycle`, `singularHomologyDesc`, `comp_singularHomologyDesc_eq_id`,
  `CubeGluing.coherentCubeEndpoint`, `CubicalBoundary.cubicalBoundaryValue_eq_zero`,
  `simplexStraighteningHomotopy`): all depend only on `[propext,
  Classical.choice, Quot.sound]`.
- Lint: the only warnings in the lane's files are pre-existing
  `linter.dupNamespace` notes inherited from the lane-A namespaces (the rename
  phase's business) — no warnings from the new G1/G2 content.

## Docstring coverage

Public declarations without a docstring in the lane's moved files: the baseline
moves carry the raw code (0/47 SimplexCube, 0/87 HomotopyExtension, 0/72
CubeTriangulation, 0/454 PrismOperator, 0/228 Subdivision, 0/126 CubeGluing,
0/53 Degree, 0/103 CrossProduct). The new-math content is docstringed
(CubeChainDecomposition: the 20 new declarations; Straightening: 17/18). The
per-declaration docstring pass belongs to the rename phase (the reference
example's pattern: `lib(C): rename …` then `lib(C): doc …`), which renames to
Mathlib-shaped names and documents each public declaration against the textbook
section. Target 0 is **not** met at this checkpoint; it is the rename phase's
deliverable.

## Mathlib twin files

| Lane-C module | Mathlib twin |
|---|---|
| `SimplexCube.lean` | none existing (the simplex–cube dictionary); shape after `Mathlib/AlgebraicTopology/TopologicalSimplex.lean` |
| `HomotopyExtension.lean` | HEP of the pair `(Δⁿ, ∂Δⁿ)`; nearest `Mathlib/Topology/Homotopy/…` |
| `CubeTriangulation.lean` | none existing (Kuhn triangulation); shape after `Mathlib/AlgebraicTopology/TopologicalSimplex.lean` |
| `PrismOperator.lean` | `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` (Mathlib's prism lives there) |
| `Subdivision.lean` | shape after `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` |
| `CubeGluing.lean` | none existing; shape after the reference example's `SimplexPaths.lean` |
| `Degree.lean` | the headline's home; the reference example `Degree1.lean` is the degree-1 instance |
| `CubeChainDecomposition.lean` | none existing (the Kuhn decomposition) |
| `Straightening.lean` | none existing (the normalization tower) |

## Open items (the exact seams)

1. **C10 assembly (the headline `hurewiczLinearEquiv` at general `n`).** Ingredients
   landed this branch (`lib/C-10-boundary`):
   - `classOperator_boundary` (`199fb46`): the class operator vanishes on
     boundaries at degree `n ≥ 3`.
   - `cubeChain_boundary` / `cubeCycle` / `cubeHomologyClass` (`bbfed66`):
     the triangulated cube chain of a based loop is a cycle at every degree
     `n ≥ 2`. Combinatorial core `sum_cubeOrientation_faces` (interior faces
     cancel by Kuhn transposition; outer faces are constant with total
     orientation zero). `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
   - `hurewiczInverse` (`4e730ad`): `singularHomologyDesc` of the class
     operator, degree `n ≥ 3`.
   - `cubeHomologyClass_homotopic` / `hurewiczFunction` (`737b1d0`): a
     boundary-relative homotopy of based cubes descends through the
     cube-to-sphere quotient, so the cube class is well-defined on `π_n`
     for `n ≥ 2`.
   Still to assemble:
   - Additivity `cubeHomologyClass (GenLoop.transAt i p q) = cubeHomologyClass p +
     cubeHomologyClass q` at degree `≥ 3` (degree 2 is `82ba4ba`, via
     `cubeHomologyClass_eq_squareHomologyClass`; half-cube scalings
     `cubeScaleLeft/Right` with `transAt_comp_cubeScale*` are `c00bb61`).
     Then `hurewiczFunction` upgrades to a `ℤ`-linear `hurewiczMap`.
   - Round trips: `hurewiczMap ∘ classOperator = id` via the landed
     `comp_singularHomologyDesc_eq_id` + the pointwise
     `hurewiczMap_classOperator_cycle`; the other direction via the
     normalized cube (`CubeGluing.coherentCubeEndpoint` +
     `coherentCubeHomotopy` + `NativeSubdivision.nativeCubeSubdivision_class` +
     `cubeChain_eq_sum_simplices`).
   - Then `hurewiczLinearEquiv := LinearEquiv.ofLinearMap …` and the per-degree
     blocks (`Second/Third/Fourth/Fifth/SixthHurewicz`, ~1,000 declarations
     remaining in `Hopf/Hurewicz.lean`) become one-line instantiations and are
     deleted.
   - **Engineering note:** boundary-plumbing proofs must NOT rewrite into
     composed tower expressions in place (timeout at `isDefEq`/`whnf`). Work
     through small named intermediate lemmas.
2. **C11 CubeSphere** — **LANDED** (`f3d6ba6` baseline + `d597ac4`
   generalize): `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` holds the
   general-`n` cube-sphere quotient (the pre-existing `Degree.SphereCube.*`
   block, moved) plus the general-`n` `quotientLoop`, `factorMap`,
   `factorMap_quotient/_comp_quotient/_unique`, and
   `factor_cubeChain/cubeCycle/cubeHomologyClass` (the last via the G1
   `cubeChain` and the factor identity). The pinned `n = 6` content in
   `Hopf/Recognition.lean` is re-derived as one-line instantiations
   (`SixSphereCube.StandardSphere = SphereHomology.UnitSphere 6 =
   Degree.SphereCube.Sphere 6` definitionally); statements unchanged,
   consumers untouched.
3. **C13 HopfDegree** (`Degree.sphere_homotopicRel_of_topClass_eq` etc.,
   pinned `n = 6` in `Hopf/Recognition.lean`): needs C10's headline (the
   sphere-connectivity bootstrap `sphere_pi_subsingleton_of_lt` is the
   induction through the general `hurewiczLinearEquiv`); blocked until then.
4. **C12 CellFilling** — **LANDED** (`71632be`): `Lib/Topology/Homotopy/
   CellFilling.lean` holds `Degree.Sphere.homotopic_const_discrete`,
   `real_unitSphere_finite`, `homotopic_const_of_homeomorph`,
   `boundary_homotopic_const_of_pi`, `exists_boundary_extension_of_pi`, and
   `Degree.CylinderFilling.exists_filling`. The disk-cylinder dependencies
   turned out to be already in `Lib/Topology/Homotopy/{HandleRetraction,
   CylinderHEP}.lean` (lanes E1/D2) — my earlier "blocked on lane F/D1"
   assessment was wrong. The pinned `n = 6` instances
   (`Degree.Sphere.boundary_homotopic_const`, `exists_boundary_extension`) and
   the `Degree.LowCellLifting.*` consumer stay in `Hopf/Recognition.lean`.
5. **Rename + doc phase** (the protocol's separate commit): Mathlib-shaped
   names and per-declaration docstrings for all baseline-moved content; the
   `instance`-reduction refactor (the `integerLinearMapModule`/
   `integerTensorModule` local-instance diamond) is attempted there, per the
   ledger.

## The interface receipt

The lane-A seam is closed: every signature naming `FirstHurewicz.*`,
`SingularMayerVietoris.*`, `PeriodTorusHigherHomology.*` resolves against the
landed `Lib/AlgebraicTopology/SingularHomology/*` modules at the current HEAD
(the full build is the evidence). The remaining `Hopf/`-side references are the
per-degree blocks (item 1) and the `SphereHomology.*` leftovers (lane B's
partial move; not mine).
