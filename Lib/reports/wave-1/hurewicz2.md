# Wave 1 — `hurewicz2`: `Lib/AlgebraicTopology/Hurewicz/Subdivision.lean` and `CubeChainDecomposition.lean`

Base `lib/integration` at `e669bc93`; branch `wave1/hurewicz2`; worktree `/home/goblin/hopf-w1-hurewicz2`.
Commits: `e669bc93..HEAD, i.e. d8f9ce06 (Subdivision split), 5d7d3afd (CubeChainDecomposition split), abadab33 (three docstring citations), then the receipt commit`. Tooling: `split_module.py` over `dump_head.jsonl` (the base dump), one run per
piece on the original source (stay set = every constant not in the piece), receipts in
`Lib/reports/wave-1/hurewicz2/receipts/`; driver, plans, check scripts and build scripts beside them. Lake 5.0.0 of the v4.33.0 toolchain rejects `-j3`
(`unknown short option '-j'`); the parallelism was limited with `LEAN_NUM_THREADS=3` instead.

## The cut

Both original modules are now facades: a rewritten module docstring listing the pieces and the
`import`s of the pieces, nothing else. `Lib.lean` and every consumer are unchanged (22 + 21 consumers
of the two facades, `grep -rln 'Hurewicz.Subdivision\b\|Hurewicz.CubeChainDecomposition\b' Lib Hopf
Solution.lean S6.lean S6Shortcuts.lean Challenge.lean --include=*.lean`).

### `Subdivision.lean` (228 declaration units, 238 ranged constants) → `Subdivision/`

| piece | lines moved (of the original) | declarations (units) | ranged constants | textbook topic |
|---|---|---|---|---|
| `SimplexQuotient` | 508 | 52 | 52 | the simplex as a quotient of the cube by prefix minima; based simplices (Hatcher, proof of Thm 4.32; Kuhn triangulation) |
| `CubeClass` | 301 | 33 | 36 | the class of a based cube, quarter turn, coordinate permutations act by the sign (Hatcher §4.1) |
| `InsertPermutation` | 105 | 13 | 13 | `Perm (Fin n) × Fin (n+1) ≃ Perm (Fin (n+1))` by inserting the last index (Mathlib-only piece) |
| `ChamberChart` | 327 | 27 | 34 | charts of the ordered (Kuhn) chambers, cut sequences, inserted charts |
| `Slicing` | 309 | 28 | 28 | slicing a based cube between two cuts; additivity under slicing |
| `ExtendedChamber` | 314 | 30 | 30 | chamber charts extended to a larger cube; the insertion sum |
| `DuffyMap` | 213 | 28 | 28 | Duffy's cumulative-product map as the canonical chamber chart |
| `SubdivisionClass` | 209 | 17 | 17 | Kuhn cells as based simplices; `nativeCubeSubdivision_class` (Hatcher, proof of Thm 4.32) |

Import DAG (checked against the dump's `uses`): `SimplexQuotient` ← `CubeTriangulation`,
`HomotopyExtension`; `CubeClass` ← `PrismOperator` (kept, as instructed); `InsertPermutation` ←
`Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Fintype.Perm`, `Mathlib.Logic.Equiv.Fin.Basic`;
`ChamberChart` ← `CubeClass`, `InsertPermutation`; `Slicing` ← `CubeClass`; `ExtendedChamber` ←
`ChamberChart`, `Slicing`; `DuffyMap` ← `ChamberChart`; `SubdivisionClass` ← `SimplexQuotient`,
`ExtendedChamber`, `DuffyMap`. `open Filter Manifold` dropped from every piece (and `Topology` from the
Mathlib-only piece); `noncomputable section` kept. Declarations are moved by name, so three sections of
the original are re-sorted by topic: `NativeChamberChart.sameFlat` and the `insertChamberMap_*` face
lemmas (original l.1407–1531, 1621–1656) go to `ChamberChart`; the cut-sequence lemmas and the
insertion sum (l.1864–1905, 2112–2153) to `ExtendedChamber`; the cell simplices (l.951–996) to
`SubdivisionClass`.

### `CubeChainDecomposition.lean` (133 declaration units = ranged constants) → `CubeChainDecomposition/`

| piece | lines moved (of the original) | declarations (units) | ranged constants | textbook topic |
|---|---|---|---|---|
| `PrismRealization` | 354 | 28 | 28 | prisms `Δ¹ × (Kuhn cell)` realized by a cube map; the bad-prism submodule (Hatcher §3.B, proof of Thm 2.10) |
| `StandardPrism` | 327 | 31 | 31 | shuffle decomposition of the prism, prism discrepancy, vanishing on bad terms (Hatcher, proof of Thm 2.10) |
| `PermutationInsertion` | 147 | 16 | 16 | `insert k e`, its sign, shuffle simplices are Kuhn cells |
| `CubeChain` | 291 | 21 | 21 | the fundamental cube chain by the edge cross product (Hatcher §3.B); degrees 1, 2 |
| `IntervalSplit` | 174 | 11 | 11 | half-interval paths, the interval chain splits up to a boundary |
| `Concatenation` | 424 | 13 | 13 | the cube chain of `transAt 0 p q` (additivity of the Hurewicz map, Hatcher, proof of Thm 4.32) |
| `KuhnDecomposition` | 174 | 6 | 6 | `cubeChain p = ∑ e, cubeOrientation e • simplexChain (p ∘ cubeSimplex e)` |
| `Cycle` | 171 | 7 | 7 | the cube chain is a cycle; `cubeCycle`, `cubeHomologyClass` (Hatcher §4.2) |

Import DAG (checked against the dump's `uses`): `PrismRealization` ← `CubeTriangulation`,
`PrismOperator` (kept, as instructed); `StandardPrism` ← `PrismRealization`; `PermutationInsertion` ←
`StandardPrism`; `CubeChain` ← `PrismRealization`; `IntervalSplit` ← `CubeChain`; `Concatenation` ←
`IntervalSplit`; `KuhnDecomposition` ← `PermutationInsertion`, `CubeChain`; `Cycle` ←
`KuhnDecomposition`. The ten `attribute [local instance] SingularHomology.integerLinearMapModule … in`
prefixes travel with their units (they are unit prefixes for the tool).

Verbatimness: every moved unit's SHA-256 in the receipts equals the SHA-256 of the same lines of the
original, and the driver (`mkpieces.py`, in the receipt directory) asserts that each unit's text occurs
verbatim in the written piece after the header/section post-processing; the two partition checks
(`partition.py`) print `moved once: 238 … missing: [] dup: {}` and `moved once: 133 …`. Hand edits after
the tool: the piece headers (copyright, imports, module docstring, `open`, `noncomputable section`),
the `/-! ### … -/` section titles carried over from the original (renamed to fit the piece; a header
with no declaration under it dropped), and the three docstring citations of the last commit.

## `Hopf/Proof` moves

None. Both files are general: every declaration is stated for an arbitrary topological space (`Type`
for the chain-level statements, `Type*` for the homotopy-level ones), for every dimension `n`, with no
`Hemisphere.Sphere 2`, dimension-6 or W4W1 hypothesis and no `mo1973` residue. The closure argument is
therefore not needed; as a check, the dump's `uses` shows every piece reachable from the `Lib` consumers
`CubeGluing`, `Straightening`, `Degree`, `CubeSphere` (Subdivision) and `CubeSphere` (CubeChainDecomposition).
`Lib/AxiomAudit.lean` has no probe of either module; nothing moved to `Hopf/Proof/AxiomAudit.lean`.

## Renames

None. The `_mo1973_` names cited by the judgement packet (`Subdivision` l.886/899
`succAbove_lt_prefix_iff_mo1973_8180/8181`, `CubeChainDecomposition` l.780
`linearMap_zsmul_apply_mo1973_8057`) had already been stripped at the base `e669bc93`
(`grep -rn mo1973 Lib/AlgebraicTopology/Hurewicz/Subdivision.lean Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean`
is empty there); `rename.txt` records this. The `native*`/`Native*` vocabulary is left (see "Left").

## Universe lifts

None. The `{X : Type}` binders of `CubeChainDecomposition` (41 at the base, now spread over the pieces)
and the three of `SimplexQuotient` (`Hurewicz.constantSimplexChain`, `correctedSimplexChain`,
`basedSimplex_simplexChain_sum`) are forced by `SingularChains.Chains (X : Type)`
(`Lib/AlgebraicTopology/SingularSmallChains/Barycentric/Native.lean:37`) and `simplexChain (X : Type)`:
a lift needs the chain interface lifted first, as the packet says. The homotopy-level statements were
already `Type*`.

## Docstrings

Computed with `doccount.py` (receipt directory): before, 226 public declarations in `Subdivision.lean`
and 132 in `CubeChainDecomposition.lean`, 0 without docstring; after, the same 358 public declarations
over the sixteen pieces, 0 without docstring; 0 docstrings added, 3 docstrings edited (citations, see
above), 16 module docstrings written, 2 facade docstrings rewritten.

## Checks

All under nohup with `LEAN_NUM_THREADS=3` (`checks.sh`, `build2.sh`, `build3.sh` in the receipt directory's
scratch; logs `checks.log`, `build2.log`, `build3.log`). Lines verbatim:

```
lake build Lib.AlgebraicTopology.Hurewicz.Subdivision            (facade + 8 pieces)
Build completed successfully (8732 jobs).
lake build Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition (facade + 8 pieces)
Build completed successfully (8732 jobs).
lake build Lib
Build completed successfully (9162 jobs).
step1 0
lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9214 jobs).
step2 0
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9164 jobs).
step3 0
python3 scripts/lib_stock_census.py --check
ratchet PASS: 123 <= baseline 1648
grep -rn '^import Hopf' Lib/ --include=*.lean
0 lines (empty)
```

Axiom audit (step 3 output, 3302 `#print axioms` results over both audit modules): the set of axiom
names occurring is exactly `{propext, Classical.choice, Quot.sound}`; `sorryAx` does not occur; 12
declarations depend on no axiom. Warnings: the four `unusedSimpArgs` warnings of
`CubeChainDecomposition.lean` l.1396/1412/1532/1781 at the base reappear at
`IntervalSplit.lean` l.154/170 and `Concatenation.lean` l.108/357 (replayed, not new);
the Subdivision pieces build with no warning.

## envdiff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` after the last edit (no `--rename`: no
renames) → `dump_after.jsonl` (38250 constants; head 38248), then
`envdiff.py dump_head.jsonl dump_after.jsonl --receipt envdiff.json > envdiff.txt`. Summary verbatim:

```
constants before 38248 after 38250 (keys 38146 38148 )
lost 11 added 13 of which source declarations: 0 0 ; names with changed type 8 of which source: 0
auxiliary lost/added/changed (not judged): 11 13 8
module moves (source declarations, 1-to-1): 371 = the plan (16 lines, counts as in the two tables:
  CubeChainDecomposition → Concatenation 13, CubeChain 21, Cycle 7, IntervalSplit 11, KuhnDecomposition 6,
  PermutationInsertion 16, PrismRealization 28, StandardPrism 31;
  Subdivision → ChamberChart 34, CubeClass 36, DuffyMap 28, ExtendedChamber 30, InsertPermutation 13,
  SimplexQuotient 52, Slicing 28, SubdivisionClass 17)
ambiguous module changes: 0
auxiliary constants that changed module: 220
VERDICT PASS
```

Source declarations: 0 lost, 0 added, 0 changed types; moves = the plan. The 11/13/8 auxiliary
lost/added/changed names, reconciled one by one (all in `CubeChainDecomposition` pieces; none is a
source declaration):

- `Hurewicz.CubeSubdivision.prismCubeVertex_shuffle._simp_1_{2,3,5,6}` (lost) ↔ `._simp_1_{1,2,3,4}`
  (added, same four type hashes 821638330, 3269858211, 2185636451, 821100061): the `simp` auxiliary
  lemmas of one proof are renumbered because the module `PermutationInsertion` contains fewer proofs
  before it; the two "changed type" entries `_simp_1_2`, `_simp_1_3` are this renumbering read as a
  name collision.
- `Hurewicz.CubeSubdivision.orientedPrismRealization_standardPrism._simp_1_2` (lost) ↔ `._simp_1_1`
  (added, hash 3705374514): same renumbering.
- `Hurewicz.CubeSubdivision.shufflePrismVertices.eq_1` (lost/added/changed) and
  `shufflePrismVertices._proof_1` (added): the equation lemma of `shufflePrismVertices` is realized
  where first used, now inside `StandardPrism` with a different abstracted proof.
- `Hurewicz.cubeCoordinates._proof_1`, `cubeCoordinates.eq_1`, `cubeRemainingCoordinates._proof_{1,2}`,
  `cubeRemainingCoordinates.eq_1` (lost/added/changed) and `cubeRemainingCoordinates._proof_3` (added):
  the `fun_prop`-generated continuity proofs of the two definitions in `CubeChain` are re-abstracted in
  the new module (one more `_proof_n`), and the equation lemmas embed them.
- The 220 auxiliary constants that changed module are the `_proof_n`/`match_n`/equation lemmas of the
  moved declarations following their parents.

## Left

- Project vocabulary `native*`/`Native*` (`nativeClass`, `NativeCube`, `NativeCubeInternalBased`,
  `NativeCubeSameFlat`, `NativeChamberChart`, `nativeDuffyCube`, `nativeOrderedDuffyMap`,
  `nativeBasedCubeSimplex`, `nativeCubeSubdivision_class`, namespace `Hurewicz.NativeSubdivision`):
  left. A Mathlib-style rename (`cubeClass`, `CubeChamberChart`, `duffyCube`, …) touches 605
  occurrences in the pieces and four consumers (`CubeGluing`, `Straightening`, `Degree`, `CubeSphere`)
  plus `Hopf/LibShims.lean`; the consumer edit is not small.
  `grep -c 'native\|Native' Lib/AlgebraicTopology/Hurewicz/Subdivision/*.lean`;
  `grep -rl 'NativeSubdivision\|nativeClass\|NativeCube\|nativeDuffy\|NativeChamber' Lib Hopf --include=*.lean | grep -v Hurewicz/Subdivision`.
- Universe 0 (`{X : Type}`) in the chain-level statements: 41 binders in the `CubeChainDecomposition`
  pieces, 3 in `Subdivision/SimplexQuotient.lean`, all forced by `SingularChains.Chains (X : Type)`.
  `grep -c 'X : Type}' Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition/*.lean Lib/AlgebraicTopology/Hurewicz/Subdivision/*.lean`.
- Twins (not literal duplicates, both kept): `Hurewicz.NativeSubdivision.insertPermutation e r`
  (inserts the last index at slot `r`; `Subdivision/InsertPermutation.lean`) and
  `Hurewicz.CubeSubdivision.PermutationInsertion.insert k e` (sends `k` to `0`;
  `CubeChainDecomposition/PermutationInsertion.lean`), with the reindexing lemmas
  `sum_insertPermutation` and `PermutationInsertion.sum_insert`; `Hurewicz.SimplexGeometry.prefixMinimum`
  and `Hurewicz.NativeSubdivision.prefixProduct` are the min/product versions of one construction.
  `grep -n 'def Hurewicz.NativeSubdivision.insertPermutation\|def Hurewicz.CubeSubdivision.PermutationInsertion.insert' -r Lib/AlgebraicTopology/Hurewicz/`.
- Better homes not taken (moving would edit modules outside my assignment): the supported-chain lemmas
  `SingularMayerVietoris.inducedChain_mem_supported_of_mapsTo`, `SingularHomology.zeroSimplexValue_const`,
  `SingularHomology.crossProductZeroLeft_pointChain`, `SingularChains.inducedChain_pointChain`,
  `SingularChains.pointChain_mem_supported` (`CubeChainDecomposition/Concatenation.lean`) and
  `SingularChains.inducedChain_const` (`CubeChain.lean`) belong with `Lib/AlgebraicTopology/SingularHomology`;
  `Hurewicz.CubeTriangulation.sum_face_trichotomy`, `sum_cubeOrientation_faces` (`Cycle.lean`) belong in
  `CubeTriangulation.lean`; `Hurewicz.constantSimplexChain`, `correctedSimplexChain`
  (`Subdivision/SimplexQuotient.lean`, namespace `Hurewicz`) are chain-level helpers among the
  `SimplexGeometry` material. `grep -n '^theorem Singular\|^theorem Hurewicz.CubeTriangulation\|^def Hurewicz.c' -r Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition/ Lib/AlgebraicTopology/Hurewicz/Subdivision/`.
- `attribute [local instance] SingularHomology.integerLinearMapModule … in` on ten units of the
  `CubeChainDecomposition` pieces (the packet's "instance that should be global in the chains file"):
  left with the units. `grep -c '^attribute \[local instance\]' Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition/*.lean`.
- `NativeCubeInternalBased` (hypothesis the textbook never states) and the proof-step names
  `badPrism`, `prismDiscrepancy` kept as they are; documented in the module docstrings.
- The four pre-existing `unusedSimpArgs` warnings (see Checks).
- `import Lib.AlgebraicTopology.Hurewicz.PrismOperator` kept in `Subdivision/CubeClass.lean` and
  `CubeChainDecomposition/PrismRealization.lean` as instructed (the module is being split with a facade);
  after that split these two could import the prism piece directly.
