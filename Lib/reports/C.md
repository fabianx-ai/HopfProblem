# Lane C report — the Hurewicz theorem in every degree

**Current Lean checkpoint:** `37fc1de8`, branch `lib/C-14-integrated-receipt`.
**Toolchain:** `leanprover/lean4:v4.33.0`.
**Textbook and live ledger:** `Lib/docs/C.md`; aggregate receipt: `Lib/docs/C-INTERFACE_RECEIPT.md`.
**Scope:** lane C only. The reassigned J/E2/F/G packets and target files were not edited.
**Authorship:** acting seat Devin, powered by Fusion (GPT-6 Astra Low Thinking + SWE-2 Medium).

## Current result

For `2 ≤ n`, a simply connected space `X`, and `x : X`, assuming
`Subsingleton (π_ j X x)` for `2 ≤ j < n`, the general Hurewicz equivalence is:

```lean
Mathoverflow1973.Hurewicz.hurewiczLinearEquivOfTwoLE x n hn hpi
```

Its result is `Additive (π_ n X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X n`.
The return type locally installs `Nontrivial (Fin n)` from `hn`; no additional mathematical
hypothesis is imposed. The degree-`m + 3` form is `Hurewicz.hurewiczLinearEquiv x hpi`.
The degree-two input is `Hurewicz.degreeTwoLinearEquiv`.

C10 and C13 are **landed**, not blocked. `Lib/reports/C-handoff.md` is a historical handoff.
The proof follows the normalization tower, coherent cube gluing, signed Kuhn subdivision,
and prism class-preservation arguments of `Lib/docs/C.md`, §§8–13.

## Continuation commits

| Commit | Independently checked result |
|---|---|
| `0a3b870` | Constant preservation through the tower; normalized cube; `classOperator_cubeChain`; inverse/map round trip; general linear equivalence |
| `71eccfe` | Strong-induction homology-to-homotopy vanishing and `sphere_pi_subsingleton_of_lt`; C13 bootstrap interface |
| `26a4708` | Replace degree-three/four/five/six proof towers with general-theorem adapters; lower stock baseline |
| `c2059b6` | General based sphere-map classification, basepoint adjustment, self-map and inverse consequences; eight recognition adapters |
| `2d6cd4c` | `HigherHurewicz → Hurewicz`; generic coface, composition, subdivision, and cube-coordinate renames; compatibility exports |
| `2bde114` | Cross-product/descent APIs renamed from `PeriodTorusHigherHomology` to `SingularHomology`, with project shims |
| `e0e73ff` through `1a31384` | Twelve file-specific documentation commits, with comment-only token validation |

All current names above are inside `Mathoverflow1973`. Compatibility names are supplied by
`Hopf/LibShims.lean`, not by importing project code into `Lib/`.

## C13 and consumers

`Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean` now exports:

- `Hurewicz.pi_subsingleton_of_homology_vanishing` and `sphere_pi_subsingleton_of_lt`;
- `Hurewicz.hurewiczMap_injective`, including the degree-two bridge;
- `Hurewicz.factorMap_homotopyRel` and `basedSphereCube_homologyClass`;
- `Hurewicz.sphere_homotopicRel_of_topClass_eq` for degrees `m + 2`;
- `Hurewicz.exists_basepoint_adjustment` for positive-dimensional quotient spheres;
- `Hurewicz.sphere_homotopic_id_of_topClass`;
- `Hurewicz.right_inverse_is_left_inverse`, with top-homology injectivity assumed for the
  sphere map, not for its proposed right inverse.

The classification is expressed using the pushed-forward quotient cube class, exactly as the
recognition consumer needs it. A separately normalized integer-valued degree API is not claimed.

`Hopf/Hurewicz.lean` retains the types of the degree-three/four/five equivalences, but their
bodies instantiate the general theorem. Its sphere homotopy-vanishing instances use the general
bootstrap. `Hopf/Recognition.lean` retains its degree-six public consumer interfaces and
naturality statements; its classification and basepoint-adjustment proofs call `Lib`.
The project theorem statements, including `threefoldHomotopyEquiv`, were not changed.

At `26a4708`, the two consumer files changed by **+69 / −10,575 lines**, a net reduction of
**10,506 Lean lines**. The subsequent C13 adapters removed another **109 net lines** from
`Hopf/Recognition.lean` (+18 / −127). At `1a31384`:

| File | Lines |
|---|---:|
| `Hopf/Hurewicz.lean` | 423 |
| `Hopf/Recognition.lean` | 8,284 |

The stock census was lowered from **3,893 to 2,862** at the consumer-deduplication commit.
The prefix list was unchanged; `python3 scripts/lib_stock_census.py --check` passes.
This measures the script's explicit stock-declaration rule, not every mathematical declaration
or generated alias in the Lean environment.

## Verification receipts

The successful committed-unit gates below used the pinned toolchain. Wall times come from the
recorded start/end epochs, not from Lean's per-module timing lines. Logs are under
`/home/kimi/s6-notes/`.

| Gate | Result | Wall seconds | Log |
|---|---|---:|---|
| C10 `lake build Lib.AlgebraicTopology.Hurewicz.CubeSphere` | pass | not captured | original tool output; CubeSphere module time 8.4 s is not total wall time |
| C13 bootstrap `lake build Lib.AlgebraicTopology.Hurewicz.HopfDegree` | pass | 18 | `C13-hopfdegree-build.log` |
| C10 adapters `lake build Hopf.Recognition` | pass | 902 | `C10-consumer-build.log` |
| C13 classification `lake build Lib.AlgebraicTopology.Hurewicz.HopfDegree` | pass | 7 | `C13-classification-build.log` |
| C13 consumers `lake build Hopf.Recognition` | pass | 455 | `C13-consumer-build.log` |
| Generic rename `lake build Hopf.Recognition` | pass | 739 | `C-rename-build.log` |
| Cross-product rename `lake build Hopf.Recognition` | pass | 726 | `C-cross-rename-build.log` |
| Documentation batch `lake build Hopf.Recognition Lib.Topology.Homotopy.CellFilling` | pass | 705 | `C-doc-build.log` |
| Documentation rework: direct `lake env lean` on twelve files | all pass | per-command timestamps recorded | `C-doc-rework-checks.log` |
| Aggregate provider / importing consumer | both pass | 3 / 3 | `C-interface-provider.log`, `C-interface-consumer.log` |

The documentation rework log includes an interrupted first CubeSphere check followed by a
successful retry; it is not evidence of thirteen distinct checked files. Two final comment
clarifications and one missing docstring were subsequently added without changing code tokens.

Axiom output for the principal consumer audit is verbatim:

```text
'Mathoverflow1973.Degree.sphere_homotopicRel_of_topClass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mathoverflow1973.Degree.Sphere.homotopic_id_of_topClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mathoverflow1973.Degree.right_inverse_is_left_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mathoverflow1973.Degree.threefoldHomotopyEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source: `C13-consumer-axioms.log`. The renamed Hurewicz equivalence, sphere self-map theorem,
and cross product were also audited with the same axiom set (`C-rename-shims.log`,
`C-cross-rename-shims.log`). The durable lane-C probes are appended to `Lib/AxiomAudit.lean`.

### Final comprehensive gates (historical: recorded at `1a31384`, not rerun at `37fc1de8`)

| Command | Result | Wall seconds | Log |
|---|---|---:|---|
| `lake build Lib Hopf.Final Solution` | exit 0; 8,817 jobs | 784 | `C-final-build.log` |
| `lake env lean Lib/AxiomAudit.lean` | exit 0; only permitted axioms | 4 | `C-final-axioms.log` |
| `lake exe comparator comparator/config.json` | **environment-blocked**, exit 1 | less than 1 at recorded timestamp resolution | `C-final-comparator.log` |
| `lake env lean C_FinalConsumerAudit.lean` (temporary import of `Solution`) | exit 0 | 3 | `C-final-consumer-axioms.log` |

The build ran from epoch `1789261194` to `1789261978`. The comparator did not reach a
verification verdict; its actual diagnostic was:

```text
Building Challenge
could not execute external process 'landrun'
uncaught exception: Child exited with 255
```

`landrun` must be provisioned on the session's PATH before this gate can be completed. The
existing real binary found during environment diagnosis was inaccessible to this user.
No passthrough/fake sandbox was used, and comparator configuration was not changed. The old
integration comparator verdict is **not** substituted for a current one. Owner assistance or
permission to provision a local real sandbox is requested.

The independent final consumer axiom output is:

```text
'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mathoverflow1973.Degree.threefoldHomotopyEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The temporary audit source was removed. No further Lean source changes followed those gates
at `1a31384`.

### Integrated-head gates at `37fc1de8` (after the two C13 adapter-body edits)

Two `Hopf/Recognition.lean` adapter bodies were re-pointed from the compatibility
`HigherHurewicz.` spelling to the current `Hurewicz.` names
(`sphere_homotopicRel_of_topClass_eq`, `Sphere.homotopic_id_of_topClass`); statements
unchanged. Fresh downstream gates, replacing nothing in the historical table above:

| Command | Result | Log |
|---|---|---|
| `lake build Hopf.Recognition` | exit 0; 8,813 jobs | `C13-integrated-recognition.log` |
| `lake build Hopf.Final Solution` | exit 0; 8,816 jobs | `C13-integrated-final.log` |
| `lake env lean C13_IntegratedConsumerAudit.lean` (`import Solution`, four `#print axioms`) | exit 0; `[propext, Classical.choice, Quot.sound]` only | `C13-integrated-consumer-axioms.log` |

The full-`Lib` aggregate build and `Lib/AxiomAudit.lean` were not rerun at `37fc1de8`; the
`1a31384` table above remains their last recorded result. See also the integrated receipt in
`Lib/docs/C13-CLASSIFICATION.md` and the refreshed `Lib/docs/C-INTERFACE_RECEIPT.md`.

## Documentation coverage

The continuation added module overviews, proof-order section headers, and missing role-stating
docstrings. Review corrected several initial prose errors about composition direction,
conditional straightening, coordinate indices, and constant simplices. The code was never
changed to match those descriptions.

A comment-aware, string-aware scan of explicit public declarations, excluding private and
generated declarations, gave the following fixed coverage snapshot. After adding the one
missing `formalPointCrossProduct` docstring, all listed declarations are documented.

| File stem | Explicit public declarations | Missing docstrings |
|---|---:|---:|
| SimplexCube | 44 | 0 |
| HomotopyExtension | 82 | 0 |
| PrismOperator | 453 | 0 |
| Straightening | 44 | 0 |
| CubeTriangulation | 70 | 0 |
| CubeGluing | 127 | 0 |
| Subdivision | 226 | 0 |
| CubeChainDecomposition | 132 | 0 |
| Degree | 53 | 0 |
| CubeSphere | 68 | 0 |
| CrossProduct | 103 | 0 |
| CellFilling | 6 | 0 |
| **Total for the twelve-file pass** | **1,408** | **0** |

`HopfDegree.lean` was documented as part of its implementation and is not included in this
particular twelve-file census. Comment-stripped token comparison of all twelve files against
`2bde114` passed. Linter output is not warning-free: existing unused-simp and `letI`/`haveI`
style warnings remain. No linter or repository security setting was disabled.

## The integer-module instance experiment

A disposable copy of `CrossProduct.lean` removed only the local wrappers selecting
`integerLinearMapModule`/`integerTensorModule`, leaving the definitions and proofs unchanged.
Lean exited **1** at four scalar-action elaboration sites. The first diagnostic was:

```text
congrArg (fun l => l b) (LinearMap.map_smul F r a)
has type
  (F (r • a)) b = (r • F a) b
but is expected to have type
  (F (r • a)) b = (RingHom.id ℤ) r • (F a) b
```

The affected constructions were `integerBilinearRightApply`, `integerBilinearFlip`,
`integerBilinearPostcompose`, and `crossProductHomologyCycles`.
Evidence: `C-module-diamond.log`. The disposable file was removed. Production instances remain;
this records the attempted removal and its concrete limitation rather than claiming it succeeded.

## Historical extraction provenance and corrections

The original baseline table is retained for provenance; these are not new continuation moves:

| Commit | Module | Historical declaration count | Source head |
|---|---|---:|---|
| `4b9b9d7` | CrossProduct | 96 | `527ac35` |
| `4d4cdc7` | SimplexCube | 47 | `527ac35` |
| `63b933a` | HomotopyExtension | 87 | `4d4cdc7` |
| `f6ef77a` | CubeTriangulation | 72 | `63b933a` |
| `b42417b` | PrismOperator | 440 | `f6ef77a` |
| `7633126` | Subdivision | 228 | `b42417b` |
| `aa3f112` | CubeGluing | 127 | `7633126` |
| `2cb2ca5` | Degree | 53 | `aa3f112` |
| `75a473c` | CubeChainDecomposition | 75 | `2cb2ca5` |
| `8611afa` | Composition machinery into PrismOperator | 11 | `2cb2ca5` era |

The general chain decomposition was introduced at `4238402`; the normalization tower at
`59ec7f8`. C11 was already landed at `f3d6ba6`/`d597ac4`; C12 at `71632be`.

Corrections required by `Lib/reviews/INTEGRATION.md`:

- The integration census was **5,170 → 3,893**, not 5,024 → 3,927.
- The historical Hurewicz file reduction was **22,910 → 9,631** lines, not 20,871 → 9,632.
- The integration review reports that the SimplexCube baseline range is off by one line at
  both ends and its recorded hash is not reproducible from that stated range. This report
  does not silently replace it with a guessed corrected hash.
- The PrismOperator baseline hash covers the source range **after removal of the cut
  sub-block**, not the entire advertised contiguous range.
- `CrossProduct.lean` uses plain `import`, not a `module`/`public import` header. This deviation
  is explicit here. The legacy dependency graph also prevents simply switching the new
  HopfDegree file to the module system without converting its dependencies first.
- The historical Stage-2 review referenced by `f42b9e6` is recovered as
  `Lib/docs/C-STAGE2-REVIEW.md`. Its original reviewer was not named in the recovered artifact;
  owner confirmation remains outstanding. Recovery is not represented as a new review.
- The pinned Mathlib uses root `GenLoop`; the former open naming question is closed.

## Mathlib twins and remaining packaging limits

| Lane-C module | Twin / shape reference |
|---|---|
| SimplexCube, CubeTriangulation | `Mathlib/AlgebraicTopology/TopologicalSimplex.lean`; cube construction has no exact twin |
| HomotopyExtension | `Mathlib/Topology/Homotopy/Basic.lean` (shape) |
| PrismOperator | `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` |
| Subdivision | `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` (shape) |
| CubeGluing | in-tree `Hurewicz/SimplexPaths.lean` (shape) |
| Degree, Straightening, HopfDegree | in-tree `Hurewicz/Degree1.lean` (shape; no exact higher-degree twin) |
| CubeChainDecomposition, CrossProduct | `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` (shape) |
| CubeSphere | `Mathlib/Topology/OnePoint.lean` |
| CellFilling | `Mathlib/Topology/Homotopy/Contractible.lean` (shape) |

The specifically requested generic-name cleanups and `HigherHurewicz → Hurewicz` rename are
landed. Full migration out of `Mathoverflow1973`, renaming the remaining degree-two helper
namespaces, and converting the entire import graph to `module` are not claimed here.
The historical prospectus's separately named general naturality and positive-degree
homology-vanishing wrappers are not among the thirteen validated public outputs; the existing
degree-six naturality consumer remains in `Hopf/Recognition.lean`. The remaining generic
`Degree.DiskCube` and lane-B leftovers in `Hopf/Hurewicz.lean` have not been silently counted as
extracted. These are explicit remaining upstream-packaging/API items, not C10/C13 proof blockers.

No push has been performed. Attribution was not changed through git configuration.
