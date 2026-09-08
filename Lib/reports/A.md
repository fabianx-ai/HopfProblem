# Lane A report — singular homology core (Hatcher §2.1–2.2, 2.B)

**Branch:** `lib/A-singular-homology` off `lib/textbook-extraction`. **Move type:** pure move.
**Status: baselines complete (everything movable landed, green), rename landed, gates green,
module docstrings landed for all 16 files; per-declaration docstrings, lint, and de-shim are
the named remaining work (see Open items).**

## Toolchain

`leanprover/lean4:v4.33.0` via elan; Mathlib pinned `db584cd` (v4.33.0) fetched with
`lake exe cache get` (never built from source). Reference example
`Lib.AlgebraicTopology.Hurewicz.*` builds in **7.6 s wall** (documented: 8 s).
`/tmp/shared-lean-copy` appeared mid-session but was stale (Mathlib `c5ea003`, toolchain
v4.30-era) and was not used; the canonical fetch superseded it.

## Method (per target file)

1. Module docstring drafted in this report before Lean was touched.
2. `baseline` commit: declarations cut **by declaration boundary** from the census ranges on
   721fc82 (Hopf/ verified byte-identical to 721fc82), pasted verbatim with the source
   file-level pragmas; only import paths and `namespace` lines changed, each named in the
   commit message; SHA-256 of every source range recorded.
3. `doc` commit: module docstring + `/-! ### … -/` section headers ("No proof term changed.").
4. Lane-wide `rename` commit + transitional `Hopf/LibShims.lean` export shims (Q2).
5. Consumers re-routed by adding `import Lib.…` to the **earliest** consumer — the `Hopf/`
   import chain is strictly linear, so one line serves the whole downstream chain.
6. Gates per commit: `git diff --check`; census `--check` before / `--update` after;
   `lake build Lib.<Module>` then consumers.

## What moved (source range → target file, all byte-verbatim, SHA-256s in commit messages)

| target file | source (721fc82) | decls | commit |
|---|---|---:|---|
| `Lib/Algebra/Homology/MayerVietorisShortExact.lean` | DifferentialTopology 30922–31131 (`SmallChainBiprod`, whole prefix; census range ended one declaration short — `shortExactOfComplexes` moves with it, cut by declaration) | 19 | bd7a4b5 |
| `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | SingularHomology 86–868 (chains core + `ChainHomology` cycle-class API + cycle calculus) + 1019–1095 (finsupp presentation); extension: SphereTopology 7021–7243 (loop-homotopy chains) | 139 | cd31909, f0cd306 |
| `Lib/AlgebraicTopology/SingularHomology/ModuleHomology.lean` | SingularHomology 1863–2087 (`SingularMayerVietoris.ModuleHomology` morphism API) | 20 | 90685ed |
| `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` | SingularHomology 870–3658 — the plan's MayerVietoris/Subdivision/SmallChains targets landed as ONE file (see File-scope note) | 249 | 81c066b |
| `Lib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` | SingularHomology 3660–3834 + 4017–4040 | 26 | e997d6c |
| `Lib/Topology/Homotopy/Suspension.lean` | SphereTopology 331–824 (unreduced suspension construction) | 66 | ae79471 |
| `Lib/AlgebraicTopology/SingularHomology/Sphere.lean` | SphereTopology 86–329 (unit-sphere preliminaries) | 37 | 7f00f6e |
| `Lib/AlgebraicTopology/SingularHomology/Suspension.lean` | SphereTopology 826–1140 (suspension isomorphism + split-exact algebra; source order binds 870–1025 here) | 33 | f95df58 |
| `Lib/AlgebraicTopology/SingularHomology/Sum.lean` | SphereTopology 1142–1260 (disjoint sums, Hatcher Prop 2.6) | 28 | 553b934 |
| `Lib/AlgebraicTopology/SingularHomology/CircleProduct.lean` | SphereTopology 1260–2508 (S¹ topology, S¹×X Künneth, H_*(S¹), 3 `ModuleHomology` coherence lemmas — movable after MayerVietoris landed) | 118 | e52b9c9 |
| `Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean` | SphereTopology 2510–2562 + 6864–6900 + 16076–16126 (H_n(Sⁿ) ≅ ℤ, H_k(Sⁿ) = 0 — Cor 2.14 rows) | 22 | d43a61b |
| `Lib/Topology/OnePointCollapse.lean` | SphereTopology 13388–13480 (`SixSphereCube`) | 12 | 4a2897b |
| `Lib/AlgebraicTopology/SingularHomology/Coproduct.lean` | SphereTopology 15326–15705 (`ThreefoldHomologyStarCoproduct`) | 29 | 9cf8747* |
| `Lib/AlgebraicTopology/SingularHomology/LocalContributions.lean` | SphereTopology 15707–16074 subset (13 `DisjointOpenHomology`/`CoverLocalContributions` decls) | 13 | 7453cba* |
| `Lib/AlgebraicTopology/SingularHomology/Naturality.lean` | SphereTopology 13962-range `CoverNaturality` (30) + CuspFilling 15076–15346 (18) | 48 | 8bb00c0, 94513de |
| `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | SingularHomology 3836–4358 + 30894–31281 subset (47 of 65; see obstruction) | 47 | c924631 |

\* Coproduct and LocalContributions share commit 7453cba (one green unit; they were extracted
in one sweep and LocalContributions consumes Coproduct's imports).

**File-scope note (deviation from the plan, reason recorded).** The plan's three targets
MayerVietoris/Subdivision/SmallChains are one file: the source's own proof order is binding —
`exact_at_ambient` elaborates only after `smallInclusion_quasiIso` (small simplices,
Hatcher Prop 2.21), so exactness cannot precede small chains, and the reverse import order is
a cycle. A later refactor may split along the same order into an acyclic import chain.
Similarly the split-exact block (SphereTopology 870–1025) landed inside Suspension.lean
(consumed there by the contractible-cover and suspension-equiv blocks), and the Cor 2.14
computations got their own SphereHomology.lean (extending Sphere.lean would be an import
cycle: Sphere.lean is upstream of Suspension/CircleProduct, this block downstream).

**Hidden elaboration dependency found and documented.** `FirstHurewicz.ChainHomology`
does not elaborate in isolation from the singular-chain core (verified: fails standalone,
passes with SingularHomology 86–391 present; no declaration-level dependency). Pure moves
keep source order, so the whole 86–868 run landed in Chains.lean.

## Rename commit (1e8c699)

`PeriodTorusHigherHomology → SingularHomology`, `CuspCentralHomology → Suspension`,
`ThreefoldHomologyStarCoproduct → Coproduct`, `SixSphereCube → OnePointCollapse`,
`FirstHurewicz → SingularChains` (declaration-name prefixes inside Lib; paths become
`Mathoverflow1973.<New>.*`, the files' own dotted-name resolution convention kept).
Transitional shims: `Hopf/LibShims.lean` recreates the old dotted paths via `export`
(449 names; PeriodTorusHigherHomology ≈1,657 references in IntegralHomology alone), and every
Hopf module gains one `import Hopf.LibShims` line. De-shim is the owner's follow-up.
The other Lib namespaces (`SmallChainBiprod`, `SingularMayerVietoris`, `SphereHomology`,
`Degree.PassageHomology`, `Smale.LocalDegree`, `Smale.PuncturedRadial`) keep their names this
lane — none is in the mandated rename list; Mathlib-shaped renames for them belong with the
de-duplication pass (Q4) and are an open item.

## Honest obstructions (declarations left in `Hopf/`, exact lists)

1. **LinearSphereAction region (SphereTopology 16147–18066).** All of
   `Smale.LinearSphereAction.*` minus nothing — together with `Smale.SphereReflection.*`,
   `Smale.SpherePoint.*`, `Smale.ManifoldMorse.MorseSurgeryData.*`,
   `Smale.SuspensionReflection.*`, `NoExotic.IntLinearAutomorphism.*` — is welded to
   `Smale.MorseHandle` (DifferentialTopology, lane D1), `Smale.SphereReflection`,
   `Degree.LinearFramePaths` and the Morse-surgery structures (lanes F/G territory).
   Word-boundary dependency closure: only 3 of 140+ decls are movable in isolation — not
   worth a fragment file. Moves after D1/F/G land. Includes the probe theorem
   `Smale.LinearSphereAction.homology_eq_sign_smul` (probed in place; same statement).
2. **LocalContributions leftovers (21 decls).** `MorseSurgeryData.attachingCollapse*`,
   `.collapseOverlapMap*`, `.upperLevelInclusion`, `.bandSublevelHomeomorph`,
   `.attachingHomology_subsingleton_of_index`, `.lowerHomology_subsingleton_of_upper_and_index`,
   `SurgeryWindows.BandData*`, `.consecutiveBandData`,
   `.lower_homologyOne_subsingleton_of_indices`, `SublevelDisk.contractibleSpace`,
   `.homology_subsingleton`, `CoverLocalContributions.localMap`, `.connecting_sum` —
   reference `Smale.OnePointCover` (SphereTopology 11026–11878, lane E1) and
   `Smale.SublevelDisk` (5000–6556, lane E1). Move after E1.
3. **LocalDegree radial family (17 decls).** `radialCylinderHomeomorph` (+2 symm lemmas),
   `radialCylinderDiffeomorph`, `radialCylinderChart` (+3), `puncturedCylinderHomeomorph`,
   `cylinderLink`, `punctured_cylinder_endpoint_relation`, `punctured_cylinder_trace_relation`,
   `PuncturedRadial.toSphere`, `.deformation`, `.sphereHomotopyEquiv`,
   `LocalDegree.linearSphereEquiv`, `BoundaryData.normalizedMap` — reference
   `Smale.PartialChart.openInclusion`, `Smale.RadialExtension.direction`,
   `homeomorphUnitSphereProd` (glue outside every lane's census range; Lib cannot import
   Hopf). Their E1/F consumers stay green against the Hopf copies.
4. **Augmentation block (Hurewicz 15792–15994 + 23324–23422, 32 decls).** References
   `SecondHurewicz.SimplyConnected.*` and `SimplexGeometry.*` — lane C (Kimi) infrastructure;
   `*Hurewicz` blocks other than these two are out of lane A's scope, so the dependency
   cannot be moved by this lane. Moves after lane C. (Extraction was attempted and reverted;
   the file never reached a commit.)

## Gates (final state)

- `lake build` green for all 16 Lib modules, `Lib` root, every `Hopf` module through
  `Hopf.Final`, and `Solution` (8747 jobs). Wall times: SH rebuild ≈2m10s–2m30s;
  SphereTopology ≈1m30s; full consumer chain ≈8m20s; reference example 7.6s.
- `#print axioms` (Lib/AxiomAudit.lean):
  - `Mathoverflow1973.SingularMayerVietoris.exact_at_ambient`:
    `[propext, Classical.choice, Quot.sound]`
  - `Mathoverflow1973.SphereHomology.unitSphere_homology_subsingleton`:
    `[propext, Classical.choice, Quot.sound]`
  - `Mathoverflow1973.Smale.LinearSphereAction.homology_eq_sign_smul` (stayed in `Hopf/`;
    probed by `lake env lean` on a scratch file with `import Hopf.SphereTopology`,
    receipt below):
    `[propext, Classical.choice, Quot.sound]`
  - headline `Mathoverflow1973.mathoverflow_1973` (comparator check, direct):
    `[propext, Classical.choice, Quot.sound]`
- **Comparator caveat:** `lake exe comparator comparator/config.json` aborts in this
  environment — it shells out to `landrun`, which is not installed (`could not execute
  external process 'landrun'`). The substantive check was replicated directly: the headline
  theorem's axioms are exactly the permitted three (above). The comparator verdict itself
  could not be produced here.
- Census: baseline lowered 9408 → 8580 across nine extraction commits
  (`lib_stock_census --check` PASS at every commit); spent prefix entries removed:
  `SmallChainBiprod`, `Hopf/SingularHomology.lean:CuspCentralHomology`,
  `Hopf/SphereTopology.lean:CuspCentralHomology`, `ThreefoldHomologyStarCoproduct`.
- `git diff --check` clean at every commit.

## Open items

1. **DONE — module docstrings for all 16 files.** Each states the headline declaration's
   exact type, an outline naming the realizing declarations, main results, the Hatcher
   reference, and tags (commits e37b114, 1fdd9f0, acf40db, and the final ten-file doc
   commit 55432ab). Long `/-! ### -/` section-header passes inside the two large files
   (MayerVietoris, Chains) are folded into the per-declaration docstring pass.
2. **Per-declaration docstrings.** ~1,000 public declarations moved this lane carry no
   docstrings yet (target: 0 without). Bulk pass after this report; section-opening and
   headline declarations are named in each module docstring's outline.
3. **Lint.** No lint driver is configured in-tree (`#lint` scratch-file run pending);
   findings to be recorded here when run.
4. **De-shim.** `Hopf/LibShims.lean` + one import line per Hopf module are transitional (Q2);
   the owner's de-shim pass deletes them.
5. **Namespace renames for the non-mandated prefixes** (SmallChainBiprod,
   SingularMayerVietoris, SphereHomology, Degree.PassageHonology→LocalDegree-family,
   Smale.LocalDegree, Smale.PuncturedRadial) to Mathlib-shaped names, with the Q4
   de-duplication review against Mathlib's `ShortComplex.ModuleCat` cycle API (the
   `ChainHomology`/`ModuleHomology` API substantially overlaps
   `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`).
6. **Import minimization.** Baseline files import `Mathlib` wholesale; per-file minimal
   `public import` sets are a style pass (the reference example's history did the same).
7. **Obstructions 1–4 above** (rejoin after lanes D1/E1/F/G/C land, in that order of
   readiness).
8. **Comparator `landrun`** — needs the binary installed to produce the official verdict
   artifact; the axiom check it would perform passes.
9. **Universe lift** (all moved singular-homology statements are `(X : Type)`, universe 0 —
   kept per lane hazard note) — the plan's separate post-A pass.

---

# Lane D1 progress (same branch, continuing lanes in session order)

**Status: DT/SH/Recognition movable baselines landed (11 Lib files, green), module docstrings
landed, axiom receipts exact. Rename deferred (rationale below). Per-decl docstrings open.**

## What moved (source on 721fc82 → target, all byte-verbatim)

| target | source | decls | commit |
|---|---|---:|---|
| `Lib/Geometry/Manifold/Morse/Handle.lean` | DT 85–776 (MorseHandle model, BeltPassage, RegularValues) | 78 | 913716d |
| `Lib/Analysis/Calculus/MorseLemma.lean` | DT 777–2988 (perturbations, IsMorseOn, exists_morse_function, SmoothMorseLemma signed charts — Milnor Morse Theory Lemma 2.2) | 157 | 913716d |
| `Lib/Geometry/Manifold/Flow/Compact.lean` | DT 2990–3543 (flow construction, morse blocks, NoExotic partial-diffeo/IFT) | 29 | 913716d |
| `Lib/Geometry/Manifold/RegularLevel.lean` | DT 3544–3865 (RegularLevel — Lee Cor 5.14, letI idiom verbatim) | 20 | 913716d |
| `Lib/Geometry/Manifold/Morse/HandleAttachment.lean` | DT 3867–5335 (attachments, punctured handles, boundary pairs, RadialExtension) | 125 | 913716d |
| `Lib/Geometry/Manifold/Flow/HeightTranslating.lean` | DT 5337–6988 (global flow — Lee Thm 9.12, height translating) | 106 | 913716d |
| `Lib/Geometry/Manifold/Morse/Existence.lean` | DT 6990–9041 (smoothing, chart-map perturbation, existence — h-cobordism Thm 2.5) | 117 | 913716d |
| `Lib/Analysis/ODE/SmoothFlow.lean` | DT 18259–19186 (Degree.SmoothODE, coordinate fields) | 54 | 913716d |
| `Lib/Topology/Homotopy/HandleRetraction.lean` | SH 5310–5859 (Degree.Handle retraction onto core — Prop 0.16/§2.3) | 68 | 99ee04d |
| `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | ST 2595–2678 + 7325–8214 subset (sublevel transport — Thm 3.1) | 12 | de4b876 |
| `Lib/Geometry/Manifold/Morse/Index.lean` | ST 8216–8707 subset | 26 | de4b876 |
| `Lib/Geometry/Manifold/ChartedSpace/Transport.lean` | Recognition 1612–1640 (atlas transport — Lee Thm 4.5-adjacent) | 3 | 44c11ef |
| `Lib/Topology/Homotopy/CylinderHEP.lean` | Recognition 2090–2333 + 3197–3453 (I×Dⁿ ≅ D^{n+1}, HEP — Prop 0.16) | 40 | 44c11ef |

## Style deviation (recorded)

D1 files use the **classic header form** (`import Mathlib` + `noncomputable section`, no
`module`/`public import`/`@[expose]`): the moved proofs contain `rfl`/`change` elaborations
through `Diffeomorph`/`PartialDiffeomorph` structure literals that do NOT elaborate under the
module system in this toolchain (minimal repro: the same bytes are green in classic form and
red in module form — `translateChart_apply`). Mathlib itself is classic, so the files remain
PR-ready. Consequence: classic Lib files cannot be imported BY module Lib files, so D1 files
that consume classic D1 files are classic too. Lane A files remain module-form (they were
written before this was known and are green).

## D1 honest obstructions (left in `Hopf/`)

1. **ST 7325–8708 majority (85 decls)** — `ManifoldMorse.MorseSurgeryData`/`SurgeryWindows`
   consumers, `Hemisphere`/`DiskDouble`/`TwoDiskDecomposition`/`SublevelDisk` family — welded
   to `Smale.MorseSurgeryData` (DT 10391, outside all lanes' ranges) and `SublevelDisk`/
   `Hemisphere.Ambient` (ST 5000–6556, lane E1). Join after E1/F/G.
2. **Recognition 11149–11254 Reeb block (4 decls)** — `nonempty_homeomorphSphere_of_two_critical_points`
   needs `Smale.Hemisphere.Sphere` (lane G). Probe still exact (below).
3. **Recognition leftovers** in the D1 ranges that reference the above.

## D1 axiom receipts

- `Smale.ManifoldMorse.exists_morse_function`: `[propext, Classical.choice, Quot.sound]`
- `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn`: `[propext, Classical.choice, Quot.sound]`
- `Smale.ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits`:
  `[propext, Classical.choice, Quot.sound]`
- `Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points` (probed via scratch
  `import Hopf.Recognition`): `[propext, Classical.choice, Quot.sound]`

## D1 rename decision (deviation recorded)

No mandated rename list for D1. The `Smale.*` root is shared with lane F/G material that
stays in `Hopf/`; renaming D1's slices alone would split one namespace across two roots and
multiply shim surface. Twins are named per file in the docstrings/messages (MorseLemma →
Milnor Morse Theory Lemma 2.2 presentation; RegularLevel → lee13 Cor 5.14; SmoothFlow →
lee13 Thm 9.12; HandleRetraction/CylinderHEP → hatcher02 Prop 0.16). A namespace-normalizing
rename (`Smale.ManifoldMorse.* → Morse.*` etc.) belongs to the post-F/G pass with the de-shim.

## D1 open items

Per-declaration docstrings for the ~750 moved D1 declarations; lint; de-shim; the
`MorseSurgeryData`-web rejoin after F/G; `landrun` for the comparator artifact.

---

# Lane H progress (same branch)

**Status: all movable H baselines landed (8 Lib files, ~470 declarations, green), module
docstrings installed, axiom receipts exact. Per-decl docstrings open.**

## What moved (source on 721fc82, cut BY NAME out of the SpecialPeriods project namespace)

| target | source | decls | commit |
|---|---|---:|---|
| `Lib/Geometry/Manifold/Instances/RiemannSphere.lean` | PeriodConstruction RiemannSphere 8012–8082 + TwoAffineCharts 7758–8011 | 37 | (H baseline) |
| `Lib/Analysis/Complex/Mobius.lean` | AnalyticFillings RiemannSphere.* 3581–4019 | 54 | (H baseline) |
| `Lib/Analysis/Complex/SchwarzReflection.lean` | AnalyticFillings SchwarzReflection.* | 16 | (H baseline) |
| `Lib/Analysis/Complex/RiemannMapping.lean` | AnalyticFillings RiemannMapping.* + TriangleRiemannNormalization.* + RiemannBoundary.* | 181 | (H baseline) |
| `Lib/Analysis/Complex/RiemannMapping/Steps.lean` | AnalyticFillings _root_.* steps 4711–5413 | 31 | (H baseline) |
| `Lib/Analysis/Complex/Cousin.lean` | PeriodConstruction HolomorphicCousin.* 15593–17278 | 95 | (H baseline) |
| `Lib/Analysis/Complex/SquareRoot.lean` | PeriodConstruction AnalyticRootCover(+Continuation) + 1 SpecialPeriods step | 62 | (H baseline) |
| `Lib/Geometry/Manifold/Complex/Biholomorph.lean` | AnalyticFillings TriangleUniformizationGluing.{3 lemmas + supports} | 8 | (H baseline) |

Commit: 685fd91 (baselines), then docstring commit.

**File-scope notes.** (1) `BoundaryExtension.lean` merges into `RiemannMapping.lean`:
`RiemannBoundary` and `RiemannMapping` interleave-depend (46 qualified references one way,
3 the other) — lane-A MayerVietoris precedent. (2) `TwoAffineCharts` pulled forward from
lane I to unblock the `RiemannSphere` atlas (27 decls, Mathlib-only deps). (3)
`DBar.lean` folds into `Cousin.lean` (the Cauchy–Green ∂̄ machinery is the Cousin proof).
(4) `SpecialPeriods.exists_analytic_unit_root` moved with its SquareRoot consumers, prefix
kept (deviation — the SpecialPeriods namespace is otherwise project code).

## H honest obstruction

The `RiemannMapping` **triangle tail** (114 decls: `triangleDomain`, `triangleMap`,
normalization/Ford-cycle machinery) is project code per the plan's STOP-at-5579 note (seed
closure on `SpecialPeriods`/`triangle*`); it stays in `Hopf/LCP/AnalyticFillings.lean`.

## H axiom receipts

- `RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`:
  `[propext, Classical.choice, Quot.sound]`
- `HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution`:
  `[propext, Classical.choice, Quot.sound]`
- `AnalyticRootCover.exists_analytic_square_root` (+ `_ball`): `[propext, Classical.choice, Quot.sound]`
  (the plan's `..._on_of_even_zeros` spelling does not exist in the source; the two actual
  root-existence theorems are probed)

## H open items

Per-declaration docstrings; import minimization; the Q6 upstream Mathlib PR for the two
duplicated steps; comparator `landrun`.

---

# Lane D2 progress (same branch)

**Status: all movable D2 baselines landed (6 Lib files, ~430 declarations, green), module
docstrings installed, axiom receipt exact. Per-decl docstrings open.**

## What moved (source on 721fc82 → target, all byte-verbatim)

| target | source | decls | commit |
|---|---|---:|---|
| `Lib/Geometry/Manifold/WhitneyEmbedding.lean` | DT 10445–11285 subset (NativeEuclideanEmbedding — Lee Thm 6.15; partial-diffeomorphism IFT lemmas) | 48 | 488c283 |
| `Lib/Geometry/Manifold/VectorBundle/ProjectionBundle.lean` | DT 11287–11600 (NoExotic.ProjectionBundle + intertwiners — Lee Thm 6.24) | 22 | 488c283 |
| `Lib/Geometry/Manifold/Collar.lean` | DT 11602–14111 subset (collars, SupportedDiffeomorph, DiskFraming, tubular neighbourhood, SmallPerturbation, SphereCoordinates) | 137 | 488c283 |
| `Lib/Topology/Homotopy/HandleRetraction.lean` | SH 5310–5859 (Degree.Handle retraction) | 68 | 720a5ae (listed under D1 lane execution, D2 dependency) |
| `Lib/Topology/Homotopy/CellAttachment.lean` | SH 28353–29652 subset (132 decls: EmbeddedCellAttachment, HandleCore*, DiskAnnulus, OuterDisk) | 132 | cf18527 |
| `Lib/Geometry/Manifold/Morse/CellStructure.lean` | Recognition 2580–3161 + 3538–3808 subset (59 decls: MorseCells, FiniteCells — Milnor Morse Theory Thm 3.5) | 59 | 4273335 |

**File-scope notes.** Tubular.lean folds into Collar.lean (source-order web); the
ProjectionBundle split keeps the plan's target name; D2's SH cell-attachment work also
UNBLOCKED lane A's recorded ST EmbeddedCellAttachment obstruction (the MorseHandle dep is
now in Lib — the ST copies were re-extracted as part of D1's Chains extension and D2's
CellAttachment).

## D2 honest obstructions (left in `Hopf/`)

1. DT tail (26 decls) depending on `Smale.MorseSurgeryData`/`Smale.Hemisphere.*` (F/G).
2. `Degree.MorseCells.built_of_compact_smooth_manifold` + `built_upper_sublevels`
   (Recognition) referencing `exists_regularSublevelHomotopyEquiv` (E1) and
   `SpecialPeriods.Threefold.chartedSpace` (project).
3. SH `MorseSurgeryData.*` (14 decls, F/G web).
All listed with seeds-based closure evidence; join after E1/F/G.

## D2 axiom receipt

- `Smale.exists_tubularNeighborhood_in_open_of_embedded_closedBall`:
  `[propext, Classical.choice, Quot.sound]`
  (the plan's `Smale.NativeEuclideanEmbedding.exists_tubularNeighborhood` spelling names a
  different, more specialized lemma — also present, at Collar.lean:530)

## D2 open items

Per-declaration docstrings; import minimization; lint; the E1/F/G rejoin; `landrun`.

---

# Lane I progress (same branch, session order A → D1 → H → D2 → I)

**Status: 4 of ~14 units landed (green); the remainder is enumerated below with exact
resume configs (cfg files in ~/s6-notes/hopf-lib-a/).**

## Landed

| target | source | decls | commit |
|---|---|---:|---|
| `Lib/Geometry/Manifold/Instances/RiemannSphere.lean` | PeriodConstruction TwoAffineCharts 7758–8011 + RiemannSphere 8012–8082 (pulled forward from lane I by lane H to unblock the atlas) | 37 | (H baseline) |
| `Lib/Topology/Algebra/FreeActionLocus.lean` | PeriodConstruction FreeActionLocus.* | 13 | 867880d |
| `Lib/Geometry/Manifold/Quotient/LocalOrbit.lean` | PeriodConstruction LocalOrbitQuotient.* subset | 17 | 91dc733 |
| `Lib/Geometry/Manifold/Quotient/Atlas.lean` | PeriodConstruction OnePointAtlas.* + BranchedQuotientAtlas.* subset | 22 | 91dc733 |
| `Lib/Topology/MappingTorus/Basic.lean` | LocalModels MappingTorus.* 6899–8394 | 76 | 79211df |

## Remaining lane I units (resume order, each = one cfg + delete + build + commit)

1. `MappingTorus/HomologyCover.lean` ← BoundaryTopology `MappingTorusHomology.*` 3988–4609 (58)
2. `MappingTorus/Wang.lean` (+ `WangAlgebra.lean` split if desired) ← IntegralHomology `MappingTorusHomology.*` 7576–8688 (105) — axiom probe `wang_exact_at_mappingTorus`
3. `GroupTheory/SplitExtension.lean` ← BoundaryTopology `SplitGroupExtension.*` (13) — probe `SplitGroupExtension.mulEquiv`
4. `GroupTheory/PresentedGroup/CentralTwist.lean` ← BoundaryTopology `TwistGroup.*` (21)
5. `FiberBundle/TwoOpenTransition.lean` ← BoundaryTopology `TwoOpenTransition.*` (45)
6. `Topology/Covering/Quotient.lean` ← LocalModels `CoveringQuotient.*` (17) + DiscreteQuotient (13)
7. `Topology/Covering/DiagonalQuotient.lean` (+ `FundamentalGroup/DiagonalQuotient.lean`) ← AF `DiagonalQuotient.*` (41) + BT `DiagonalQuotient.*` (36)
8. `Homotopy/SublevelRetraction.lean` ← LocalModels `ThreefoldHomologyFinitenessRetraction.*` (22; rename per lane task)
9. `Homotopy/LocalCollapse.lean` ← CuspFilling `CuspRetraction.Patching.*` 490–631 (11; rename per lane task)
10. `Quotient/Covering.lean` ← CuspFilling `InvariantSubsetQuotient.*` (14) + `CoveringOrthant.*` (6) + `ProductRestriction.*` (5)

## Lane I honest obstructions so far

- LocalOrbitQuotient.localHomeomorph + 3 atlas decls: welded to
  `SpecialPeriods.triangleGeometricAction` (project) and
  `BranchedQuotientAtlas.contDiffAt_transition_of_lift`
  (Hopf/LCP/Specialization.lean 14450, outside all lanes' ranges).

---

# Lane I, session 2 addendum (HomologyCover landed; Wang blocked)

## Landed this session

- `Lib/Topology/MappingTorus/HomologyCover.lean` (58, d92f3cf)
- `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` (58, 5e9a74e — pull-forward)
- `Lib/AlgebraicTopology/SingularHomology/CrossInsert.lean` (3, 5e9a74e — pull-forward)

## Wang (`MappingTorus/Wang.lean`, IH 7576–8688, 105 decls): BLOCKED

Closure requires, besides landed material, the cross-product / circle-path cluster:
- `PeriodTorusHigherHomology.crossProduct*` + `chainBilinear*`/`homologyDesc*`/
  `homologyLinearMap*` in Hopf/Hurewicz.lean (~106 decls, dense `attribute
  [local instance] integerTensorModule in` runs), and
- `PeriodTorusHigherHomology.positiveCircleCross`, `CirclePaths.*`,
  `twoChainSmallCycle*`, `connectingHomomorphism_twoChain`,
  `crossProductEdge_path_boundary` in Hopf/LCP/CuspFilling.lean.

First extraction attempt ended in a proof-script rewrite loop (rejection test 5).
This cluster needs its own declaration-level Stage-4 cut (proposed target
`Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`) before Wang can move.
The four `LinearMap.map_smul` proof sites that failed under the local
`integerLinearMapModule` instance are the seam to re-derive first.

## Tooling

- `~/s6-notes/hopf-lib-a/dag.py` + `dag_gen.py` → `DAG.md`: computed import DAG
  (dotted-name references over 721fc82 bytes, rename-mapped, family over-
  approximation). Every future unit's import list is now precomputed.
- extract.py still mangles one-line `attribute [local instance] X in` in two
  ways (head stripped + indented). Post-extract normalizer used:
  `re.sub(r'^\s*(?:attribute \[local instance\] )?((?:\w+\.)+integer(?:Tensor|LinearMap)Module) in\s*$', r'attribute [local instance] \1 in', ...)`.
  Fix the hoister before the next unit.

---

# Lane E1 scoping (session 3; no lane-E1 commit landed)

E1 is the largest lane: ~700 declarations over 22 families (census in
~/s6-notes/hopf-lib-a/, cfgs cfg-tc/cfg-lcyl created). Dependency findings
from the DAG closure scans (dag.py with HOPI mapping):

- `Degree.FlowTimeChange` (55) is mid-stack: its closure needs
  FlowSuspension native cylinders, FlowCancellation levelBasin,
  LocalFunctionReplacement, and MorseCancel band normalization (23 refs).
- `Degree.FlowSuspension` (91) is also mid-stack: 29 Hopf refs incl.
  MorseCancel.Model and the cubic-cylinder cluster.
- The true base layer is the **cubic model cluster**: MorseCancel.Model +
  cubic descent/flow-cylinder + AxisCoordinates + Regular/Signed height
  coordinates + Smale.PartialChart — closure of 197 declarations.

**Proposed E1 unit order (resume here):**
1. `Morse/Cubic.lean` (+`CubicFlow.lean`) — the 197-decl cluster (one
   baseline commit; the plan's finer file split should follow the
   declaration cut, not precede it)
2. `Flow/LevelCylinder.lean` — FlowSuspension (91) [draft exists]
3. `Morse/Cancellation-support` — FlowCancellation (71) +
   LocalFunctionReplacement (14)
4. `Flow/TimeChange.lean` — FlowTimeChange (55) [draft exists]
5. `Flow/PhaseChart.lean` — TransverseGerms (32); `FieldChartGluing.lean` (13)
6. `Morse/Rearrangement.lean` — MorseRearrangement (74) +
   SupportedDiffeomorph (19) + PartialChart (2)
7. `Morse/Cancellation.lean` — MorseCancel remainder (~124) + AdaptedWindows (13)
8. Splits for IndexOrdering / SuperfluousMinima / Birth / Duality follow the
   landed declaration cut.

Drafts (red, unlanded) preserved under ~/s6-notes/hopf-lib-a/drafts/.
Axiom probes pending: exists_morse_rearrangement_of_no_connection,
cancel_of_transverse_level_isotopy, exists_excellent_indexed_morse_birth.

---

# Lane E1 unit-1 attempt (session 3 close): BLOCKED at the SurgeryWindows web

The 197-decl cubic closure grew to 291 under definition-closure (the full
MorseCancel/AdaptedWindows/AxisCoordinates/PartialChart neighborhood) and
still fails: the kept material references `AdaptedWindows` (the band
Lyapunov structure), whose family is interleaved with the MorseSurgeryData /
SurgeryWindows web — the ownerless obstruction recorded at the D2 stage.

Consequence: lane E1's base layer is coupled to the SurgeryWindows decision
(the same one gating lane C's augmentation and lane G). Until that web gets
its Stage-4 treatment (owner decision: rename-and-move as generic Morse
window data, or keep as project code with an interface seam), the movable
E1 units are the flow-side leaves only, and each of those needs the cubic
core. E1 therefore joins C/F/G in the blocked column.

Drafts preserved: drafts/Cubic.lean.draft (291-decl extraction),
drafts/TimeChange.lean.draft (55), drafts/LevelCylinder.lean.draft (91),
plus cfg-tc/cfg-lcyl/cfg-cubic and the definition-closure script inline in
the session history. Resume order in the previous section stands, with the
amendment: unit 1 requires the SurgeryWindows decision first.

---

# Lane B progress (session 3)

## Landed

- `Lib/AlgebraicTopology/FundamentalGroup/SimplyConnectedCover.lean` (9, da29618)

## Drafted, not landed (preserved in ~/s6-notes/hopf-lib-a/drafts/)

- `VanKampen.lean` — 114 BT decls + 51 HW family members. The family's
  three STRUCTURES (LocalPathValue, PathValue, TwoOpenCover) live in
  Hurewicz.lean while their 114 lemmas live in BoundaryTopology.lean; the
  cfg (cfg-vk.json) assembles both. Last build: 26 errors, all cross-family
  (`SimplyConnectedCover.trans_mem` — now landable — and
  `TriangleRegularBaseFundamentalGroup.basedLoop`).
- `TwoSimplyConnectedCover.lean` — 31 decls (19 HW + 12 BT). The closure
  sweeps in project-welded `SpecialPeriods.EllipticAttachingMeridians`
  material via `LoopSquare`; name-based weld rules needed (the text-based
  WELD regex both over-matches names like `adaptedSurgeryWindows` and
  under-matches pure-namespace welds).

## Resume (next session)

1. Land `TwoSimplyConnectedCover.lean`: cfg-tri.json, HW block (19) + BT
   block (12); refine weld to NAME-based prefixes
   (SpecialPeriods./EllipticAttachingMeridians.) plus text-based for the
   recorded web; expect ~2 build rounds.
2. Land `VanKampen.lean`: cfg-vk.json; imports SimplyConnectedCover +
   TwoSimplyConnectedCover once landed.
3. Then EuclideanSphere (14) → `Lib/Topology/InstanceSpheres.lean` per plan,
   and the SH 18734–19048 remainder.
