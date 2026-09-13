/-! Review-A item 5: this file was split out of the monolithic lane report on
branch `lib/A-surgerywindows-split` (off bda000e). Corrections from review A check 10 are
applied inline (marked **[corrected]**). Provenance receipts for all lanes: `Lib/reports/RECEIPTS.md`.
-/

# Lane A report — singular homology core (Hatcher §2.1–2.2, 2.B)

**Branch:** `lib/A-singular-homology` off `lib/textbook-extraction`. **Move type:** pure move.
**Status: baselines complete (everything movable landed, green), rename landed, gates green,
module docstrings landed for all 16 files; per-declaration docstrings, lint, and de-shim are
the named remaining work (see Open items).**

## Toolchain

`leanprover/lean4:v4.33.0` via elan; Mathlib pinned `db584cd` (v4.33.0) fetched with
`lake exe cache get` (never built from source). Reference example
`Lib.AlgebraicTopology.Hurewicz.*` builds in **7.6 s wall** (documented: 8 s).
**[corrected]** The shared Lean copy is at Mathlib `db584cd6d4` with the v4.33.0
toolchain — the earlier report's "stale v4.30-era" claim was wrong (review A check 10.1).

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

## What moved (source range → target file, all byte-verbatim)

**[corrected]** Receipts now live in `Lib/reports/RECEIPTS.md` (item 2): per contiguous
declaration-boundary run, `721fc82 file:range → SHA-256 → target → baseline commit`, verified
reproducible. The commit hashes below that do not resolve on the integration branch (review A
check 10.3) are superseded by RECEIPTS.md; the true per-file baseline commits are recorded there.

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
(541 names; **[corrected]** was 449, review A check 10.7; PeriodTorusHigherHomology ≈1,657 references in IntegralHomology alone), and every
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

## Current linear-sphere-action probe landing (GLM seat run by Devin/Astra)

The exact remaining probe closure has 35 source declarations: one radial
normalization map in SingularHomology and 34 linear-action and reflection
lemmas in SphereTopology. Their original positions at `721fc82` lie inside
the A ranges in `TASK-LIB-GLM.md`. The historical whole-family obstruction
is superseded for this probe closure; this is not a claim that every other
historical A remainder has moved.

They move to `Lib/AlgebraicTopology/SingularHomology/LinearSphereAction.lean`.
The only changes inside declaration bodies are three explicit alias maps:
`Suspension.topSus → Suspension`,
`PeriodTorusHigherHomology → SingularHomology`, and
`CuspCentralHomology.contractibleCoverConnecting_injective →
Suspension.contractibleCoverConnecting_injective`. These resolve existing
Hopf spellings to the canonical Lib API; the mathematics and propositions
are unchanged. Source and normalized-target hashes are recorded separately
in `Lib/reports/A-linear-sphere-provenance.json`; this is not a claim of
literal byte identity before that name map.

Verification for this boundary:

- All 35 source hashes and normalized hashes match; each normalized declaration
  occurs exactly once in the target. Source files differ only by the recorded
  removals, explicit imports and blank-line cleanup.
- `Lib.lean` registers the module; both source consumers import it explicitly.
- `lake build Lib Solution S6Shortcuts S6 Challenge`: exit 0 (8840 jobs),
  on the final documented tree; the earlier pre-documentation focused build
  of the new module and `Hopf.SphereTopology` also passed.
- `lake env lean Lib/AxiomAudit.lean`: exit 0. The linear-sphere probe and
  the A/B/D1/D2/E1 headline probes use exactly
  `[propext, Classical.choice, Quot.sound]`.
- The standalone Lib-only linear-sphere probe passed with those same axioms.
- Stock census: **2234 → 2199**; `--check` and the Lib import guard pass.
- `git diff --check`: clean.

This closes the remaining A probe extraction in this round, not every
historical A follow-up. Wang transfer formulas and wrapper removal remain
blocked on C/J-owned prerequisites, as recorded in `Lib/reports/I.md`.

