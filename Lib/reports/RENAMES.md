# Rename ledger (item 9)

## Landed

| commit | rename | scope | Mathlib twin |
|---|---|---|---|
| 55d76ce | `FundamentalGroupVanKampen` -> `FundamentalGroup.VanKampen` | 163 decls, 8 Hopf refs | `Topology.FundamentalGroupoid.VanKampen` |
| 05b5d14 | `MorseCancel` -> `MorseCancellation` | 1,487 refs, 10 files | `Mathlib/Geometry/Manifold/Morse/Cancellation.lean` (new) |
| 31124fc | `NoExotic.` prefix dropped | 211 refs, 14 files | `Mathlib/Geometry/VectorBundle/ProjectionBundle.lean` (new) + per-family |
| 31124fc | `Degree.` prefix dropped | 2,315 refs, 256 families | `Mathlib/AlgebraicTopology/LocalDegree.lean` (new) + per-family |

Recipe (validated): boundary-aware regex rename (`(?<![A-Za-z])NS\.` — the naive
string replace glued compound namespaces like `LocalDegree`, repaired from the
HEAD name map) -> `lake build Lib` -> full consumer chain -> commit with twin.

## Landed (continued)

| commit | rename | scope | Mathlib twin |
|---|---|---|---|
| ff89376 | `Smale.` prefix dropped | 11,687 refs, 168 families, 43 files | `Mathlib/Geometry/Manifold/Morse/*` (new), `Mathlib/Geometry/Manifold/Transversality/*` (new) |
| ff89376 | Hopf disambiguations | Hopf DiskCone -> SphereCone (17+6 refs, distinct from HandleRetraction's DiskCone); Recognition SixSphere -> MetricSixSphere (33 refs, distinct from the SingularHomology SixSphere family) | — |

Name confirmations (no rename needed; twins recorded): `SingularMayerVietoris`
(twin `Mathlib/AlgebraicTopology/SingularMayerVietoris.lean`, new),
`SphereHomology` (`Mathlib/AlgebraicTopology/SphereHomology.lean`, new),
`RiemannMapping` (`Mathlib/Analysis/Complex/RiemannMapping.lean`, new),
`HolomorphicCousin` (`Mathlib/Analysis/Complex/Cousin.lean`-adjacent, new),
`MappingTorus*` (`Mathlib/Topology/MappingTorus/`, new).

## Wrapper removal (Mathoverflow1973): attempted, reverted, resumable

The off-tree WIP artifacts are not included in this repository; the findings
and resume recipe below record the attempt.

Findings from the attempt (Lib side was GREEN, zero errors, zero Mathlib
root-name collisions across 79 files — the hard part works):

1. The failure seam is Hopf-side: LibShims' self-export blocks
   (`namespace N / export N (...) / end N`) became invalid once the wrapper
   was gone, and deleting them removed the bare-name lifting that Hopf
   consumers rely on (`twoPunctureSet`, `linkingSphere`, ...).
2. The Wang-family cone (PassageHomology./MappingTorusHomology., 117 decls,
   plus CirclePaths/PartialChart/Elliptic closure, ~50 more) must land in
   `Lib/Topology/MappingTorus/Wang.lean` BEFORE the wrapper removal, so
   LibShims can be regenerated with bare-name exports per family.

## Resume recipe

1. Recreate Wang.lean from the source families and land it: `lake build Lib` green, consumers via shims.
2. Regenerate LibShims: one `export <Family> (<bare names>)` line per family,
   plus the CuspCentralHomology/CuspRetraction.Patching alias blocks as
   `abbrev`s.
3. Re-apply the wrapper strip to Lib/ (79 files), strip `Mathoverflow1973.`
   from LibShims and Hopf/ (36 + references), migrate AxiomAudit probes.
4. Full chain green -> single commit.

## Open rename and record discipline

- `Suspension.topSus`: choose the type name against its Mathlib twin under
  `Mathlib/Topology/Homotopy/`, then rename again; a type is not called `topSus`.
  The final name is not yet settled.
- Rename commits must not rewrite another seat's ledger or `Lib/reviews/*`.
  Historical names remain in the record; this ledger carries the rename map.

Record fixes: GLM seat, run by Devin/Astra, based on upstream `37fc1de8`.

## Current-tree name confirmations (2026-09-13, GLM seat run by Devin/Astra)

Checked against pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The earlier entries labelled `new` describe proposed destinations, not proof
that those files exist in Mathlib. Each confirmation below records the actual
existing reference and leaves representation/API generalization separate.

### SingularMayerVietoris — retain the family name

Existing reference: `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`,
which defines `AlgebraicTopology.singularChainComplexFunctor` and
`singularHomologyFunctor`. The local extension is
`Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean`: its two-open-cover
sequence and exactness API are specifically singular Mayer–Vietoris, so the
family name remains informative. The proposed upstream destination is
`Mathlib/AlgebraicTopology/SingularHomology/MayerVietoris.lean`, not an
already-existing file. No replacement theorem in the reference is asserted.

Decision: confirm `SingularMayerVietoris`; no rename, statement or proof change.
Receipt: census **2,287 → 2,287**, prefix list unchanged; this commit changes
only this ledger. Module/public-section and coefficient generalization are
separate upstream-alignment work, not implied by name confirmation.
