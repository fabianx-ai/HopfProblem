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

## Wrapper removal (Mathoverflow1973): attempted, reverted, resumable

WIP preserved: `~/s6-notes/hopf-lib-a/wrapper-removal-wip.diff` (4,084 lines)
and `~/s6-notes/hopf-lib-a/wang-wrapper-attempt.lean`.

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

1. Recreate Wang.lean from the preserved attempt (or re-run the family
   closure mover) and land it: `lake build Lib` green, consumers via shims.
2. Regenerate LibShims: one `export <Family> (<bare names>)` line per family,
   plus the CuspCentralHomology/CuspRetraction.Patching alias blocks as
   `abbrev`s.
3. Re-apply the wrapper strip to Lib/ (79 files), strip `Mathoverflow1973.`
   from LibShims and Hopf/ (36 + references), migrate AxiomAudit probes.
4. Full chain green -> single commit.
