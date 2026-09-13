# E2 Axis-5 typed-ledger review (fresh-context subagent)

Head: 84d9450 (lib/textbook-extraction-muse-i3)
Scope: the typed ledger in `Lib/docs/E2.md` (§15, lines 568–971) — verbatim
signature check, coordinate check, current-names check.

## Per-entry table (22 source-cited rows + 1 proposed decl)

| # | Decl | Cited coord | Actual coord | Status |
|---|------|------------|--------------|--------|
| 1 | `RegularValues.exists_null_exceptional_values_manifold` | Transversality/Basic.lean:288 | :288 | VERBATIM |
| 2 | `TransverseCoordinates.exists_null_exceptional_native_translations` | :365 | :365 | VERBATIM |
| 3 | `TransverseCoordinates.dense_native_translations` | :415 | :415 | VERBATIM |
| 4 | `NativeTransversality.exists_ambient_transverse_diffeomorph` | Morse/Rearrangement.lean:2723 | :2723 | VERBATIM |
| 5 | `GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range` | Morse/SurgeryWindows.lean:396 | :396 | VERBATIM |
| 6 | `GeneralPosition.exists_disjoint_smooth_map_homotopicRel` | Morse/SurgeryWindows.lean:431 | :431 | VERBATIM (ends `:=`, correct) |
| 7 | `SupportedDiffeomorph.IsotopicToIdentity` | Morse/Cancellation.lean:3614 | :3614 | VERBATIM (ends `: Prop :=`) |
| 8 | `SupportedDiffeomorph.SupportedRelativeIsotopy` (structure, all 7 fields) | Morse/Cancellation.lean:3685 | :3685 | VERBATIM |
| 9 | `SupportedDiffeomorph.SupportedRelativeIsotopy.extension` (full `where` block) | Transversality/Basic.lean:1122 | :1122 | VERBATIM |
| 10 | `SupportedDiffeomorph.exists_supported_isotopy_extension` | :2633 | :2633 | VERBATIM |
| 11 | `DiskShrinking.exists_embedded_disk_isotopy_of_same_center` | :2794 | :2794 | VERBATIM |
| 12 | `SupportedDiffeomorph.exists_supported_pointMoving` | :2839 | :2839 | VERBATIM |
| 13 | `SupportedDiffeomorph.exists_pointMoving_of_path` | Immersion/Relative.lean:332 | :332 | VERBATIM |
| 14 | `MorseCancellation.exists_isotopic_pointMoving_of_path` | Immersion/Relative.lean:208 | :208 | VERBATIM (current name confirmed) |
| 15 | `ManifoldImmersion.exists_immersion_on_compact_rel` | :1635 | :1635 | VERBATIM |
| 16 | `ManifoldImmersion.exists_compact_embedding_of_immersion` | :2017 | :2017 | VERBATIM |
| 17 | `ManifoldImmersion.exists_immersion_on_compact_rel_general` | none (G-E2) | absent from source | NEW — properly labelled "**new mathematics, NOT a move**" (E2.md:877); its comments cite only helper locations (:1635, :2697/2701, :2930/2973 — all verified), no false source claim |
| 18 | `sphereMap_nullhomotopic_of_dim_lt` | Hopf/SingularHomology.lean:4473 | :4473 | VERBATIM |
| 19 | `sphere_sphere_nullhomotopic` | :4488 | :4488 | VERBATIM (ends `:=`, correct) |
| 20 | `isDiscrete_transverse_intersections` | :1979 | :1979 | VERBATIM |
| 21 | `finite_transverse_intersections` | :2000 | :2000 | VERBATIM |
| 22 | `exists_short_embedded_arc` | :8654 | :8654 | VERBATIM |
| 23 | `exists_embedded_connecting_arc_avoiding_finite_dim_two` | :8715 | :8715 | VERBATIM |

Secondary comment coords verified OK: Basic.lean:219/234 (helpers), :2874
(`exists_open_pointMoving`), Rearrangement.lean:2752
(`exists_ambient_disjoint_diffeomorph_of_dimension`), SurgeryWindows.lean:451
(`ImageComplement.domain`), Cancellation.lean:3697/3708/3716 (projection
lemmas), Relative.lean:67/185/312/385/983/1973/2035/2098/2697/2701/2930/2973,
Collar.lean:1638, Existence.lean:2159, SH:4418/4428/8654–8714/8774–8780,
Basic.lean:2198/2679/2758.

## Current-names check — CLEAN

No `Suspension.topSus`, `SecondHurewicz.*`, `HigherHurewicz.*`,
`PeriodTorusHigherHomology.CircleTopology`, `MorseCancel.*`, `Smale.*`, or
`SixSphere` anywhere in E2.md. `MorseCancellation.*` at ledger line 830 is the
current source spelling (Relative.lean:208); the NB at lines 836–838 correctly
flags the prefix as a census artifact.

## Findings (all repaired in the subsequent commit)

1. **Stale comment/table coordinates** (mid-proof or wrong-decl lines; column
   header says "Source declaration starts"):
   - E2.md:526 (E1 row): `Basic.lean:176, 230` — stale for **234** and **288**
     (a uniform −58 pre-insertion shift).
   - E2.md:527 (E2 row) **and** ledger comment E2.md:627: `Basic.lean:357` —
     stale for **415** (`dense_native_translations`); 357 is mid-proof inside
     `surjective_sheetDifference_iff` (338–363).
   - E2.md:531 (E6 row) **and** ledger comment E2.md:734: `Basic.lean:2550` —
     stale for **2633** (`exists_supported_isotopy_extension`); 2550 is
     `DiskShrinking.family_one_inner`.
   - E2.md:532 (E7 row): `Basic.lean:2675` — stale for **2758**
     (`exists_disk_chart_isotopy`); 2675 is mid-proof inside the 2633 decl.
     (2679 is correct.)
2. **Stale-path citation**: E2.md:1025 — `~/muse-env.sh`,
   `/tmp/E2_Astra_RepairCheck.lean` in the historical astra
   repair-verification note. It records a past run accurately (probe deleted);
   flagged under the no-off-tree-paths rule. **Annotated as a historical run
   record in the repair commit.**
3. **Anchor staleness**: header claimed coordinates current at `840aef4`;
   HEAD at review time was `84d9450`. All row coords still verified —
   cosmetic only. **Re-stamped in the repair commit.**
4. Unverifiable-in-repo: `Mathlib/Geometry/Manifold/SmoothApprox.lean:107`
   (line 138) — Mathlib not vendored; consistent with prior astra review.

All 22 signature rows are verbatim at correct row-level coordinates; the
ledger's core is sound. The defects were residual coordinate drift the prior
closing review believed fully corrected — also present inside the ledger
section's own group comments (627, 734) — plus the flagged stale path strings,
against the doc's claim "All coordinates below are current."

## Verdict

```
Verdict: NO-GO — residual stale coordinates (Basic.lean:357→415, :2550→2633,
:176→234, :230→288, :2675→2758) in the §13 table and ledger comments at
E2.md:627/734, plus stale `~/`/`/tmp/` citation at E2.md:1025; all 23 signature
rows themselves are verbatim at correct coordinates.
```
