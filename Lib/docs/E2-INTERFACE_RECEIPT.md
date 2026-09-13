# Lane E2 — interface receipt (Axis-5 probes, first pass — historical)

Seat: muse. Base: branch `lib/textbook-extraction`, probe run on top of
`0c48e7b` (post J-C1 landing). Toolchain: leanprover/lean4:v4.33.0 at
`/tmp/shared-lean-copy/toolchain-v4.33.0/bin`; shared package cache.

**Status: historical.** The probes below were recorded against the pre-rename,
pre-split tree; the `#check` list and coordinates are verbatim from that run.
Post-integration (`7e98c58`) name map per `Lib/reports/RENAMES.md`: the `Smale.`,
`NoExotic.` and `Degree.` prefixes are dropped and `MorseCancel.` →
`MorseCancellation.`; the providers moved to the split files listed under
"Post-integration provider locations" below. A re-probe at the new head is
required before certification — stale `.olean`s may still resolve old names.

## What was probed

### Probe 1 — FQN resolution (legacy context)

File `/tmp/E2Probe.lean` (removed after use):

```lean
import Hopf.SingularHomology
open Mathoverflow1973

#check @Smale.RegularValues.exists_null_exceptional_values_manifold
#check @Smale.RegularValues.exists_null_exceptional_values_in_chart
#check @Smale.RegularValues.exists_null_exceptional_values_on
#check @Smale.TransverseCoordinates.dense_native_translations
#check @Smale.TransverseCoordinates.exists_null_exceptional_native_translations
#check @Smale.SupportedDiffeomorph.IsotopicToIdentity
#check @Smale.SupportedDiffeomorph.SupportedRelativeIsotopy
#check @Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.extension
#check @Smale.SupportedDiffeomorph.exists_supported_isotopy_extension
#check @Smale.SupportedDiffeomorph.exists_supported_pointMoving
#check @Smale.SupportedDiffeomorph.exists_open_pointMoving
#check @Smale.SupportedDiffeomorph.exists_pointMoving_of_preconnected
#check @Smale.SupportedDiffeomorph.exists_pointMoving_of_path
#check @Smale.NativeTransversality.exists_ambient_transverse_diffeomorph
#check @Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel
#check @Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range
#check @Degree.DiskShrinking.exists_embedded_disk_isotopy_of_same_center
#check @MorseCancel.exists_isotopic_pointMoving_of_path
#check @MorseCancel.exists_open_isotopic_pointMoving
#check @MorseCancel.exists_isotopic_pointMoving_of_preconnected
#check @Smale.exists_pointMoving_fixing_finite
#check @Smale.ManifoldImmersion.exists_immersion_on_compact_rel
#check @Smale.ManifoldImmersion.exists_compact_embedding_of_immersion
#check @Smale.ManifoldImmersion.exists_compact_embedding_of_immersion_within_target
#check @Smale.ManifoldImmersion.exists_relative_compact_embedding
#check @Smale.ManifoldImmersion.exists_relative_compact_embedding_twoDimensional
#check @NoExotic.sphereMap_nullhomotopic_of_dim_lt
#check @NoExotic.sphere_sphere_nullhomotopic
#check @Smale.isDiscrete_transverse_intersections
#check @Smale.finite_transverse_intersections
#check @Smale.exists_short_embedded_arc
#check @Smale.exists_embedded_connecting_arc_avoiding_finite_dim_two
#check @Smale.exists_smooth_path_avoiding_finite
```

Result: **33/33 resolve, zero errors.** Note: without `open Mathoverflow1973`
every name fails — all declarations live inside that namespace; the ledger
signatures carry the `Smale.`/`NoExotic.`/`Degree.`/`MorseCancel.` infixes which
resolve under `open Mathoverflow1973` or fully qualify as
`Mathoverflow1973.Smale.*` etc. The three names the integration review flagged
(`exists_immersion_on_compact_rel`, `exists_compact_embedding_of_immersion`,
`exists_relative_compact_embedding*`) are `Smale.ManifoldImmersion.*` — now
written with that prefix in the ledger.

### Probe 2 — G-E2 target signature at `2k+1 ≤ n`

File `/tmp/E2GenProbe.lean` (removed after use), same imports plus the standard
`open scoped` set used by the source files (needed for `∞`, `mfderiv`,
`C(X, N)`): the generalized `exists_immersion_on_compact_rel` signature at
`{E G H N}` with `(hdim : 2 * Module.finrank ℝ E + 1 ≤ Module.finrank ℝ G)`
**elaborates** (only the expected `sorry` linter warning on the proof stub —
this is an interface check, not a proof claim).

Specialization check: `Module.finrank ℝ Smale.PlaneImmersion.Plane = 2`
(`Smale.PlaneImmersion.Plane` is `abbrev ... := ℝ × ℝ` (SW 11318 at probe time;
now `PlaneImmersion.Plane` at `Immersion/Relative.lean:980`);
proof `by rw [Smale.PlaneImmersion.Plane]` fails because `abbrev` equation
lemmas don't fire by `rw` — the working proof is
`by show Module.finrank ℝ (ℝ × ℝ) = 2; rw [Module.finrank_prod]; simp`,
probed). So the general bound `2k+1 ≤ n` recovers `5 ≤ n` at `k = 2` and
`3 ≤ n` at `k = 1`, matching the recorded disposition in E2.md open item 2.

## Source-coordinate correction recorded

The ledger's old `DT nnnnn` coordinates referred to the pre-split
`Hopf/DifferentialTopology.lean` (now a 234-line documentation umbrella).
The SW numbers in the recorded probe were verified by direct reads against the
then-monolithic `SurgeryWindows.lean` (~17.5k lines) at `0c48e7b` — they are
historical. Post-integration provider locations (`7e98c58`, all still legacy
non-`module` Lib files):

- `Lib/Geometry/Manifold/Transversality/Basic.lean`: 158/173/227 (RegularValues
  Sard), 304/354 (TransverseCoordinates), 1061 (SupportedRelativeIsotopy.extension),
  2547 (supported isotopy extension), 2593/2672 (chart disk shrinking, disk-chart
  isotopy), 2708 (same-center disc theorem), 2753/2788 (SupportedDiffeomorph
  pointMoving).
- `Lib/Geometry/Manifold/Morse/Cancellation.lean`: 3374 (IsotopicToIdentity),
  3441 (SupportedRelativeIsotopy, fields at 3452/3462/3469).
- `Lib/Geometry/Manifold/Morse/Rearrangement.lean`: 2581 (NativeTransversality
  ambient), 2609 (disjunction corollary).
- `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` (reduced to 1,838 lines):
  378/412 (GeneralPosition), 708+ (ImageComplement).
- `Lib/Geometry/Manifold/Immersion/Relative.lean`: 64/182/205
  (MorseCancellation isotopic pointMoving), 309/329 (SupportedDiffeomorph
  pointMoving), 340/382 (finite-avoiding path, finite-fixing point motion),
  980 (`PlaneImmersion.Plane`), 1192 (plane rank/collision engine),
  1490 (immersion patch step), 1632 (E10 headline), 1970/2014/2032/2095
  (E11 embedding family), 2698 (curve affine helper), 2927/2970 (curve wrappers).
- `Hopf/SingularHomology.lean`: SH 11271/11292 (E13 intersections),
  SH 14199/14214 (E12 sphere maps), SH 18380/18441 (E14 arcs).

## Caveats / not certified

- These are **resolution and elaboration** probes in legacy context — not
  `module`/`public` production probes. Production probing of E2-B* is blocked
  by the provider seam: the destination files import Mathlib + the Lib
  providers, but the SW source file is legacy and the moved decls must keep
  resolving for `Hopf.SingularHomology`/`SphereTopology` consumers during
  transition (LibShims export aliases).
- E13 has no destination file in §14 — provisionally
  `Transversality/Intersections.lean`, flagged for the owner.
- The `MorseCancel.` prefix on the homogeneity family was preserved verbatim at
  probe time; post-integration it is `MorseCancellation.` (the rename already
  landed — consumers' FQNs were updated in-tree).
- D1/D2 seams (`exists_contMDiff_approx` / `exists_tubularNeighborhood_*`)
  remain unlanded-provider dependencies for E8/E12 proofs — the moved files
  will import `Hopf.DifferentialTopology` during transition, as today.
- G-E2 is a signature-elaboration check only; the general-`k` immersion
  creation proof is new mathematics (§10), not a move.
