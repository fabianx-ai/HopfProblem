# G Axis-5 typed-ledger review (fresh-context subagent)

Head: 84d9450 (lib/textbook-extraction-muse-i3)
Scope: all 35 ledger entries in `Lib/docs/G.md` — verbatim signature check,
coordinate check, current-names check.

## Verification table

| # | Decl | Cited coord | Actual coord | Status |
|---|---|---|---|---|
| 1 | `simplyConnectedSpace_of_homotopySixSphere` | MinimalSystem.lean:63 | MinimalSystem.lean:63 | VERBATIM |
| 2 | `pathConnectedSpace_of_homotopySixSphere` | MinimalSystem.lean:68 | :68 | VERBATIM |
| 3 | `homotopySixSphere_homology_subsingleton` | MinimalSystem.lean:73 | :73 | VERBATIM |
| 4 | `MorseCancellation.exists_minimal_excellent_morse_system` | SphereTopology:4802 | :4802 | VERBATIM |
| 5 | `MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points` | SphereTopology:5455 | :5455 | VERBATIM |
| 6 | `MorseCancellation.minimal_excellent_morse_extreme_counts_one` | SphereTopology:5526 | :5526 | VERBATIM |
| 7 | `MorseCancellation.exists_outer_index_minimal_ordered_morse_system` | SphereTopology:7664 | :7664 | VERBATIM |
| 8 | `MorseCancellation.exists_excellent_indexed_morse_birth` | Birth.lean:883 | Birth.lean:883 | VERBATIM |
| 9 | `MorseCancellation.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` | SphereTopology:7260 | :7260 | VERBATIM |
| 10 | `MorseCancellation.exists_one_to_three_handle_trade` | SphereTopology:7455 | :7455 | VERBATIM |
| 11 | `MorseCancellation.exists_one_to_three_handle_trade_at_cut` | SphereTopology:7543 | :7543 | VERBATIM |
| 12 | `MorseCancellation.exists_one_to_three_handle_trade_of_ordered_indices` | SphereTopology:7636 | :7636 | VERBATIM |
| 13 | `MorseCancellation.outer_index_minimal_index_one_count_zero` | SphereTopology:7724 | :7724 | VERBATIM |
| 14 | `MorseCancellation.outer_index_minimality_neg` | SphereTopology:7772 | :7772 | VERBATIM |
| 15 | `MorseCancellation.outer_index_minimal_outer_counts_zero` | SphereTopology:7805 | :7805 | VERBATIM |
| 16 | `MorseCancellation.exists_minimal_ordered_morse_system_without_outer_indices` | SphereTopology:7854 | :7854 | VERBATIM |
| 17 | `ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere` | SphereTopology:11557 | :11557 | VERBATIM |
| 18 | `ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks` | SphereTopology:11579 | :11579 | VERBATIM |
| 19 | `MorseCancellation.exists_middle_index_blocks` | SphereTopology:11605 | :11605 | VERBATIM |
| 20 | `AdaptedWindows.exists_ordered_middle_family` | SphereTopology:11687 | :11687 | VERBATIM |
| 21 | `AdaptedWindows.exists_canonical_middle_family` | Recognition.lean:758 | :758 | VERBATIM |
| 22 | `MorseCancellation.canonical_middle_matrix_surjective` | Proof/Recognition.lean:782 | :782 | VERBATIM (terminator `:=`, correct — term-mode proof at :809–812) |
| 23 | `AdaptedWindows.exists_primitive_functional_unit` | Recognition.lean:5317 | :5317 | VERBATIM (full ~117-line signature incl. `ops`/`Γ`/flow-equivalence tail) |
| 24 | `AdaptedWindows.exists_first_middle_pivot` | Recognition.lean:1799 | :1799 | VERBATIM |
| 25 | `MorseCancellation.exists_native_belt_cut_family` | Recognition.lean:6283 | :6283 | VERBATIM |
| 26 | `MorseCancellation.cancel_from_preserved_unit_belt_cut` | Recognition.lean:6632 | :6632 | VERBATIM (incl. `letI := RegularLevel.chartedSpace hg hga` and `∀ (_ : ContMDiff …)` continuation binders) |
| 27 | `MorseCancellation.cancel_from_complete_middle_family` | Recognition.lean:6786 | :6786 | VERBATIM |
| 28 | `MorseCancellation.minimal_ordered_index_two_count_zero` | Proof/Recognition.lean:815 | :815 | VERBATIM |
| 29 | `MorseCancellation.minimal_ordered_index_four_count_zero` | Proof/Recognition.lean:875 | :875 | VERBATIM |
| 30 | `MorseCancellation.ordered_no_middle_indices_count_two` | Proof/Recognition.lean:960 | :960 | VERBATIM |
| 31 | `MorseCancellation.critical_pair_of_surgery_count_two` | Recognition.lean:7055 | :7055 | VERBATIM |
| 32 | `ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points` | Reeb.lean:694 | Reeb.lean:694 | VERBATIM |
| 33 | `MorseCancellation.exists_two_critical_point_morse_of_homotopySixSphere` | Proof/Recognition.lean:982 | :982 | VERBATIM |
| 34 | `MorseCancellation.nonempty_homeomorph_of_homotopySixSphere` | Proof/Recognition.lean:1000 | :1000 | VERBATIM (correctly lacks `[SecondCountableTopology M]`) |
| 35 | `homeomorphic_sixSphere_of_homotopySixSphere` | Proof/Recognition.lean:1011 | :1011 | VERBATIM (carries `[SecondCountableTopology M]` at :1013; terminator `:=`) |

## Current-names check

- **`SixSphere` vs `MetricSixSphere`: correct everywhere.** `SixSphere` is
  `abbrev` at `Lib/Geometry/Manifold/Morse/MinimalSystem.lean:60`;
  `Hopf/SphereTopology.lean` imports MinimalSystem (import line 105) and all
  its ledger signatures verbatim use `≃ₕ SixSphere`. `MetricSixSphere` is
  `abbrev` at `Hopf/Proof/Recognition.lean:270`, and the ledger uses it only
  in the Proof/Recognition signatures (782, 815, 875, 960, 982, 1000, 1011) —
  matching source exactly.
- **No `Suspension.topSus`, `SecondHurewicz.*`, `HigherHurewicz.*`,
  `PeriodTorusHigherHomology.CircleTopology`, or `MorseCancel.*` in G.md.**
  All cancellation decls carry the current `MorseCancellation.` prefix.
- **`Smale.*`:** the only `Smale.` occurrences in G.md are the target filename
  `PoincareConjecture/Smale.lean` and author-name prose — no stale decl
  prefixes.
- **No stale `/home/`, `/tmp/`, `~/`, `s6-notes`, or `file:///` citations** in
  G.md.

## Minor nits (non-blocking)

1. G.md §7 line 300: `` `MetricSixSphere` (Recognition) `` — the abbrev lives
   in `Hopf/Proof/Recognition.lean:270`, not `Hopf/Recognition.lean`. Prose
   shorthand; ledger entries correct. **Repaired at e03a056.**
2. The ledger preamble's "coordinates re-verified at `27f8e7f`" label was
   historical; coordinates remained accurate at 84d9450. **Re-stamped at
   e03a056.**
3. `Lib/docs/G-map.md` (a different document, not the ledger) contains stale
   pre-split coordinates — already stamped historical in-tree.

## Verdict

```
Verdict: GO
```
