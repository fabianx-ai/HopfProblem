# G closing review (fresh-context subagent)

Head: 840aef4 (lib/textbook-extraction-muse-i3)
Checks: 34/35 signatures verified verbatim; coordinates: 32 exact / 3 corrected
(stale, banner-disclaimed)

## Signature-by-signature result

| Row | Decl | Cited | Actual | Verdict |
|---|---|---|---|---|
| G1 | `simplyConnectedSpace_of_homotopySixSphere` | MinimalSystem:24 | **63** | verbatim; coordinate stale (module-conversion header added ~39 lines) |
| G1 | `pathConnectedSpace_of_homotopySixSphere` | MinimalSystem:29 | **68** | verbatim; coordinate stale |
| G1 | `homotopySixSphere_homology_subsingleton` | MinimalSystem:34 | **73** | verbatim; coordinate stale |
| G2a | `exists_minimal_excellent_morse_system` | ST:4802 | 4802 | verbatim ✓ |
| G2a | `exists_index_ordered_morse_system_preserving_critical_points` | ST:5455 | 5455 | verbatim ✓ |
| G2a | `minimal_excellent_morse_extreme_counts_one` | ST:5526 | 5526 | verbatim ✓ |
| G2a | `exists_outer_index_minimal_ordered_morse_system` | ST:7664 | 7664 | verbatim ✓ |
| G3 | `exists_excellent_indexed_morse_birth` | Birth:883 | 883 | verbatim ✓ |
| G3 | `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` | ST:7260 | 7260 | verbatim ✓ |
| G3 | `exists_one_to_three_handle_trade` | ST:7455 | 7455 | verbatim ✓ |
| G3 | `exists_one_to_three_handle_trade_at_cut` | ST:7543 | 7543 | verbatim ✓ |
| G3 | `exists_one_to_three_handle_trade_of_ordered_indices` | ST:7636 | 7636 | verbatim ✓ |
| G3 | `outer_index_minimal_index_one_count_zero` | ST:7724 | 7724 | verbatim ✓ |
| G3 | `outer_index_minimality_neg` | ST:7772 | 7772 | verbatim ✓ |
| G3 | `outer_index_minimal_outer_counts_zero` | ST:7805 | 7805 | verbatim ✓ |
| G2b | `exists_minimal_ordered_morse_system_without_outer_indices` | ST:7854 | 7854 | verbatim ✓ |
| G4 | `middleMatrix_surjective_of_homotopySphere` | ST:11557 | 11557 | verbatim ✓ |
| G4 | `middleMatrix_surjective_of_complete_blocks` | ST:11579 | 11579 | verbatim ✓ |
| G4 | `exists_middle_index_blocks` | ST:11605 | 11605 | verbatim ✓ |
| G4 | `exists_ordered_middle_family` | ST:11687 | 11687 | verbatim ✓ |
| G4 | `exists_canonical_middle_family` | Recognition:758 | 758 | verbatim ✓ |
| G4 | `canonical_middle_matrix_surjective` | Proof/Recognition:782 | 782 | verbatim ✓ (correctly ends `:=`, term-mode) |
| G5 | `exists_primitive_functional_unit` | Recognition:5317 | 5317 | **TRUNCATED mid-expression** (see finding 1) |
| G5 | `exists_first_middle_pivot` | Recognition:1799 | 1799 | verbatim ✓ (restored through `:= by` at source:1852) |
| G5 | `exists_native_belt_cut_family` | Recognition:6283 | 6283 | verbatim ✓ (includes initial `let`s) |
| G5 | `cancel_from_preserved_unit_belt_cut` | Recognition:6632 | 6632 | verbatim ✓ (includes internal `letI`) |
| G5 | `cancel_from_complete_middle_family` | Recognition:6786 | 6786 | verbatim ✓ |
| G5 | `minimal_ordered_index_two_count_zero` | Proof/Recognition:815 | 815 | verbatim ✓ |
| G5 | `minimal_ordered_index_four_count_zero` | Proof/Recognition:875 | 875 | verbatim ✓ |
| G5 | `ordered_no_middle_indices_count_two` | Proof/Recognition:960 | 960 | verbatim ✓ |
| G6 | `critical_pair_of_surgery_count_two` | Recognition:7055 | 7055 | verbatim ✓ |
| G6 | `nonempty_homeomorphSphere_of_two_critical_points` | Reeb:694 | 694 | verbatim ✓ |
| G6 | `exists_two_critical_point_morse_of_homotopySixSphere` | Proof/Recognition:982 | 982 | verbatim ✓ |
| G6 | `nonempty_homeomorph_of_homotopySixSphere` | Proof/Recognition:1000 | 1000 | verbatim ✓ (no `SecondCountableTopology` — doc note correct) |
| G6 | `homeomorphic_sixSphere_of_homotopySixSphere` | Proof/Recognition:1011 | 1011 | verbatim ✓ (carries `[SecondCountableTopology M]` at source:1013; body delegates to inner chain — doc claims both correct) |

No invented binders or fabricated instances found in any complete signature.
Namespace usage (`MorseCancellation.`, `AdaptedWindows.`,
`ManifoldMorse.SurgeryWindows.`) matches source exactly; no
`MorseCancel.`/`Smale.`/`topSus` remnants in G.md.

## Findings

1. **blocker** — `AdaptedWindows.exists_primitive_functional_unit` signature is
   truncated mid-expression at **G.md:889**: the ledger text ends
   `MorseCancellation.canonicalMiddleMatrix (M := M) (f :=` — cut inside
   **Hopf/Recognition.lean:5385**. The source signature continues through
   **:5433** (`:= by`). Missing verbatim text:
   `(f := g) (a := a) (r := r) (n := n) B' Γ = canonicalMiddleMatrix … B γ *
   (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod`, the
   surjectivity conjunct, the `∃ i : Fin n, L ((equalCutHomologyEquiv
   hsub).symm (middleSectionClass (Γ i))) = 1 ∨ … = -1` unit disjunction, and
   the three flow-limit/orbit-preservation conjuncts (`∀ z : M, f z ≤ a → …`).
   This is precisely the defect the fresh2 NO-GO flagged ("the ledger drops the
   very unit its prose promises"): the repair extended the signature past the
   internal `let`s but still stops before the outer `:= by`. The banner claim
   at G.md:10–11 that "the two truncated G5 result types it flagged are
   restored verbatim below" is only half true —
   `exists_first_middle_pivot` was restored; this one was not.

2. **minor** — §5 mechanism misattribution, **G.md:200–201**:
   "`consecutive_last_two_first_three` (Recognition:6743, applied inside
   `cancel_from_preserved_unit_belt_cut`)". It is actually applied at
   **Recognition.lean:6874 inside `cancel_from_complete_middle_family`**
   (6786–6907); its output `hconsecutive` is then passed as a hypothesis to
   `cancel_from_preserved_unit_belt_cut` at :6900. The decl coordinate (6743)
   is correct; the enclosing-theorem attribution is wrong. (G.md:258–261
   describes the correct arrangement, so this is internally inconsistent too.)

3. **minor** — §4 parenthetical, **G.md:147**: "the level f = a is preserved
   verbatim (`heq`, `hsub`, `hlevel` in the code)". In the (1,2)-trade chain
   the preserved-cut datum is `heq : ∀ y, g y = a ↔ f y = a` (plus
   `∀ y, f y ≤ a → g =ᶠ[𝓝 y] f`, discarded as `-` in
   `exists_one_to_three_handle_trade`:7490, from
   `birth_preserves_lower_levels`:6401). `hsub`/`hlevel` are hypothesis names
   of the §5 middle-cut theorem `cancel_from_preserved_unit_belt_cut`
   (Recognition:6646–6647), not of the trade. `hgr`,
   `birth_preserves_unique_index_zero` (:7341), `hgap`
   (`birth_first_new_value_gap`:7321) all check out as described.

4. **minor (banner-disclaimed)** — G1 coordinates stale after public-module
   conversion: cited 24/29/34, actual **MinimalSystem.lean:63/68/73** (both
   the Axis-2 table at G.md:311 and the signature comments). The RECEIPTS.md
   addendum (line 181) confirms the move but gives no new lines; the banner
   says stale landed-provider coordinates "are not current blockers". Same
   provenance staleness at G.md:292 — "`SixSphere` (SingularHomology)" is now
   `MinimalSystem.lean:60`.

5. **minor (stale open item)** — Open item 6 (G.md:1222–1227) describes
   `SurgeryWindows.lean` as a 17,556-line GLM blob with
   `exists_compact_embedding_of_immersion` at :12352 and
   `exists_ambient_transverse_diffeomorph` at :17495. Current file is 1,983
   lines; those decls are now at
   `Lib/Geometry/Manifold/Immersion/Relative.lean:2017` and
   `Lib/Geometry/Manifold/Morse/Rearrangement.lean:2723`. Side-note only, not
   ledger content.

## Verification of non-ledger claims (checks 2–5) — all pass

- **Dependency order G2a → G3 → G2b → G4 → G5 → G6**: verified by call graph.
  `exists_minimal_ordered_morse_system_without_outer_indices` (ST:7854) calls
  `exists_outer_index_minimal_ordered_morse_system` (G2a) then
  `outer_index_minimal_outer_counts_zero` (G3) — the G2b split is real. G2a
  decls use only existence/`Nat.find`, rearrangement, and (0,1)-cancellation —
  no trade dependency (despite
  `exists_outer_index_minimal_ordered_morse_system` sitting textually after
  the G3 block at :7664, its proof at 7690–7722 uses none of it).
- **§3 mechanism**: `exists_excellent_morse_reduction_of_multiple_minima`
  (ST:4704) = `exists_native_one_handle_joining_components` (:4615) →
  `realize_one_handle_minimum_branches` (:1643) → higher-minimum case split
  (:4729–4735) → `cancel_realized_higher_minimum` (:4636, via
  `unique_connection_of_distinct_minimum_branches` +
  `exists_flow_preserving_consecutive_pair` + `cancel_unique_zero_one_connection`);
  `minimal_excellent_morse_minimum_count_one` (:5508) applies it +
  `minimal_excellent_morse_forbids_pair_removal` (:4833);
  `extreme_counts_one` (:5526) adds the −f application via
  `nativeMorseCount_neg`. Matches §3 verbatim.
- **§4 trade**: `exists_one_to_three_handle_trade` (:7455) births a
  (2,3)-pair at k=2 inside the `Ioo` band (`exists_excellent_indexed_morse_birth`,
  :7485), preserves the cut via `birth_preserves_lower_levels`, regularity via
  `regular_level_of_retained_critical_germs` (:7494), `hgap`/`hnewlow`/
  unique-minimum via the birth lemmas, then
  `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (:7518). The latter
  calls `cancel_one_two_pair_at_preserved_middle_cut` (:7024), which uses
  `exists_handle_trade_transverse_level_data` (:6645; internally
  `exists_transverse_middle_belt_loop` @6700,
  `exists_new_attaching_circle_placement` @6702,
  `exists_transverse_sheet_of_circle_placement` @6705 — all cited coordinates
  5551/6553/5699/7100 exact) and
  `cancel_transverse_pair_after_flow_preserving_descent` (@7096).
  `hlow`/`hhigh`/`hqa`/`hband`/`hx` as described. ✓
- **§5 Whitney-complement**: `lower_circle_nullhomotopies_of_middle_indices`
  (ST:4228 — first-sublevel-disk base `nonempty_firstSublevelDisk`@4251,
  induction through indices 2/3) → specialization
  `lower_circle_nullhomotopies_of_ordered_native_indices` (:4333, applies it
  @4373) → `last_index_two_collapse_is_primitive` (Rec:6247, output includes
  primitive collapse coordinate + lower-level contractions @6277–6280) →
  `exists_native_belt_cut_family` (:6283, applies it @6328, produces `hnull`
  @6305) → `cancel_from_preserved_unit_belt_cut` (:6632, `hnull` hypothesis
  @6639; body: `exists_single_intersection_of_unit_coordinate` @6701 →
  `cancel_single_basin_section_isotopy` @6740).
  `ImageComplement.circle_nullhomotopies` (SurgeryWindows:767),
  `beltComplement_circle_nullhomotopies_of_sphere_dimension` (:782),
  `surgery_beltComplement_circle_nullhomotopies` (:879),
  `newBoundary_circle_nullhomotopies` (:1486), `nonempty_belt_tubularBigon`
  (SH:10206, called :10342) — all coordinates exact.
- **Elimination order**: Proof/Recognition:991–997 confirms index-2 first
  (`minimal_ordered_index_two_count_zero` @993), index-4 by duality
  (`minimal_ordered_index_four_count_zero` @994, which applies the index-2
  theorem to −f via `nativeMorseCount_neg`, :915–918), index-3 last via
  `ordered_no_middle_indices_count_two` (@996), whose body uses
  `middle_blocks_complete_of_no_four_five` + `middle_counts_equal` (bijective
  middle matrix — injectivity from the degree-3 subsingleton, i.e., the
  H₃(M)=0 input with zero 2/4 groups; surjectivity from H₂ vanishing). Doc's
  "complete-block matrix/count argument" gloss is accurate.
- **SixSphere vs MetricSixSphere**: correctly distinguished. `SixSphere` =
  `Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1` at MinimalSystem.lean:60
  (used by ST decls via import); `MetricSixSphere` = same spelling, separate
  abbrev at Proof/Recognition.lean:270 (used by Proof/Recognition decls). The
  ledger keeps each where the source has it; the five-spelling consolidation
  claim (UnitSphere/Sphere.lean:64, Hemisphere.Sphere/SurgeryWindows:619,
  SixSphereCube.StandardSphere/Hurewicz:255) is defeq-true. The `proof_wanted`
  reference at G.md:58 is real
  (`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere`).

## Verdict

```
Verdict: NO-GO — one blocking ledger defect: AdaptedWindows.exists_primitive_functional_unit
(G5, Hopf/Recognition.lean:5317–5433) remains truncated mid-expression at G.md:889; the banner's
restoration claim is false for this decl. Everything else — the other 34 signatures, all
dependency-order and mechanism claims, the elimination order, and the SixSphere/MetricSixSphere
distinction — verifies clean. Findings 2–5 are minor repairs to fold into the same fix pass.
```
