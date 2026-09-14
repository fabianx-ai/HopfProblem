# Integration review 2 — GLM `lib/A-surgerywindows-split`, Kimi/Devin `lib/C-10-boundary`, Devin `lib/textbook-extraction-devin`

Reviewer: Claude Fable 5.1 (goblin seat), 2026-09-13. Base: `lib/textbook-extraction` at f284365b.
Result: branch `lib/integration-2`, fast-forwarded into `lib/textbook-extraction` once the build below was green.
Method: the three branches were merged or replayed onto the base in one worktree, every
conflict was resolved by rule (below), and the result was checked as one tree: build, axiom
probes, statement comparison of `Hopf/`, census ratchet, module registration, placeholder
grep. Scratch scripts and their outputs are in the reviewer's session directory; the rules
and numbers are recorded here so a reader can reproduce them without those scripts.

## 1. What was integrated

| Branch | Author seats | Commits | Taken as |
|---|---|---|---|
| `lib/C-10-boundary` (24 commits on f034c13b) | Kimi seat (Grok, then Astra+SWE2), last 10 commits by Devin | C10 boundary relation, round trips, general `hurewiczLinearEquiv`, adapters replacing the degree-3..6 towers, cross-product rename | merge, clean |
| `lib/textbook-extraction-devin` (12 commits on f034c13b) | Devin (Muse seat) | J ledger passes and landings J-A, J-B1, J-C1; F0a/F0b + HomologyTransport; E2 and G ledgers/reviews | merge, one conflict (census baseline) |
| `lib/A-surgerywindows-split` (46 commits on accd1ed1) | GLM | SurgeryWindows split (item 0), receipts, FREE rule, dupNamespace fix, report split, coherence web (item 6), E1 drafts/scoping, Wang findings, four namespace renames (item 9) | replayed commit by commit; renames re-derived by regex; 7 docstring commits skipped; 11 commits were duplicates of commits already on the base (same patch-id) |

Integration commits and rules:

1. C then Devin merged. Devin's baseline conflict resolved provisionally, then recomputed (§4).
2. GLM's non-rename commits cherry-picked in GLM's order. Markdown conflicts in
   `Lib/reports/*` resolved toward GLM (the reports are GLM's). Lean conflicts:
   - `6c14fbd4` (dupNamespace): for files whose text equalled GLM's parent modulo the
     `_mo1973_NNNN` suffixes, GLM's result taken verbatim (suffix-stripped); `Hopf/LibShims.lean`
     resolved by hand (`topSus` export lists, `LocalCollapse` abbrev + `Collapse` export).
   - `276c58be` (coherence web, 112 declarations): the 8 conflict regions in
     `CrossProduct.lean` were lane C's cross-product rename (`PeriodTorusHigherHomology.* ->
     SingularHomology.*`, 105 names) against GLM's older text; C's names kept and the map
     applied to GLM's block and to Devin's `Pontryagin.lean` (21 references). GLM's block also
     carried `PeriodTorusHigherHomologyPontryagin.additionMap` and `.product`, which Devin had
     already landed in `Pontryagin.lean` (lane J's file); those two were dropped from GLM's
     block. `Specialization.lean` resolved to contain neither GLM's 112 nor Devin's 18 moved
     declarations. One reference (`crossProductTriangle`) was missed by the map and found by the
     first build; fixed in bdb26973.
3. GLM's four renames were not cherry-picked (they were made on a tree without the lint of
   6e5c4c30 and would have conflicted in every renamed file) but re-derived: identifier-boundary
   regex over `*.lean` and the E1 drafts, in GLM's order, plus GLM's two Hopf disambiguations
   applied line-for-line from ff893762 (`DiskCone -> SphereCone` in SingularHomology.lean and
   SphereTopology.lean; `SixSphere -> MetricSixSphere` in Recognition.lean). Verification: every
   Lean file whose pre-rename text matched GLM's parent is byte-identical to GLM's result
   (steps 1–4: 1, 6, 22, 22 files). The only textual difference found was one module-docstring
   line in `Cancellation.lean` where GLM left the old name. A boundary bug in the first pass
   (`⟨` treated as an identifier character) was caught by the build and fixed in d9f3c5cf.
   Prose, ledgers, reviews and `RECEIPTS_DATA.json` were **not** rewritten: GLM's own rename
   commits had rewritten `Lib/reviews/A.md`, `Lib/reports/D1.md`, `D2.md` and other seats'
   ledgers with a pattern that turned `Smale.*` into `*` (four places in the review); that
   damage is not taken. The historical names stay in the record; the map is
   `Lib/reports/RENAMES.md`.
4. Skipped from GLM's branch: the seven "reapplied from the unmerged docstring wave" commits.
   GLM's branch was started from a fork state that lacked bba4df2, so it re-derived the headline
   docstrings; the re-derived texts are shorter than the merged ones and in `Chains.lean` drop
   two docstrings the merged wave has. The merged wave stands.

## 2. Checks on the integrated tree

| # | Check | Result |
|---|---|---|
| 1 | Placeholders (`sorry`, `admit`, `axiom`) in `Hopf/`, `Lib/`, `Solution.lean` | 0 (the `sorry` in `Challenge.lean` is the challenge statement, unchanged) |
| 2 | `Lib.lean` registration | 98 modules, each `Lib/**/*.lean` registered exactly once, no stale entries |
| 3 | Statement-change rule, `Hopf/` (13,860 declarations) against the base with the rename map applied to the base | 0 new declarations; 1 "changed statement" that is only the dropped `attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in` prefix of `AdaptedWindows.exists_primitive_functional_unit` (Recognition.lean), statement text identical; 37 changed proofs with identical statements (Recognition 21, Hurewicz 10 — lane C's adapters; Specialization 4, PeriodConstruction 2). Before the rename step the same scan gave 0 new / 1 (the same) / 32. |
| 4 | Declarations deleted from `Hopf/` vs base | 1,229: Hurewicz.lean 911 (Third/Fourth/Fifth towers, now 2 adapter declarations each), Recognition.lean 135 (SixthHurewicz, 21 naturality proofs kept), Specialization.lean 143 (coherence web + Pontryagin core, moved), CuspFilling.lean 23 (torus core, moved), SphereTopology.lean 17 (HomologyTransport, moved). 425 of the 1,229 exist in `Lib/` by name; the rest are the per-degree proofs replaced by instantiation of the general theorem. |
| 5 | Census ratchet | Prefix list carried through the rename map (§4); count 2,663 on both the pre-rename and post-rename trees, so the renames move nothing; baseline 2,862 -> 2,663 lowered by `--update`. |
| 6 | Build (`/home/goblin/hopf-lib-integration`, seeded `.lake`, Lean 4.33.0, pinned Mathlib) | `lake build Lib` exit 0, then `lake build Solution S6Shortcuts S6 Challenge` exit 0, 8,834 jobs, 03:06–03:19 on 2026-09-13; the endpoint `mathoverflow_1973` printed with `[propext, Classical.choice, Quot.sound]`. Two earlier attempts failed on the two integration defects named above (VanKampen boundary, `crossProductTriangle`), both fixed in their own commits. |
| 7 | Axiom probes (`#print axioms`, 21 names: general `hurewiczLinearEquiv` and `…OfTwoLE`, `threefoldHomotopyEquiv`, `homeomorphic_sixSphere_of_homotopySixSphere`, `sphere_homotopicRel_of_topClass_eq`, F0a/F0b heads, J heads in Torus/Pontryagin/MinorCoordinates, the five split-file heads, the coherence web, `mathoverflow_1973`) | 21/21 exactly `[propext, Classical.choice, Quot.sound]` |
| 8 | Cross-product compatibility | every old `PeriodTorusHigherHomology.*` name still referenced from `Hopf/` (9) has a `LibShims` export; no qualified cross-product reference inside `Lib/` is unresolved (static scan) |

## 3. Findings per branch

### GLM (`lib/A-surgerywindows-split`)

Landed and confirmed: SurgeryWindows split into five files with 882 declarations preserved
(119+301+133+213+116), pure moves in source order; item 0 receipts; provenance receipts for
every A/D1/D2/H/I/B baseline (`RECEIPTS.md`, 171 rows, 8/8 sample reproduced by GLM);
FREE-rule fix; the 78 dupNamespace fixes; per-lane reports; the coherence web (110
declarations after the Pontryagin pair) in `CrossProduct.lean`; four renames with their
Mathlib twins named in `RENAMES.md`; E1 scoped by measurement with drafts committed.

Record defects (fix in the next commits, not blockers):

1. The branch was based on a stale fork state (accd1ed1 plus rebased copies of eleven base
   commits). The next branch starts from the head named in `NEXT-STEPS-GLM.md`.
2. The rename regex was applied to Markdown: `Smale.*` became `*` in `Lib/reviews/A.md` (4),
   `Lib/reports/D1.md` (1), `D2.md` (1). Not taken here; do not rewrite other seats' files.
3. `RENAMES.md`, `I.md`, `E1.md`, `B.md` cite `~/s6-notes/hopf-lib-a/` (7 lines: WIP diff,
   resume configs, drafts). A report may only cite what is in the tree; commit those files
   under `Lib/reports/drafts/` or delete the citations.
4. `Suspension.topSus` is not a Mathlib-shaped name. The dupNamespace fix needed a rename;
   the name should be chosen against the twin (`Mathlib/Topology/Homotopy/…`), e.g. keep the
   type as `Suspension` in the parent namespace. Item for the rename ledger.
5. The coherence-web commit moved two lane-J declarations (`additionMap`, `product`); J's
   file already had them. Lane boundaries hold even when a cluster is contiguous.
6. The seven re-derived docstring commits duplicated merged work with lower quality. Check
   `git log` of the fork before re-doing a wave.

### Kimi seat + Devin (`lib/C-10-boundary`)

Landed and confirmed in code: `hurewiczLinearEquiv` at general `n ≥ 2`
(`CubeSphere.lean:792`, plus `hurewiczLinearEquivOfTwoLE`); `Hopf/Hurewicz.lean` 9,631 -> 423
lines; `HopfDegree.lean` present in `Lib/` (C13 classification seam); cross-product rename
with shims. Statement scan: no `Hopf/` statement changed (§2.3).

Record defects:

1. `Lib/reports/C.md` §"Open items" and `Lib/reports/C-handoff.md` (head `63ef708`) still say
   the round trips and the equivalence are not landed; ten later commits landed them. The
   report must be brought to the branch head before the lane is called done.
2. The gate used for the tower replacement was `lake build Hopf.Recognition` only; the full
   chain was not claimed. It is built here (§2.6).
3. The last ten commits carry Devin's trailer but the seat file is Kimi's; say in the report
   which seat did what.

### Devin / Muse (`lib/textbook-extraction-devin`)

Landed and confirmed: J-A (`MinorCoordinates.lean`, 15 nodes), J-B1 (`Torus.lean`), J-C1
(`Pontryagin.lean`, mapped to lane C's names here); F0a (`TransvectionReduction.lean`, 10
declarations) and F0b (`IntegerPresentation.lean`, plus five HomologyTransport declarations);
E2 typed ledger at `2k+1 ≤ n` with the TDV §2 pointer dropped; G ledger with exact
signatures; Milnor numbers corrected to 6.6/7.6 in F.

Record defects:

1. Stage-2 and Axis-5 reviews are self-reviews: `G-stage2-review.md` says "Muse (self-review
   pass)", the three J Axis-5 reviews are by "Devin, seat devin-axis5-j" on Devin's own packet.
   The protocol needs a different seat for the review; the owner assigns one (this integration
   review does not replace it for the mathematics).
2. Probes were compiled from `/tmp/G_Probe.lean`, `/tmp/E2Probe.lean`; the protocol wants them
   in the tree, deleted before the commit, so the receipt names a path a reader can recreate.
3. Every ledger and receipt now cites pre-rename names (`Smale.*`, `MorseCancel.*`,
   `Degree.*`): G.md 101, F.md 61, E2.md 53, E2 receipt 41, F receipt 14, G receipt 11,
   G stage-2 review 9. They were correct at f034c13; the next receipt must be taken at the new
   head with the new names. `Lib/reports/RENAMES.md` has the map.
4. `G-stage2-review.md` cites `~/s6-notes/kimi-notes/G-map.md` (off-tree).

## 4. Census prefix list

The renames leave every stock declaration in `Hopf/` in place under a new name, so
`scripts/lib_stock_prefixes.txt` follows the map: `Smale`, `NoExotic`, `Degree` are replaced by
their former sub-families (108, 17, 37 entries, taken from the base tree), `MorseCancel` by
`MorseCancellation`, `FundamentalGroupVanKampen` by `FundamentalGroup.VanKampen`, `SphereCone`
added for the Hopf disambiguation, and 91 former leaf declarations (`Prefix.name` with no further
component) are listed with the new exact-name form `=name`, added to
`scripts/lib_stock_census.py` for this purpose. Count on the pre-rename tree with the old list
and on the post-rename tree with the new list: both 2,663.

## 5. Verdict

GO for the integrated head: full chain green, 21/21 axiom probes exact, no `Hopf/` statement
changed under the rename map, census 2,663 with a map-preserving prefix list, no placeholder,
every module registered. The record defects in §3 are the seats' next items
(`NEXT-STEPS-GLM.md`, `NEXT-STEPS-KIMI.md`, `NEXT-STEPS-MUSE.md`); none of them changes what
is proved. Two matters are the owner's: who reviews Devin's E2/G/J packets (a seat other than
Devin's), and whether `Suspension.topSus` is renamed now or with the wrapper removal.

Numbers the seats' reports must carry forward: `Hopf/Hurewicz.lean` 423 lines; `Hopf/`
13,860 declarations (1,229 fewer than the base); `Lib/` 98 modules; census 2,663.

## 6. Addendum, same day: second pass (Kimi docstrings and C record, Devin's Astra reviews)

Integrated on top of bd21441d:

- `lib/C-10-boundary` 2bde1149..88bdcc73 (13 commits, Kimi seat, based on the pre-rename
  head): docstrings, section headers and module overviews in twelve `Lib` files, plus
  `Lib/docs/C.md`, `C-INTERFACE_RECEIPT.md`, `C-STAGE2-REVIEW.md`, `Lib/reports/C.md`,
  `C-handoff.md`. The twelve Lean files were taken from the branch and the rename map
  replayed on them (99 references); comment-stripped text is identical to bd21441d in every
  file, so no proof term or statement changed. The C record now says C10 and C13 are landed
  and marks the hand-off historical (§3 Kimi 1 closed). Open: the receipt was taken at the
  branch head `1a313843` with pre-rename names (4 citations; `C.md` 28, `reports/C.md` 7);
  the Stage-2 review is a recovered artifact whose reviewer is not recorded; the receipt's
  "coordinating reviewer" is Devin, the same seat as the last ten C commits.
- `lib/textbook-extraction-devin` 699d1a4a..8e4a8510 (5 commits, documentation only):
  Astra's Stage-2 reviews of G (two passes, at 699d1a4a and bd9c3936) and E2 (at 6bcd99d1),
  each "NO-GO as written" with repairs applied by Muse between passes and findings still open;
  `G.md` expanded by about 1,100 lines. Reviewer named as "astra (Devin)", stated independent
  of Muse. E2 and G stay DRAFT. `G.md` now cites 308 pre-rename names.
- Build of the result (10dfe126): `lake build Lib` exit 0, consumers exit 0, 8,834 jobs, 03:35–03:48 on 2026-09-13; census 2,663 unchanged; no placeholder. Verdict unchanged: GO for the head; E2 and G remain DRAFT until Astra's closing pass.
