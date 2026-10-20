# Review of Lib/reports/round-8/dfiles-a/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — every declaration of the five files is accounted for (split
receipts cover the base files exactly, all moves are verbatim, the six renames change only the
name, the "must stay" closure claim reproduces exactly from the base dump), but the receipt
carries three small counting errors and the merge receipt omits one merge-time edit.

## Findings

1. `[wrong receipt]` BeltCancellation: "8 filed, 10 returned, 40 blocked" and "The remaining 40
   are blocked by `SurgeryCollapse`" (RECEIPT.md item 4, and commit `1a7358c0`'s body) — the file
   had 60 declarations, 8 were filed elsewhere in `Lib`, 10 moved to `Hopf/Proof`, so **42** remain
   in `Lib/Geometry/Manifold/Morse/BeltCancellation.lean` (head has 42 declaration heads;
   `split-BeltCancellation.json` says `units_kept: 50` = 42 + 8). Recomputing the closure from
   `dump_base.jsonl` gives 50/60 source declarations in the must-stay set, i.e. all 42 remaining
   ones are really blocked (consumer: only `SurgeryCollapse`), so the substance is right and only
   the number is off. Fix the two "40"s to "42".

2. `[incomplete]` / `[nit]` CutTransport: the receipt says "17 kept, 42 returned" but the envdiff
   block it quotes says `52 Lib.…CutTransport -> Hopf.Proof.…CutTransport`, and the receipt does
   not reconcile the two. The 10 extra names are the auto-generated projections of the structure
   `MorseCancellation.CenteredSheetPassage` (`.mk`, `.family`, `.support`, `.compact_support`,
   `.avoids`, `.smooth`, `.zero`, `.slices`, `.fixedOutside`, `.crossing`), which the dump counts
   as source declarations (they carry a range) and which `split-CutTransport.json` lists inside the
   `CenteredSheetPassage` unit (69 names in 59 units). Same for SurgeryHomology's `BandData` (5
   projections; 85 names in 80 units) — harmless there because the receipt's per-file numbers are
   consistent with envdiff. One sentence in the envdiff section would have closed this.

3. `[wrong receipt]` `[nit]` MinimalSystem: "the seven `Lib` files that imported the module … drop
   the import" — `git grep -l "import Lib.Geometry.Manifold.Morse.MinimalSystem" 4e15a034 -- Lib/`
   lists **eight** `.lean` files (the seven in the commit stat plus
   `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean`). The eighth is dropped in the same commit
   `5d75d095` and the receipt's closing note even mentions that this file "had lost one import
   line in commit 5d75d095", so the work is correct; only the count is wrong.

4. `[incomplete]` (MERGE.md, not this receipt) `Lib/reports/round-8/MERGE.md` §7 says the only
   cross-branch fix inside the merge was the four `classCoordinateMatrix` /
   `eq_mul_transvection_of_columns` retargets in `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean`.
   `git diff fc6b6ffe^2 fc6b6ffe -- Hopf/Proof/Geometry/Manifold/Morse/` shows a second one:
   `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean` (`exists_relative_surgery_cut_transport`)
   had `FlowSuspension.exists_relative_regular_level_isotopy_realization` retargeted to
   `RegularLevel.exists_flow_realization_of_relative_isotopy` (a `r8/moved` rename). Correct
   edit, not recorded.

5. `[docstring]` `[nit]` `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` module docstring
   inventories 41 of its 42 declarations; `MorseCancellation.passageNormalProduct_det` (l.824) is
   missing. `Lib/Geometry/Manifold/Morse/RadialFilling.lean` has a module docstring but none of
   its 12 declarations has a docstring (the receipt only claims "documented modules", so this is
   not a false claim, but the packet's complaint was zero declaration docstrings).

6. `[nit]` Naming: `SingularHomology.homologyMap_unit_smul_of_range_eq` names the map
   `homologyMap` while the function is `SingularMayerVietoris.singularHomologyMap` and the
   neighbouring lemmas are `SingularHomology.singularHomologyMap_comp/_id`. The other five new
   names are fine (`Set.ncard_…_of_injective`, `Submodule.span_range_fin_succ`,
   `…IsotopicToIdentity.conj`, `ContinuousLinearMap.surjective_coprod_comp_left`,
   `MorseCancellation.middleSectionClass_unit_smul_of_range_eq`) and each sits in the namespace
   of its head symbol. `Submodule.span_range_fin_succ` stays pinned to `Module ℤ A`, `A : Type`
   — the receipt says explicitly no generalisation was made, so not a finding.

7. `[citation]` `[nit]` `Lib/Geometry/Manifold/Morse/CutTransport.lean` cites Milnor,
   h-cobordism, "§3 (sublevel sets across a regular interval)". §3 is "Elementary cobordisms";
   the product-cobordism statement for an interval without critical points is Thm 3.4 there, so
   the section is right but the parenthesis is loose. The other citations check out: Thm 5.4 /
   Thm 6.4 (first / second cancellation), §4 (rearrangement, self-indexing), Milnor *Morse
   theory* Thm 3.2 (attaching a λ-cell), Hatcher §2.2 (degree / local degree). Hatcher "§0" for
   "null-homotopic iff extends over the ball" is Chapter 0 material — acceptable.

No `[unsound]` finding. Receipt's packet path says `d-files.md`; the assignment says
`d-files-a.md` — both files exist and the five Morse entries are identical in both.

## Claims checked

| claim | status | how |
|---|---|---|
| 6 commits, one per file + receipt commit; messages describe the commits | verified | `git log 4e15a034..fc6b6ffe^2`; per-commit `--stat`; bodies read |
| Both trailers on every commit | verified | `git log -1 --format=%B` × 6 (co-author line reads "Claude Opus 5") |
| Split receipts account for every declaration of the base files | verified | python: base decl heads (59/31/60/80) ⊆ unit names; every unit's line-range sha256 matches `git show 4e15a034:…`; `source_sha256` matches for all four (SurgeryHomology's `SH_base.lean` = base blob) |
| Every "move" unit is in the Hopf/Proof file, every "keep" unit in Lib (file, island or filing target) | verified | python cross-check at head 39f1d12b; the only kept-but-elsewhere names are the 6 renamed + 8 filed + 17 split-off |
| Moved/kept text verbatim | verified | normalised-whitespace containment; the 10 non-verbatim units diffed: 6 are the rename lines only, 2 are the MERGE.md §7 retargets, 1 is finding 4, 1 (`place_one_handle_in_distinct_minimum_basins`) is an `r8/moved` rename auto-merged in the `Lib` file |
| Declaration bookkeeping: 234 base = 85 Hopf/Proof + 149 Lib | verified | head counts 4+27+42+10+2 and 17+42+61+4+12+5+2+5+1 |
| Must-stay closure 96/115, 0/115, 0/80, 0/4, 120/143 | verified exactly | recomputed from `…/r8-dfiles-a/dump_base.jsonl` (seeds = constants used by a `Lib.*` constant outside the five, closed under `uses` within the module); consumers: Belt ← `SurgeryCollapse` only; SurgeryHomology ← `SurgeryCollapse`, `OrderedCancellation` |
| Nothing in the must-stay set moved under Hopf | verified | same script against `dump_after.jsonl` |
| Spot-check by grep of the monoliths | verified | `exists_signed_belt_cancellation_step`, `IsTransverseBeltSphere`, `HandleDomain`, `coreCellPresentation`, `handleMap` in SurgeryCollapse; `HasIndexTwoPrefix`, `HasIndexThreeBlock`, `SurgeryWindows.point` in SurgeryCollapse + OrderedCancellation; `indexThreeBoundaryEquiv`, `indexTwoNormalModel`, `beltCollapseCoordinate`, `BandData` in SurgeryCollapse |
| Moved names no longer referenced in Lib | verified | grep for 10 moved names (`upperLevelInclusion`, `lastUpperHomeomorph`, `canonicalMiddleMatrix`, `nativeMiddleCutSequence`, `exists_sheet_arc_tube_with_normal_change`, `ManifoldMorse.MorseSurgeryData.instLocal1`, …): none in `Lib/` (other `instLocal1`s in Lib are unrelated namespaces) |
| `Lib` never imports `Hopf` | verified | `grep -rn "import Hopf" Lib/` — only prose in `Lib/docs/*.md` |
| MinimalSystem: 4 decls moved verbatim, twins = themselves | verified | `diff` base Lib file vs head Hopf/Proof file: only the module docstring differs |
| MinimalSystem: no Lib use of its declarations; 24 Hopf files retarget | verified | grep `SixSphere\|homotopySixSphere` in Lib at base/head: one prose mention; 24 head Hopf files import `Hopf.Proof.…MinimalSystem`; Lib.lean entry gone; no `MinimalSystem` string left in Lib |
| Rename map: 6 entries, old names absent, new names present | verified | grep at head; scratch elaboration on the built head: 6 new names `#check` OK, `MorseCancellation.span_prefix_succ`, `same_image_sphere_maps_unit`, `canonicalMiddleMatrix`, `SixSphere` unknown |
| Renamed statements unchanged (incl. `span_prefix_succ` PROOF-NAMING) | verified | unified diff of each unit: only the declaration-name line differs; universe binders unchanged (`Type` stays `Type`, `Type*` stays `Type*`) |
| Envdiff: 0 lost / 0 added source, 1 changed type explained | verified | `envdiff.json` read; the lost/added pair is `span_prefix_succ._proof_1` ↔ `Submodule.span_range_fin_succ._proof_1` with identical hash 2277154165 |
| Islands are general (no Hopf hypotheses as `variable`s) | verified | read `EqualRangeHomology.lean`, `RadialFilling.lean`, `SignedCancellation.lean` in full; no `variable`, no `finrank … = 6`, no `SurgeryWindows`/`AdaptedWindows` hypotheses; `Hemisphere.Sphere n` is `Lib`'s abbrev for the unit sphere in `EuclideanSpace ℝ (Fin (n+1))` |
| Filed lemmas' docstrings vs statements (12 sampled: 4 EqualRangeHomology, 2 RegularLevel, 5 LinearSphereAction, 1 Transversality; plus the 3 island module docstrings, the rewritten Lib CutTransport/Belt/SurgeryHomology docstrings, the 4 Hopf/Proof headers) | verified | read each against its statement; Belt "Main declarations" names exist in the Lib file; Hopf/Proof headers' inventories match their files except finding 5 |
| `middleSectionClass_unit_smul_of_range_eq`, `equalCutSection_class`, `conj`, `ncard…` docstring/prose descriptions | verified | statements read at head |
| Hygiene: no `sorry`/`axiom`/`maxHeartbeats`/`unsafe`/`native_decide`/`@[simp]`/`private` changes | verified | regex over the branch diff; only new-file `noncomputable section` headers; base preambles (`open scoped`, `universe u v`) unchanged in the kept files; import blocks unchanged except MinimalSystem drop and the two new island imports |
| MERGE.md §7: 4 references retargeted in Hopf/Proof CutTransport | verified (plus finding 4) | `grep coordMatrix\|eq_mul_transvection` → lines 162, 1188, 1190, 1194; `git diff fc6b6ffe^2 fc6b6ffe` |
| LinearSphereAction add/add resolution kept both blocks | verified | head file contains dfiles-a's 5 declarations after dup-hom's |
| No later branch touched the branch's files after the merge | verified | `git diff --stat fc6b6ffe 39f1d12b -- <files>` empty |
| Axioms of two new names | verified | `#print axioms`: `[propext, Classical.choice, Quot.sound]` |

## Not checked

* The build lines (`lake build …`, `Lib.AxiomAudit`, census 123) — not re-run; the integrated head
  is built and my scratch elaboration against it succeeded, which is indirect evidence only.
* The "auxiliary constants that changed module: 100" line — not itemised anywhere; auxiliaries
  are not judged by the protocol.
* Whether `Submodule.span_range_fin_succ`, `Set.ncard_range_comp_inter_range_comp_of_injective`
  or `ContinuousLinearMap.surjective_coprod_comp_left` duplicate a Mathlib lemma under another
  name — not in this packet's scope (keep + rename), not searched.
* The mathematical content of the 42 remaining Belt and 61 remaining SurgeryHomology statements —
  unchanged text, not re-read.

## Tool notes

* `split-*.json` is the most useful artefact in this receipt: per-unit line ranges and sha256s
  made the "every declaration accounted for" check mechanical. Two improvements: list structure
  projections separately (or mark them) so the envdiff move counts (52, 19) reconcile with the
  receipt's declaration counts (42, 2) without the reader having to discover why; and record the
  base blob id instead of a path under `/home/goblin/.claude/jobs/...` for `SurgeryHomology`.
* The receipt's closure table would be more trustworthy with the seed list (which `Lib` modules
  consume which constants) attached; `stay_*.txt` and `why.py` exist in the job directory and
  reproduce it in seconds, but they are outside the repo.
* The dump's `uses` graph made the closure claim fully checkable in one script; `envdiff`'s
  PROOF-NAMING classification was correct here. The `--rename` two-direction map trick works
  because the name sets are disjoint; a tool flag that states the direction would remove the
  need for the explanatory comment.
