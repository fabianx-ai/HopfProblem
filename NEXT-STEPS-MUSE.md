# Next steps — Muse seat / Devin (after integration review 3, 2026-09-13)

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the
branch (`git log -1`). Your `lib/textbook-extraction-devin-2` is in: the E2 and G repairs
with your four subagent reviews, the `module` conversion of 25 provider files, J naturality
(`CircleProduct.lean`, `CrossProduct.lean`), F2 (`Whitney/BigonModel.lean`), G1
(`Morse/MinimalSystem.lean`). In the same head: GLM's E1 (`Morse/ConnectionCancellation.lean`,
`RearrangementTheorem.lean`, `Birth.lean`), Reeb, the `Suspension.topSus -> Suspension`
rename (your ledgers that say `topSus` are stale again; map in `Lib/reports/RENAMES.md`),
Kimi's C14–C16 (`Hurewicz.DegreeTwo`). Full chain green under Lake
(`Lib/reviews/INTEGRATION-3.md` §2), which is the first Lake verification of your commits.
Review: `INTEGRATION-3.md` §3 "Muse seat".

## In this order, branches `lib/<lane>-<n>-<slug>` off the head above

1. **Lake, not direct `lean`.** Use the recipe in `SEAT-SETUP.md` (the `GIT_CONFIG_*` lines
   stop Lake from re-cloning Mathlib). A direct-`lean` build is not a receipt.
2. **Citations** (one commit): `/home/ox-alpha/...` in the four `*-fresh*-subagent-review.md`
   files, `/tmp/sidekick-modconv-batch3-*/` in `Lib/reports/RECEIPTS.md`,
   `~/s6-notes/J-review*.md` in `J.md` and `J-INTERFACE_RECEIPT.md`. Bring the evidence in
   (`Lib/docs/logs/<lane>/`) or drop the citation; the reviews are your seat's and may be
   edited for paths only, with a line saying so.
3. **Reviews.** Fresh-context subagents count as independent reviewers (owner, 2026-09-13);
   your `fresh`/`fresh2` reviews stand. Missing: the closing pass on E2 and G at the current
   head with a GO line, by a fresh reviewer (zero context, not the authoring session), then
   the Axis-5 review of the typed ledgers with the current names (`Suspension`,
   `Hurewicz.DegreeTwo`, `SingularHomology.CircleTopology`), again by a fresh reviewer. J's
   Axis-5 reviews the same way. Until then E2 and G stay DRAFT, as their ledgers say.
4. **Module docstrings** for `Morse/MinimalSystem.lean` and `Whitney/BigonModel.lean`; the
   twin named. One commit.
5. **`import all`**: none added from now on; in your own files (`Transversality/Basic.lean`,
   `Immersion/Relative.lean`) replace the two lines by the public Mathlib API or a `Lib` lemma.
   The other eight lines are in GLM-owned files and are on that seat's list.
6. **J**: the circle-path/section cluster and the higher coordinate/exterior boundaries
   (`RECEIPTS.md` §"Still open"), then J-D, J-E per `J.md`, product at `(1, n)`.
7. **E2 refactor** at `2k+1 ≤ n` from the split files, per `E2.md`.
8. **F** after E2: the remaining geometric/Whitney/slide blocks per `F.md`, Milnor 6.6 / 7.6.
9. **G** last: G2a–G6 after F; the `SecondCountableTopology` drop only in the `Lib` version.

## Rules

- `ps` before `lake build`; never `lake update`/`cache get`; never push.
- Reviewer ≠ author; a fresh-context subagent is a reviewer. Probes in the tree. Reports cite only what is in the tree.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
- Do not edit E1, H, I files or ledgers (GLM seat) or the C packet (Kimi seat); the `module`
  conversion of their files is taken this once, not a precedent for editing them.
