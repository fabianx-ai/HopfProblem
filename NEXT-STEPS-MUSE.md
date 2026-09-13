# Next steps — Muse seat (after integration review 4, 2026-09-14)

Only lanes J and E2 are open on this seat (owner, 2026-09-13); F and G are closed as they stand.

Layout note: `Hopf/<path>.lean` holds only the stock still to be moved into `Lib/`; proof-specific
declarations are under `Hopf/Proof/<path>.lean` (same names, same namespaces). The
`Mathoverflow1973` wrapper is gone from the tree (GLM's `686b598e`); your ledgers that still spell
`Mathoverflow1973.` are stale by that prefix only. The census counts only outside `Hopf/Proof/`
(baseline 1648, now 1586). The split's demoted list was corrected: `Lib/reports/proof-split/FREED.md`
— 175 of the 475 rows were demoted by a spurious edge and are pure moves; your S-path landing moved
62 of them, and 40 more `PeriodTorusHigherHomology` rows under `Hopf/Proof/LCP/CuspFilling.lean`
are yours.

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the branch
(`git log -1`). Your `lib/textbook-extraction-muse-i3` is in: citations repointed, module
docstrings, the `import all` removal in `Transversality/Basic.lean` and `Immersion/Relative.lean`
with the two transparent variants, the E2/G/J Axis-5 reviews, the S-path landing
(`CirclePaths.lean`, 88 declarations). GLM's Wang landing had moved 23 of the same rows into
`Wang.lean`; the integration kept yours and made `Wang.lean` import `CirclePaths`. Review:
`Lib/reviews/INTEGRATION-4.md` §4 "Muse seat": GO, record items below. Commit identity: `muse`.

## In this order, branches `lib/<lane>-<n>-<slug>` off the head above

1. **Record fixes** (one commit, docs only): (a) `Lib/reports/RECEIPTS.md` — the S-path bullet
   must say that 62 of the 88 rows came from `Hopf/Proof/` (rows listed in `DEMOTED.md`, now
   `FREED.md`), carry the commit hash `6211eadc` and its job count, and the section header
   "head `84d9450`" is stale; (b) `Lib/docs/E2-fresh2-subagent-review.md` — the path rewrite
   produced `git -C the repository root rev-parse HEAD` and "relative to `the repository root`";
   restore the command with the path elided in brackets; (c) `J.md` was edited after the Axis-5
   stamp at `90cd3d9` — say so in the receipt.
2. **J, the freed rows**: the 40 `PeriodTorusHigherHomology` declarations in `FREED.md` under
   `Hopf/Proof/LCP/CuspFilling.lean` are pure moves; land them in `CirclePaths.lean` or the
   `Lib` module their subject names, statements verbatim modulo the disclosed retargets, Lake
   build, one green unit per commit, receipts as for the S-path.
3. **J-B/J-C/J-D/J-E** certification per `J.md` (they are uncertified; the S-path gate is
   discharged), then the product at `(1, n)`.
4. **E2 refactor** at `2k+1 ≤ n` from the split files, per `E2.md`.

## Rules

- `ps` before `lake build`; never `lake update`/`cache get`; never push; Lake, not direct `lean`.
- Reviewer ≠ author; a fresh-context subagent is a reviewer. Probes in the tree. Reports cite only
  what is in the tree (no `/tmp`, `~`, `/home`).
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
- Do not edit E1, H, I files or ledgers (GLM seat), the C packet (Kimi seat), `Hopf/LibShims.lean`,
  or the F and G packets (closed).
