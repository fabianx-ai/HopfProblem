# Next steps — GLM seat (after integration review 3, 2026-09-13)

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the
branch (`git log -1`). Your `lib/A-7-linear-sphere` is in: E1 (probe closure landed, three
probes in `Lib/` with exact axioms), the B, D1 and D2 probes, the lane I quotient charts,
`LinearSphereAction.lean` Lib-only, the `Suspension.topSus -> Suspension` rename, the five
name confirmations, the 70-file documentation wave, the record fixes. Kimi's C13–C16 and
Devin's module conversion, J naturality, F2 and G1 landed in the same head; full chain green.
Review: `Lib/reviews/INTEGRATION-3.md` §3 "GLM seat". Start every new branch from this head.

Seat note: this seat is run by Devin/Astra while GLM is paused. Commit as the seat and name
the model in the report. This seat does not author E2, F, G or J; the Muse seat does not
review E1, H or I.

Settled by review 3: E1 done (old item 2); record fixes done (old item 1); name confirmations
done (old item 5); documentation wave merged (old item 6, first pass). The `topSus` rename is
taken pending the owner's confirmation (`INTEGRATION-3.md` §5.2); if the owner names a
different name, rename again with the same receipt.

## In this order, branches `lib/A-<n>-<slug>` off the head above

1. **`B.md` status** (one commit): put a current-status paragraph at the top, as `E1.md` has;
   the "[corrected] NOT complete" line is history now that
   `simplyConnectedSpace_of_open_cover` is in `SimplyConnectedCover.lean`.
2. **Lane I: Wang.** The circle cross-product prerequisites you read as C/J-owned are in
   `Lib/` (`CircleProduct.lean`, `CrossProduct.lean`); nothing is owed to you by C or J. Move
   the Hopf-side closure recorded in `Lib/reports/I-wang-dependencies.json` (232 rows) into
   `Lib/Topology/MappingTorus/Wang.lean` in dependency order, one green unit per commit,
   receipts as for E1. The FREE/CHARGED rule decides per row: `SpecialPeriods`, `Threefold*`
   and `Cusp*` vocabulary is CHARGED and is not moved; stop at the first CHARGED row on a
   path, record it in `I.md`, and continue with the rows that do not need it. Then the
   remaining I units in `I.md` order.
3. **`Mathoverflow1973` wrapper removal** after item 2, one commit, full chain green, with
   the `Hopf/LibShims.lean` aliases for `topSus` and `Hurewicz.DegreeTwo` retired in the same
   commit only if every Hopf consumer is re-routed (else keep them and say so).
4. **`import all`** in the files you own (`MorseLemma`, `SmoothFlow`, `Collar`, `Flow/Compact`,
   `Morse/Cancellation`, `Morse/Rearrangement`, `RegularLevel`): replace each by the public
   Mathlib API or by a `Lib` lemma that proves the needed fact; one commit per file, no
   statement changed. Do not add new `import all` lines.
5. **Layout** (after items 2–4): `ConnectionCancellation.lean` (9,600 lines) and
   `Cancellation.lean` split along the Milnor h-cobordism sections (`Cubic`, `CubicFlow`,
   `Connection`, `Cancellation`); in-`Lib` moves, statements unchanged, one commit per file.
6. **Docstrings**: module docstring for `SingularHomology/CrossProduct.lean` (yours: the
   coherence web lives there), per-declaration docstrings where missing, one commit per file,
   "No proof term changed."
7. **Lane H** per `H.md` (114 `RiemannMapping` declarations remain under `Hopf/`).

Rules unchanged: `ps` before `lake build`; never `lake update`/`cache get`; never push; every
report cites only what is in the tree; nothing is "COMPLETE" while its probe theorem is still
under `Hopf/`; never rewrite another seat's ledger, review or draft.
