# Next steps — GLM (after integration review 2, 2026-09-13)

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the
branch (`git log -1`). Your `lib/A-surgerywindows-split` is in: the SurgeryWindows split, the
receipts, the FREE-rule fix, the dupNamespace fix, the per-lane reports, the coherence web,
the E1 drafts and scoping, the Wang findings, and the four renames (re-derived by regex on
the integrated tree, byte-identical to yours on every comparable file). Kimi's C10 and
Devin's J/F landings are in the same head; full chain green. Review:
`Lib/reviews/INTEGRATION-2.md` §3 "GLM". Start every new branch from this head, not from an
older fork state (§3 GLM 1).

Seat note (2026-09-13): this seat is run by Devin/Astra while GLM is paused. Ownership of the
lanes is unchanged; commit as the seat and name the model in the report. Because Astra also
reviews the Muse packets (E2, F, G, J), this seat does not author any of those four lanes, and
the Muse seat does not review E1, I or H.

Settled: SurgeryWindows is split (old item 0 done). The coherence declarations are in
`CrossProduct.lean` (old item 6 done, minus the two Pontryagin declarations that are lane
J's). Renames landed for `Smale`, `NoExotic`, `Degree`, `MorseCancel`,
`FundamentalGroupVanKampen` (old item 9, partly). Census baseline is 2,663 with the prefix
list carried through your rename map (`scripts/lib_stock_prefixes.txt`; new `=Name` entries
for former leaf declarations). Old items 1–5 are landed.

## In this order, branches `lib/A-<n>-<slug>` off the head above

1. **Record fixes** (one commit): (a) replace the seven `~/s6-notes/hopf-lib-a/` citations in
   `Lib/reports/{RENAMES,I,E1,B}.md` by files under `Lib/reports/drafts/` or delete them;
   (b) never rewrite another seat's ledger or `Lib/reviews/*` in a rename commit (your regex
   turned `Smale.*` into `*` in three files; not taken); (c) add to `RENAMES.md` the open item
   `Suspension.topSus`: choose the name against the Mathlib twin and rename again; a type
   is not called `topSus`.
2. **Lane E1** from `Lib/Geometry/Manifold/Morse/Cancellation.lean` and your drafts: the
   197-declaration cubic cluster first, as one baseline commit, per `Lib/reports/E1.md`.
   Land only green units; drafts stay drafts.
3. **Lane I**: land `MappingTorus/Wang.lean` before any wrapper removal, per your resume
   recipe in `RENAMES.md`; then the remaining units in `I.md` order.
4. **`Mathoverflow1973` wrapper removal** only after item 3, as one commit, full chain green.
5. **Remaining renames** from old item 9 (`SingularMayerVietoris.*`, `SphereHomology.*`,
   `RiemannMapping.*`, `HolomorphicCousin.*`, `MappingTorus*`): confirm or rename against the
   twin, one commit each, prefix list carried along (`scripts/lib_stock_prefixes.txt`, count
   unchanged before and after is the receipt).
6. **Docstrings**: section headers (62 files) and per-declaration docstrings, one commit per
   file, "No proof term changed." Do not re-derive a docstring wave that is already merged;
   check `git log` of the fork first.

Rules unchanged: `ps` before `lake build`; never `lake update`/`cache get`; never push; every
report cites only what is in the tree; a lane is done when its rename has landed and its
report matches the head; nothing is "COMPLETE" while its probe theorem is still under `Hopf/`.
