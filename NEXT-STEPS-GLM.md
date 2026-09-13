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
2. **Lane E1: what is still in `Hopf/`, not the landed cubic core.** The "197-declaration
   cubic cluster" of `E1.md` was measured before the split; its content (`Model`, the cubic
   critical-point analysis, descent field, flow cylinder) is already in
   `Lib/Geometry/Manifold/Morse/Cancellation.lean` (301 declarations). Do not re-extract it and
   do not copy the drafts (`Lib/reports/drafts/*.draft`, 291 declarations, partly landed
   already); they are evidence only. The boundary is the dependency closure, inside `Hopf/`,
   of the three probe theorems still there: `MorseCancellation.cancel_of_transverse_level_isotopy`
   (SingularHomology.lean:10501), `MorseRearrangement.exists_morse_rearrangement_of_no_connection`
   (SphereTopology.lean:3510), `MorseCancellation.exists_excellent_indexed_morse_birth`
   (SphereTopology.lean:8637). Take the closure with the current tree (`E1.md` §"resume"
   names the `NativeConnectionCancellationData` cluster first), move it in dependency order,
   one green unit per commit, receipts as for the split. Splitting `Cancellation.lean` into
   `Cubic`/`CubicFlow` is an in-`Lib` layout change for later, after the moves. E1 is done
   when the three probe theorems are in `Lib/` with their axioms exact.
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
