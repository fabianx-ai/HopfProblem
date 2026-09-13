# Next steps — Kimi seat (after integration review 4, 2026-09-14)

Layout note: `Hopf/<path>.lean` holds only the stock still to be moved into `Lib/`; proof-specific
declarations are under `Hopf/Proof/<path>.lean` (same names, same namespaces). The
`Mathoverflow1973` wrapper is gone from the tree (GLM's `686b598e`); only the final theorem keeps
it. The census counts only outside `Hopf/Proof/` (baseline 1648, now 1586).

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the branch
(`git log -1`). Your C-17, C-18, C-19 and C-20 are in (citations in-tree, owner gates closed, nine
Hurewicz leftovers moved, 35 private helpers documented). Review: `Lib/reviews/INTEGRATION-4.md`
§4 "Kimi seat": GO, three record items below. Commit identity: `kimi`, as set.

## Lane C — in this order, branches `lib/C-<n>-<slug>` off the head above

1. **Record fixes** (one commit, docs only): (a) `Lib/docs/C19-LEFTOVERS.md` and the C19
   checkpoint in `Lib/reports/C.md` say statements are unchanged; two retargets were made and must
   be named: `Suspension.topSus.* -> Suspension.*` in `suspensionConeCover` (owner-confirmed rename)
   and `HigherHurewicz.hurewiczLinearEquiv -> Hurewicz.hurewiczLinearEquiv` in the six wrappers
   (shim unwind); (b) C20 documented 35 private helpers, not 34; (c)
   `Lib/docs/C-STAGE2-REVIEW.md:5` still cites `~/s6-notes/review/C.md`; point it at `Lib/docs/C.md`.
2. **The seven CHARGED leftovers** in `Hopf/Hurewicz.lean` (`SixSphereCube` data and the pinned
   `Sphere.piN_subsingleton` theorems) are proof-specific by your own classification, so under the
   layout rule they belong in `Hopf/Proof/Hurewicz.lean`, not in the stock file. Move them there
   (same names; `Hopf/Proof/Hurewicz.lean` imports `Hopf.Hurewicz`), full chain green, census
   falls by the moved count; one commit. After that `Hopf/Hurewicz.lean` should hold nothing or
   only stock still to be moved — say which.
3. Then lane C is closed; report it in `C.md` with the head. The Comparator stays owner-deferred.

Do not edit the packets of the other seats (E2, J — Muse; A, B, D, E1, H, I — GLM) or
`Hopf/LibShims.lean` (GLM's de-shim pass).

## Rules

- Gate for a change that deletes or moves `Hopf/` declarations is the full consumer chain.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
- Citations are checked against the reference before they enter a ledger; no off-tree paths.
