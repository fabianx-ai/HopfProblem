# Next steps — Kimi seat (after integration review 2, 2026-09-13)

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the
branch (`git log -1`). Your `lib/C-10-boundary` is in: the boundary relation, both round
trips, `hurewiczLinearEquiv` at general `n ≥ 2` (`Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean`),
the adapters that replaced the degree-3..6 towers (`Hopf/Hurewicz.lean` 9,631 -> 423 lines),
`HopfDegree.lean`, and the cross-product rename with shims. GLM's renames landed in the same
head (`Smale.`, `NoExotic.`, `Degree.` prefixes dropped; `MorseCancel` -> `MorseCancellation`);
the map is `Lib/reports/RENAMES.md`. Full chain green; no `Hopf/` statement changed.
Review: `Lib/reviews/INTEGRATION-2.md` §3 "Kimi seat + Devin".

Old items 1 (C10) is landed. Old items 2–7 stand. New first:

## Lane C — in this order, branches `lib/C-<n>-<slug>` off the head above

1. **Bring the record to the code — done in 88bdcc73, one remainder.** `Lib/reports/C.md`
   now says C10 and C13 are landed and the hand-off is historical; the twelve documented files
   are merged (docstrings only, code identical). Remainder: the record still cites pre-rename
   names (`Lib/docs/C.md` 28, `Lib/reports/C.md` 7, `C-INTERFACE_RECEIPT.md` 4; the map is
   `Lib/reports/RENAMES.md`), and the receipt was taken at your branch head `1a313843`, not
   at the integrated head. Re-take it at the head above with the current names, and name the
   reviewer of `C-STAGE2-REVIEW.md` if it can be established, otherwise leave it marked
   recovered.
2. **C13**: the general `sphere_homotopicRel_of_topClass_eq` is in `HopfDegree.lean`; the
   pinned `n = 6` versions are still declared in `Hopf/Recognition.lean` (lines ~978, ~1009).
   Re-derive them as one-line instantiations, delete the pinned proofs, statements unchanged,
   `lake build Hopf.Recognition` then the consumers; record the receipt in
   `Lib/docs/C13-CLASSIFICATION.md` §"Production verification receipt".
3. **Interface receipt** (old item 2), taken at the current head with the current names.
4. **FREE rule in `Lib/`** (old item 3): the renames listed there, and the
   `HigherHurewicz -> Hurewicz` twin-naming commits.
5. **Docstrings** (old item 4), one commit per file.
6. **Report corrections** (old item 5) and the committed Stage-2 review (old item 6), old
   item 7 (`GenLoop`).
7. **Authorship**: set `git config user.name` / `user.email` for the seat before the next
   commit; say in the report which model ran the seat for which commits.

## The packets E2, F, G, J — Muse seat

Unchanged: lanes J, E2, F, G are the Muse seat's (`TASK-LIB-MUSE.md`, `NEXT-STEPS-MUSE.md`).
Do not edit those packets or their target files. The general cross product for J's `(p, q)`
follow-up is now landed; nothing else is owed from C to a packet.

## Rules that the reviews found broken; they hold from now on

- Gate for a change that deletes `Hopf/` declarations is the full consumer chain, not one
  module.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names,
  and says "not landed" only for ones that do not.
- Citations are checked against the reference, by theorem number, before they enter a ledger.
