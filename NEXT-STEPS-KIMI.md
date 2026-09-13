# Next steps — Kimi seat (after integration review 3, 2026-09-13)

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the
branch (`git log -1`). Your `lib/C-14-integrated-receipt` is in: the refreshed receipt, C13
(ten Recognition proofs are now instantiations, statements unchanged), C14
`Hurewicz/Naturality.lean`, C15 `Topology/Homeomorph/DiskCube.lean`, C16
`SecondHurewicz -> Hurewicz.DegreeTwo` with shims, the archived independent review. Full chain
green at the integrated head (`Lib/reviews/INTEGRATION-3.md` §2), which covers the gates you
could only run on the working tree. Review: `INTEGRATION-3.md` §3 "Kimi seat".

Old items 1–6 are closed (`C.md` §"NEXT-STEPS item disposition"). Old item 7 is not.

## Lane C — in this order, branches `lib/C-<n>-<slug>` off the head above

1. **Seat identity before the next commit** (old item 7): `git config user.name`/`user.email`
   for the seat in this clone; the seven merged commits carry the owner's name and address.
2. **Citations** (one commit): `Lib/docs/C-FOLLOWUPS-INDEPENDENT-REVIEW.md` has 24
   `file:///home/kimi/...` links and `C-INTERFACE_RECEIPT.md` two `/home/kimi/s6-notes/` log
   paths. Rewrite the `file://` links to repository-relative paths (say at the top that the
   archive's links were rewritten, nothing else); bring the cited logs in under
   `Lib/docs/logs/C/` or drop the citation. Rule: every report cites only what is in the tree.
3. **Owner gates**: the two conditions of the independent review (Stage-2 order exception,
   Comparator) are the owner's; the answers will be recorded in `INTEGRATION-3.md` §5. Once
   answered, close them in `C.md` in one commit; do not run the Comparator yourself.
4. **`Hopf/Hurewicz.lean` leftovers**: the 23 declarations still there; classify each FREE or
   CHARGED, move the FREE ones with the usual receipt, record the CHARGED ones.
5. **Docstrings**: module docstring for `Hurewicz/Straightening.lean`; per-declaration
   docstrings in the C files, one commit per file.
6. **Shim retirement** for `Hurewicz.DegreeTwo` and the cross-product exports is part of the
   GLM seat's wrapper removal (`NEXT-STEPS-GLM.md` item 3); leave `Hopf/LibShims.lean` alone.

## The packets E2, F, G, J — Muse seat; E1, H, I — GLM seat

Do not edit those packets or their target files.

## Rules

- Gate for a change that deletes `Hopf/` declarations is the full consumer chain.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
- Citations are checked against the reference before they enter a ledger; no off-tree paths.
