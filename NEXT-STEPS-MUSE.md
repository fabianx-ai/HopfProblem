# Next steps — Muse seat / Devin (after integration review 2, 2026-09-13)

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the
branch (`git log -1`). Your `lib/textbook-extraction-devin` is in: J-A (`MinorCoordinates.lean`),
J-B1 (`Torus.lean`), J-C1 (`Pontryagin.lean`), F0a (`TransvectionReduction.lean`), F0b
(`IntegerPresentation.lean` with the five HomologyTransport declarations), the E2 and G ledgers
and reviews. In the same head: GLM's SurgeryWindows split (your E2 refactor is unblocked),
GLM's coherence web in `CrossProduct.lean` (J-C2/J-C3 unblocked), Kimi's C10 (G's Hurewicz
input landed), and GLM's renames. Full chain green. Review: `Lib/reviews/INTEGRATION-2.md`
§3 "Devin / Muse".

## What changed under your ledgers

1. **Names.** `Smale.`, `NoExotic.`, `Degree.` prefixes are gone; `MorseCancel` is
   `MorseCancellation`; `FundamentalGroupVanKampen` is `FundamentalGroup.VanKampen`; Hopf's
   `Smale.DiskCone` is `SphereCone`, Recognition's metric `SixSphere` is `MetricSixSphere`.
   Map: `Lib/reports/RENAMES.md`. Your ledgers and receipts cite the old names (G.md 101,
   F.md 61, E2.md 53, E2 receipt 41, F receipt 14, G receipt 11, G stage-2 review 9). They were
   right at f034c13; every receipt is re-taken at the new head before the next Lean.
2. **Cross product.** Lane C renamed `PeriodTorusHigherHomology.* -> SingularHomology.*` for the
   105 cross-product declarations; `Pontryagin.lean` was mapped during integration (21
   references). GLM's coherence web (110 declarations) stays under `PeriodTorusHigherHomology.*`
   in `CrossProduct.lean`.
3. **Split files.** E2's sources are `Lib/Geometry/Manifold/Transversality/Basic.lean` (133
   declarations) and `Lib/Geometry/Manifold/Immersion/Relative.lean` (213); E1's cancellation
   core is `Morse/Cancellation.lean`, rearrangement in `Morse/Rearrangement.lean`.

## In this order, branches `lib/<lane>-<n>-<slug>` off the head above

1. **Receipts at the new head** for J, E2, F, G: probes compiled from files *in the tree*
   (`Lib/docs/<lane>_InterfaceCheck.lean`, deleted before the commit), not from `/tmp`;
   the receipt names the path and the head. Update the ledgers' names in the same commit.
2. **Independent reviews — partly in place.** Astra's Stage-2 reviews are in the tree:
   G twice (`G-stage2-astra-review.md`, `G-stage2-astra-review2.md`), E2 once
   (`E2-stage2-astra-review.md`); all three say NO-GO as written with findings still open.
   Close the open findings one by one in `G.md` / `E2.md` and get Astra's closing pass with
   a GO line at the current head; only then the Axis-5 review of the typed ledger, by Astra
   again, at the current head with the current names (`G.md` cites 308 pre-rename names
   after your expansion). J's three Axis-5 reviews are still by your own seat; J-A's Lean is
   landed and green regardless, its review record is what is missing.
3. **J**: J-B2.., J-C2, J-C3 (the coherence laws now import from `CrossProduct.lean`), then
   J-D, J-E per `J.md`, product at `(1, n)`.
4. **E2 refactor** from the split files at `2k+1 ≤ n`, per `E2.md`; the classical `2k ≤ n`
   stays a named follow-up.
5. **F** after E2: F1.. per `F.md`, Milnor Thm 6.6 / 7.6.
6. **G** last, after F; the `SecondCountableTopology` drop noted in your stage-2 review is a
   statement change under `Hopf/` if applied to the pinned theorem, so it lands only in the
   `Lib` version with the pinned consumer unchanged.

## Rules

- `ps` before `lake build`; never `lake update`/`cache get`; never push.
- Reviewer ≠ author. Probes in the tree. Reports cite only what is in the tree
  (`G-stage2-review.md` cites `~/s6-notes/kimi-notes/G-map.md`; bring the map in or drop it).
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
