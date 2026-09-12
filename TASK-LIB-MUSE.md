# TASK LIB-MUSE — packet lanes J, E2, F, G (taken over from the Kimi seat)

**TruthSeed:** `lib-extraction:generalize-the-pinned-dimensions`
**For:** Muse Spark, working on a fork of github.com/fabianx-ai/HopfProblem, branch
`lib/textbook-extraction`. Start every branch from the head the owner names when handing you
the branch (692e7f5f or later); toolchain leanprover/lean4:v4.33.0; Mathlib pinned in
lake-manifest.json. Never `lake update`, never `lake exe cache get` on the shared box: the
`.lake` seed is provided by the owner.
**Nature:** GENERIC library extraction, upstream-shaped, *generalize-then-move*. The full
seven-axis cycle applies. Read, in this order, before anything else:

1. `lean-protocol.md` (repository root): Stages 1–7, the section "Extraction mode", and the
   Stage-5 GO conditions. This file governs everything below.
2. `Lib/README.md`, then the reference example `Lib/AlgebraicTopology/Hurewicz/`
   (`Degree1.lean` lines 12–70 first).
3. `TASK-LIB-KIMI.md`: the lane specifications for J, E2, F, G (sections "Lane J", "Lane E2",
   "Lane F", "Lane G"), the COPY / DO NOT COPY checklist, "OUT OF SCOPE", "Build discipline",
   "Commit conventions", "Report". Those sections are binding for you unchanged; only the
   ownership and order below differ from that file.
4. `Lib/reviews/INTEGRATION.md`: the review that judged the four packets. Every item it lists
   for J, E2, F, G is your to-do list.
5. The four packets as they stand: `Lib/docs/J.md`, `Lib/docs/E2.md`, `Lib/docs/F.md`,
   `Lib/docs/G.md` (Axis-1 textbook plus Axis-5 ledger drafts). They were drafted by the Kimi
   seat; you continue them as author. You may rewrite any part; keep the textbook content
   that the review did not fault.

## What you own and what you do not

- Yours: lanes **J, E2, F, G**, in that order, and their files `Lib/docs/{J,E2,F,G}.md`,
  `Lib/docs/<lane>-INTERFACE_RECEIPT.md`, `Lib/reports/{J,E2,F,G}.md`, and the `Lib/` target
  files named for those lanes in `Lib/EXTRACTION_PLAN.md` §2.
- Not yours: **lane C** (Kimi, in progress: `Lib/AlgebraicTopology/Hurewicz/*` beyond the
  reference files, `Lib/docs/C.md`, `Lib/reports/C.md`), and every GLM lane (A, B, D1, D2, E1,
  H, I; `TASK-LIB-GLM.md`). If you need a declaration from one of them before it has landed in
  `Lib/`, import the `Hopf` module as today and record the dependency in the ledger.
- Ownership in doubt goes to GLM. Do not resolve it yourself; write it as an open item in the
  lane report and continue.

## Settled owner decisions (2026-09-12) that shape your ledgers

- **E2 dimension condition:** state the lane's theorem at `2k+1 ≤ n`, which is what the tree's
  perturbation proof proves and covers every project instance (k = 2, n ≥ 5 and k = 1, n ≥ 3).
  Record the classical `2k ≤ n` as a named follow-up requiring the Stiefel-bundle argument. The
  "2k ≤ n" wording in `TASK-LIB-KIMI.md` is superseded.
- **J product shape:** state the Pontryagin product at `(1, n)` now, matching the landed cross
  product in `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`; general `(p, q)` is a
  named follow-up once C's general cross product lands.
- **SurgeryWindows** is GLM's. GLM splits `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean`
  along the E1/E2/F target files (`NEXT-STEPS-GLM.md` item 0). Your E2 refactor starts from
  the split files once they are on the branch; the E2 ledger and probes do not wait for that.
- **Milnor numbers for F:** the Whitney lemma is *Theorem 6.6* and the Basis Theorem is
  *Theorem 7.6* (h-cobordism). Earlier files carried 6.4/7.8; those were our error.
- The 42 coherence declarations in `Hopf/LCP/Specialization.lean` (formerly "G-J3") are GLM's;
  import them from `CrossProduct.lean` when they land.

## No packet starts Lean until it is GO

Verdicts at 856e4762: J DRAFT (closest), E2 DRAFT, F DRAFT, G NOT GO. GO requires, per
`lean-protocol.md` Stage 5: a Stage-2 review artifact committed in the tree with the reviewer
named; every ledger row with an exact Lean signature (binders, instances, universes, result)
and all `ChallengeNode` fields, no prose for types; namespaces that resolve at the current
head; a compiled producer probe and consumer probe (`*_InterfaceCheck.lean`,
`*_InterfaceConsumerCheck.lean`, compiled with `lake env lean`, deleted before the commit) with
a durable `Lib/docs/<lane>-INTERFACE_RECEIPT.md`; and an independent Axis-5 review by a seat
that is not you. The owner assigns the reviewer; ask for one when a packet is ready by naming
the commit in your report.

## Order of work

1. **J** (depends only on lane A, landed). Replace the `H₁ G →ₗ[ℤ] Hₙ G` / `⋀[ℤ]^n` notation
   rows with Lean signatures (`exteriorPower` is not an identifier at the pin; the notation
   `⋀[ℤ]^n M` is); probe, receipt, review in tree; then J's Lean per `TASK-LIB-KIMI.md`
   "Lane J", product at `(1, n)`.
2. **E2** (ledger now; refactor after GLM item 0). Exact signatures for the immersion and
   embedding rows with their `Smale.ManifoldImmersion.` namespace; drop the "Milnor TDV §2
   Lemma" pointer (TDV §2 is Sard–Brown); theorem at `2k+1 ≤ n`; probe, receipt, `E2-review.md`
   committed; then the in-`Lib` refactor from GLM's split files.
3. **F** (after A, D1, D2, E1, and your E2). Land F0a and F0b first: they depend only on
   Mathlib. Replace the `…` inside `primitive_row_has_unit_after_column_additions`; write F7 and
   F11 as signatures; add the `Smale.` namespaces to `MorseSurgeryData.beltIntersectionSign` and
   `RankThreeWhitneyModel.Space`.
4. **G** last (after C, landed by Kimi, and your F). Write the Stage-2 review; bring the ledger
   body (`G-map.md` §1) into the packet; add the `MorseCancel.` namespaces; probe, receipt.

While a lane is blocked, write the Axis-1 textbook and the Axis-5 ledger of the next one; they
need no landed code.

## Rules the review found broken; they hold from the first commit

- No packet "waits for X to land": A, D1, D2 and C's landed part are on the branch. Receipts
  are produced at the current head before Lean starts.
- Citations are checked against the reference, by theorem number, before they enter a ledger.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
- Commit as yourself: set `git config user.name` / `user.email` for your seat before the first
  commit, so authorship is attributable. No trailers. **NEVER git push.**
- `python3 scripts/lib_stock_census.py --check` before every commit; `--update` after every
  extraction commit; commit the lowered baseline. `ps` before every `lake build`; the box is
  shared with two other seats.
