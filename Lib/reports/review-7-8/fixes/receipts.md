# Fix round after the reviewer pass — `receipts` (2026-09-21)

Worktree `/home/goblin/hopf-fix-receipts`, branch `fix/receipts`, base `62d45257`
(`lib/integration`, the commit that added the twenty-one reviews).  Seat: the one agent allowed to
edit `Lib/reports/round-7/**`, `Lib/reports/round-8/**` and `Lib/reviews/INTEGRATION-{7,8}.md`.

**Scope: receipt and coordinator-review *text* only.  No Lean file was touched** (`git diff
--name-only 62d45257..HEAD` is 22 `.md` files, 0 `.lean`), so no build, no envdiff, no rename map.

Source of truth: the `[wrong receipt]` and `[incomplete]` findings of the twenty-one reviews in
`Lib/reports/review-7-8/*.md`, consolidated in `Lib/reviews/REVIEW-7-8.md` §3, paragraph "Receipts
(counts and wording)".  All twenty-one reviews were read in full.

## Method

Two forms of edit, per the assignment:

* **Headline figures corrected in place**, each marked `(corrected)` with the original figure quoted
  beside it, because several of them were reported to the coordinator or copied into commit messages
  (packet 08's 118/217, `dfiles-a`'s "40 blocked") and a silent rewrite would break the link to that
  history.  Per-file table rows whose arithmetic the headline depends on are corrected the same way.
* **A dated `## Corrections after the reviewer pass (2026-09-21)` section appended to every edited
  receipt**, listing each finding, what it changes, and what the reviewer verified.  Findings that
  are code fixes (docstrings, citations, lifts) are named there too, with a pointer to
  `Lib/reviews/REVIEW-7-8.md` §3 and the packet fix agent who owns them, so no receipt claims a fix
  it did not make.

Where a review gives an exact number it is used.  Where a count is disputed and the receipt never
stated its counting rule, **both counts are recorded as a disagreement rather than one being
picked** — this happens three times: packet 01's `: Type` binders (receipt 74/57, reviewer 72/55),
packet 03's binder total (receipt 99, its own rows 34 + 106 = 140, reviewer's literal count 193) and
packet 09's audit-derived binder figures.  In packet 03's case the *withdrawal* is unambiguous and
recorded as such: 0 widened stands, 106 is what the receipt's rows support, the 99 is withdrawn.

## One commit per receipt file (22 commits, `62d45257..HEAD`)

| commit | file | findings closed |
|---|---|---|
| `21effda3` | `round-7/packets/RECEIPT-01.md` | pins 119/24 → **116/27** with three per-file "before" numbers (6→7, 3→4, 35→36); the `Generators` envdiff row explained by `pullback_simplex`, not the `Cochains` abbreviation; `moduleDual`/`dualComplex` land in `max u w`; 11 not 12 narrative files; binder counts recorded as disputed; no per-packet envdiff in tree |
| `1c466688` | `RECEIPT-02.md` | totals 101/126/25 → **103/134/31**; `Coproduct.lean`'s "not a local fix" refuted (`Abelian.hasFiniteBiproducts`), item re-opened; the `PositivePrimitives`/`Vanishing` "forced by the interface" reason refuted (only `chains` is pinned); occurrence vs declaration counts labelled; `FirstHurewicz.ChainHomology` exists in `Hopf/LibShims`; public/private split; 113 of 218 |
| `e7bc8ecb` | `RECEIPT-03.md` | binder total **withdrawn** (0 widened, 106 by its rows); `CanonicalPositiveCofinalExt.lean` recorded as silently skipped; the forced-pin claims recorded as stale at the merge; 858 → **857** changed lines |
| `3f02d27b` | `RECEIPT-04.md` | pins 81 → **80**, mixed units recorded; the +1 constant named (`…higherDirectImageResolutionSheafificationIso._proof_5`); a fourth outside forcer added (`cohomologyAddCommGroup`); the six `AdaptedWindows.lean` binders recorded as found-and-left |
| `5f2aa51a` | `RECEIPT-05.md` | the only receipt-text finding: no envdiff artefact in the tree (the reviewer found **no** `[wrong receipt]` here at all) |
| `4c6cffe4` | `RECEIPT-06.md` | **0 pins / 6 binders** (the same six edits had been counted twice); docstrings 395 → **392** and `TransvectionReduction` 9 (1/10) → **10 (0/10)**; forced pin attributed to `groupHomology`, not `Rep`; coverage per file; the un-named 8 lost / 8 added auxiliaries; two mislabelled table cells; the dropped "Twin" information |
| `7816a83f` | `RECEIPT-07.md` | binders "58 + 1" → **62**; `AcyclicResolutionH1` 15 → **16**; `OverBase` 40 + 21 → **62 = 40 + 22**; the surviving `(C13)`, `(C14)`, `(C8)` and "receipts" jargon; no per-packet envdiff |
| `442fef98` | `RECEIPT-08.md` | **334 / 108 / 226** and **35** docstrings and sections **A (100) / B (133)**, with the note that 118/217 propagated into `835b39be` and INTEGRATION-7; the `ConstantProduct*`/`ConstantSheafH1` forcer corrected to `SingularCochains.chains`; the second `(C24)`; three envdiff-section inconsistencies; no envdiff in tree; the cross-receipt `pushforwardStalkEquiv` location |
| `b831736d` | `RECEIPT-09.md` | 316 → **317** pins (`GlobalPatch` 7 → 8); "forced by an imported interface outside the packet" qualified with the three files' own chokepoints; no envdiff in tree; binder rule unstated |
| `58a1d481` | `RECEIPT-10.md` | the +1 constant is **`TopCat.SingularCochainSheaf.unit._proof_1`**; one of `PrimitivesH1`'s 14 "forced" pins is not forced; the `A`-side forcing chain changed by packet 01 mid-round (still forced, through `HasWeakSheafify`); three internal inconsistencies |
| `2f4a491d` | `round-7/preamble/RECEIPT.md` | a **method caveat** under removal rule (b): `autoImplicit` is on in all 96 minimised files (no `leanOptions` in `lakefile.toml`), compile-success was not evidence, the envdiff was the guarantee (it caught `SquareRoot`/`ω`); the 410 reconciled as **411 notation artifacts + 14 `_proof_` of `CrossProduct.lean` − 15 added**, with the note that a definition *body* changed (benign `Prop` instance) and that envdiff hashes types only; **89 × `universe u v` + 1 × `universe u v w`**; 227 not 230 files; the instance-path description; `Challenge.lean:46` |
| `eb84a251` | `round-7/names/RECEIPT.md` | a **per-declaration twin table** for `Contragredient.lean` marking the five twin-less deletions and the type mismatch of the other two; the `AddCommGroup.lean` reason corrected (`Sheaf.H` is a reducible `abbrev`; the blocker is `TopCat.Sheaf`); cherry-picks cite no originals; the extra blank line in `77af0c88`; the stale `Int.signed_residual_coordinate_zero`; mixed probe-count units |
| `1d050396` | `round-8/pins/RECEIPT.md` | chokepoint-8 mechanism: **instance argument of `germ` at a universe metavariable**, not bare binders, `autoImplicit` irrelevant, with the detector that does work; §3 **32 files / 280 pins / 9 occurrences**; the `ULift ℤ` **protocol** obstruction added; "only proof-text edits" corrected; §6's omitted third group of 9; "one commit per chokepoint" qualified; two stale packet items; `pushforwardStalkEquiv`'s file |
| `5bab8bc9` | `round-8/dup-hom/RECEIPT.md` | table B twin → **`SingularMayerVietoris.connectingMap_naturality` at `chainSequenceMapOfMapsTo`**; monolith **1,810** lines; the double-counted added name; "character-for-character" modulo whitespace; two file/line refs; the rename-map gap; item 3 **no longer blocked** (`GlobalUnitH1Criterion.lean` deleted by `dup-sheaf`); the `MERGE.md` mis-attribution |
| `6dce1952` | `round-8/dup-sheaf/RECEIPT.md` | the **five** `PROOF-NAMING` names pasted verbatim (two had been named); the **`Lib/AxiomAudit.lean` edit** (119 diff lines) and `Lib.lean` listed; `forgetIso`'s twin marked definitionally equal; two twin locations added |
| `4ee5f202` | `round-8/dfiles-a/RECEIPT.md` | Belt **42** blocked (not 40, incl. in commit `1a7358c0`'s body); MinimalSystem **8** importers; the **42-vs-52 move row reconciled** by the ten `CenteredSheetPassage` projections (and `BandData`'s five); the MiddleBlocks merge-time edit forwarded to `MERGE.md` |
| `4afdf360` | `round-8/dfiles-b/RECEIPT.md` | `fibre_constant_of_ker_le` recorded as **deleted, no named twin, reason** in both tables, **with the note that a fix agent is re-adding it**; `MonoidHom.liftOfSurjective` is in **`Subgroup/Basic.lean:930`**; the three untaken packet suggestions; the dead code parked under `Hopf/Proof`; the stock→`Hopf.Proof` import direction; three unlisted cosmetic edits |
| `3fba36e9` | `round-8/dfiles-c/RECEIPT.md` | "remain axiom-audited transitively" → **"unprobed"**, with `Hopf/Proof/AxiomAudit.lean` being added; the instance cause corrected (`TopCat.Sheaf` is a non-reducible `def`); the two Mathlib paths (`Ext/Basic.lean:239`, `Sheaves/Sheafify.lean:137`); the pending `w4-w1-solution` reroute; ten call sites + two probes; the moved auxiliary is the first `local instance`'s |
| `26b6221a` | `round-8/moved/RECEIPT.md` | item 3's "docstrings were added on this branch's base" → **false**, 0 at base and at head, **being added now**; the envdiff explanation of the 39 replaced by the real breakdown; the duplicate `import` lines and the commit that adds them; the two Mathlib twins and two over-promising names; 226 lines; l.899 |
| `1b6711ec` | `round-8/MERGE.md` | lost sub-counts **170 + 2**; the **99** residue listed by module (reviewer's counts) with the two non-uniform causes; "abbreviation" → **"definitionally equal"**; the three `d-files-*.md` in `5ad9ec3c` disclosed; `dup-hom`'s two module moves and the `LinearSphereAction` block re-attributed; the **six inert `dfiles-a` map lines** (85 effective renames); §2's "one line each"; the second `fc6b6ffe` cross-branch fix; `fibre_constant_of_ker_le` |
| `3b894884` | `reviews/INTEGRATION-7.md` | packet 01 cell **"314 source of 407"**; packet 03 cell **"0 widened; forced count inconsistent in the receipt, 106 by its rows"**; seven further cells corrected from the per-file tables; **"one commit per file" qualified** (packets 01 and 03); **260 commits + 10 merges**; the merged-head `PASS` row rewritten as necessary-not-sufficient with the mitigation done; `Contragredient.lean` no longer called a true Mathlib duplicate; the attribution note turned the right way round; a dated §5 |
| `66b23dba` | `reviews/INTEGRATION-8.md` | **"MinimalSystem deleted" → moved**; the **127 breakdown corrected** (residue 99, by module, two non-uniform causes); pins 271 → 280 and the `ULift ℤ` protocol obstruction; monolith 1,810; rename map 85 effective; `dfiles-c`'s instance cause and the **unprobed** `SphereTwo` theorems (not an owner decision) with the `w4-w1-solution` reroute; §3's invisible-pin note; a dated §5 listing the dropped "left" items |

## Findings left, with reasons

* **Every `[docstring]`, `[citation]`, `[unsound]`-adjacent and code-level finding.**  They belong to
  the per-packet fix agents (`Lib/reviews/REVIEW-7-8.md` §3, "Code and docstrings"); this seat edits
  no Lean file.  Each is named in the corrections section of the receipt it was raised against, so a
  reader of a receipt sees what is outstanding and who owns it.
* **The three disputed counts** (packet 01 binders, packet 03 binders, packet 09 binders): recorded
  as disagreements, not adjudicated, because no receipt states its counting rule.  Packet 03's "99"
  is withdrawn outright, since it matches neither the receipt's own rows nor any independent count.
* **The missing per-packet `envdiff.json` files** (packets 01–10).  They cannot be produced now: the
  worktrees and dumps are gone and the tool would have to be re-run against a base that no longer
  exists in a built form.  Each affected receipt now states plainly which of its envdiff claims are
  unverifiable from the tree, and the standing rule (`REVIEW-7-8.md` §4) is that every receipt
  commits its `envdiff.json`/`.txt` beside itself.
* **`NEXT_STEPS.md`** is outside this seat's list; the "left" items the reviewers found dropped are
  recorded in `INTEGRATION-8.md` §5 instead, where they are in scope.
* **Commit messages that carry a wrong figure** (`835b39be` "118 / 217", `1a7358c0` "40 blocked",
  `ab98de39` "9 docstrings", `6b1c40f1`'s subject) are left as they stand — history is not rewritten
  — and each is named in the corresponding receipt's corrections section.

## Builds

None.  No Lean file was edited, so per the shared rules no `lake build`, no environment dump and no
`rename.txt` applies to this branch.
