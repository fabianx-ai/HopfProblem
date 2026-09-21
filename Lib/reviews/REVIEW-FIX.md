# Review of the fix round (three Fable reviewers, 2026-09-21)

The fix round (`REVIEW-7-8.md` §5; eleven Opus 5 agents; merge receipt `Lib/reports/review-7-8/fixes/MERGE.md`)
was checked by three fresh Fable reviewers, one per slice, with the brief
`Lib/reports/review-7-8/fixes/review/BRIEF.md`. Reviews: `review/A-code.md`, `review/B-structure.md`,
`review/C-prose.md`. Head reviewed: `8da46f0d`. All three worked read-only against the built copy; A ran three
elaborations, B two, C none (its four code branches are comment-only, verified line by line).

## 1. Verdicts

| slice | branches | verdict | unsound | rule broken | findings |
|---|---|---|---|---|---|
| A code | `fix/p02`, `fix/p0304`, `fix/p10` | ACCEPT WITH FINDINGS | 0 | 0 | 6 (3 wrong receipt, 1 incomplete, 2 nit) |
| B structure | `fix/names-dfiles`, `fix/moved`, `fix/dup-dfa` | ACCEPT WITH FINDINGS | 0 | 0 | 4 (all nit) |
| C prose | `fix/p01`, `fix/p09`, `fix/p0708`, `fix/p0506`, `fix/receipts` + coordinator docs | ACCEPT WITH FINDINGS | 0 | 0 | 8 (2 wrong receipt, 2 incomplete, 1 docstring, 3 nit) |

What was verified positively, exhaustively where the list was finite:

- **All 28 lifted or widened statements** are literally the base statements at `u = 0`, token by token against
  `62d45257` and by `example` at the head; no hypothesis or instance argument changed; the lifts are real
  (`.{1}` instances elaborate); `pp.universes` on the 10 downstream `Coproduct.sigma*` declarations shows every
  universe still `0` (only a Prop-valued `HasBiproduct` proof term changed). The 38 `envdiff.json` rows are
  exactly 18 + 12 + 6 + 2. Pins 293 → 269 reproduced (`git grep -o '\.{0}' -- 'Lib/**/*.lean'`).
- **All five deletions** have twins confirmed by elaboration: the four `SingularSmallChains.*_one` lemmas close
  by the bare `_succ` twin term at `n = 0` (base statements verbatim); `Fin.tailHeadAddEquiv` is `rfl`-equal to
  the Mathlib composite as a bundled `≃+`, pointwise, and in both directions. The two re-added lemmas are the
  round-8-deleted statements verbatim (diff = name and `_root_.`). Consumers rerouted (0 hits for 13 old names);
  `rename.txt` direction and completeness right; no `import Hopf` under `Lib/`; exactly the three admitted
  duplicate imports remain; the `AddCommGroup.lean` cause reproduces (instance search fails on
  `TopCat.Sheaf`-typed `F`, succeeds with `local reducible`).
- **27 corrected docstrings** sampled across the four prose branches, all right against their declarations;
  **18 changed citations** judged: 15 right, 3 unsure (Kashiwara–Schapira §2.3, Iversen III, Godement II.5.10),
  0 wrong at head. The adjunction correction in §5 is confirmed against Mathlib (`sheafAdjunctionContinuous`
  is `j_! ⊣ j^*`, `sheafAdjunctionCocontinuous` is `j^* ⊣ j_*`). `fix/receipts`: 22 files, every correction
  section quotes the original claim, the corrected fact and the source finding; the 60 in-place edits all carry
  the original figure; "unverifiable" is used only for the lost per-packet envdiff outputs.
- MERGE.md numbers reproduce (103 non-merge commits, 129 files, +4,080/−518, eleven merges in the stated
  order). Commit hygiene: 103/103 commits carry both trailers, subjects `Lib/<path>: …` (one exception, a
  three-file import commit), bodies name the finding; no `sorry`/`axiom`/`maxHeartbeats`/`@[simp]`/
  `noncomputable`/`private` change; no branch touched `Lib/reports/`/`Lib/reviews/` beyond its own receipt.

## 2. Findings that matter (all receipt or coordinator text; nothing in `Lib` is wrong)

1. **MERGE.md "Left" was assembled from receipt text, not from the head** (C1, C3, C4, A4): it listed a Weibel
   item `fix/p01` had already fixed, dropped `p10`'s Bredon III Thm. 1.1 residue in `GlobalUnitPredicates.lean`,
   omitted the `M`/`C29x` labels in two further files, and omitted the pins the code receipts left. Corrected
   in MERGE.md at this commit, each bullet now with its reproducing grep.
2. **Counts in coordinator text** (A3, B3, C6): "38 universe lifts" is 28 lifts + 10 unchanged-statement
   downstream rows; "3,302 probes" is 3,310 + 4 `#print axioms` lines at the head; MERGE.md rows 1 and 9
   undercount docstrings (5, 7). §5 and MERGE.md corrected at this commit.
3. **One refuted "forced" reason** (A1): `p02.md` says `dualHomotopyEquiv`'s `{K L : ChainComplex (ModuleCat.{0}
   ℤ) ℕ}` pin goes through `chains` and is "not local"; the declaration mentions no chains and a verbatim copy
   at `.{u}` elaborates. Leaving the pin is fine; the reason is the kind of claim the review round exists to
   remove.
4. **All three code receipts misread the envdiff lost/added rows** (A2) as `_proof_n` auxiliaries; they are
   the changed-type constants themselves (the tool lists a changed-type constant as lost and added). Nothing
   unsound follows; the prose is wrong in `p02.md`, `p0304.md`, `p10.md`.
5. **Hartshorne III Ex. 8.1** (C2): `p0708.md` and `RECEIPT-08.md` item 7 call it the sheafification
   description of `R^i f_*` (that is Prop. 8.1); Ex. 8.1 is the degenerate Leray statement, as `fix/p09` cites
   it. The head text is a permitted section reference, so `Lib` is right; the two receipts and the §3 list
   (which carried Ex. 8.1 with opposite arrows) are not. Recorded in §5 at this commit.
6. **One overstated docstring survives** (C5): `exists_clean_bigon_boundary_neighborhood`
   (`CleanStrips.lean:2781`) still says "meets the two sheets only there" although its conclusion, like the
   two the fixer corrected, constrains only the bigon side.
7. `Hopf/Proof/AxiomAudit.lean` and `Lib/AxiomAudit.lean` are reachable by no default target (B1): they are
   built only by an explicit module target. Consistent with convention; the receipts should say so.

## 3. Fix list (small; one Opus agent)

- `fixes/p02.md`: replace the `dualHomotopyEquiv` "not local" sentence by "left as out of scope; liftable
  (verbatim copy at `.{u}` elaborates)", or lift the pin (one token, private def, no outside consumer).
- `fixes/p02.md`, `fixes/p0304.md`, `fixes/p10.md`: rewrite the envdiff lost/added sentence (rows are the
  changed-type constants; only `dualHomotopyEquiv._proof_1/2`, `homologyBiproductEquiv._proof_1..5`,
  `sigmaChainComplexInverse._proof_1`, `sigmaChainInverseDegree.eq_1` are auxiliaries).
- `fixes/p0708.md` and `Lib/reports/round-7/packets/RECEIPT-08.md` item 7: Ex. 8.1 = Leray, Prop. 8.1 =
  sheafification description; optionally restore "III Ex. 8.1 (Leray)" in
  `FiniteClosedPushforward/AcyclicResolution.lean`.
- `Lib/Geometry/.../CleanStrips.lean:2781–2785`: one sentence, as in `af11d3a2`.
- `fixes/names-dfiles.md`: "reachable" → "by explicit module target only, not in `defaultTargets`".
- The residue bullets of MERGE.md "Left" (the sweep with the wider patterns, the three citation numbers, the
  three duplicate imports) — unchanged from before, now with greps.

## 4. Protocol changes adopted

- A "Left" list carries, per bullet, the grep or command that reproduces it at the merged head; it is built
  from the head, not from receipt text.
- Twin claims ship as `example`s in the receipt's branch (base statement verbatim, proved by the bare twin
  term) rather than as sentences; an `envdiff.py --accept-lost <name>=<twin>` that elaborates such an
  example is requested from the tool.
- "Left pinned, with the reason" attaches the elaboration that shows the pin forced, or says "untested".
- `envdiff.txt` needs a legend that lost/added include changed-type constants, and should print the full
  changed-type list (38 names is short); a per-citation table (`file:line | item | verified-by | confidence`)
  in citation receipts, so that two receipts cannot assert opposite confidence about one item unnoticed.
- The next label sweep uses `\bC[0-9]+[a-z]?\b`, `\bM[0-9]+`, `textbook lines`.
- Universe lifts and changed types are counted separately everywhere.
