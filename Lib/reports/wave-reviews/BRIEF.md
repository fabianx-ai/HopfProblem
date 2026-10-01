# Fresh-reviewer brief — the monolith waves (2026-10-01)

You are an independent reviewer with no prior context. Twenty-two agents split 24 oversized Lean 4 files
of a library (`Lib/`) into 290 topic modules. Your job is to check ONE SLICE of that work: whether it is
SOUND (nothing weakened, nothing lost, moves really verbatim, moves out of the library really safe),
whether the receipts are TRUE and COMPLETE, and whether the prose the agents wrote (docstrings) is RIGHT.
You do not redo the work and you are not polite. A receipt sentence is verified by looking.

## Where things are (all READ-ONLY for you)
* Source tree and history: `/home/goblin/hopf-lib-audit` (branch `lib/textbook-extraction`, head `8ff8d81e`).
  `git log/diff/show` and reading only. NEVER edit, commit, checkout, reset, stash, or branch there.
* A fully built copy of the same head: `/home/goblin/hopf-lib-integration`. You may elaborate a scratch
  file there: `cd /home/goblin/hopf-lib-integration && /home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env lean <absolute path>`.
  Scratch files may `import Lib.…`/`import Hopf.Proof.…` and use `#check`, `#print`, `#print axioms`,
  `set_option pp.universes true`, `example`. Keep them under
  `/home/goblin/.claude/jobs/06995e68/tmp/review-waves/<slice>/`. NEVER run `lake build`, never edit files
  there, never run `lean-agent-ide dump`. One `lean` process at a time, at most ~10 elaborations.
* Never use `/tmp`. Never push. Touch nothing else. Another agent is working in `/home/goblin/hopf-int7`;
  leave it alone.
* Dumps you may read (declaration tables: name, module, kind, range, type hashes, `uses`): wave-1 base
  `/home/goblin/.claude/jobs/06995e68/tmp/wave1/dump_head.jsonl` (head `e669bc93`), wave-2 base
  `/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl` (head `8eba3d72`), final
  `/home/goblin/.claude/jobs/06995e68/tmp/wave2/final/dump_head3.jsonl` (head `63337fee`, same Lean sources
  as `8ff8d81e`). `uses` lists only constants of `Hopf`/`Lib` modules, is raw (a use of `X._proof_1` is not
  a use of `X`), and misses names used only inside `simp only […]` sets that were eliminated.

## The work
Wave 1: base `e669bc93`, ten branches `wave1/*`, coordinator receipt `Lib/reports/wave-1/MERGE.md`, rules
`Lib/reports/wave-1/RULES.md`, per-agent receipts `Lib/reports/wave-1/<name>.md` + `<name>/`.
Wave 2: base `3760f829`, twelve branches `wave2/*`, `Lib/reports/wave-2/MERGE.md`, `RULES.md`, receipts
likewise. Every branch was merged `--no-ff`; its commits are `git log --format='%h %s%n%b' <base>..<branch>`
and its diff `git diff <base> <branch>`. The judgement the agents worked from:
`Lib/reports/round-7/judgement/monoliths.md`.
Protocol: each monolith `X.lean` becomes a facade (imports + docstring only) over pieces; every declaration
is moved VERBATIM by a tool (`split_module.py`, per-piece JSON receipts with SHA-256); nothing deleted; no
statement changed; project-specific declarations may move from `Lib` to `Hopf/Proof` ONLY if no `Lib` module
uses them directly or transitively (`Lib` never imports `Hopf`); renames go into `rename.txt` as
`<new> <old>` with every consumer updated; universe lifts keep the `u = 0` statement literally; docstrings
must state exactly the hypotheses and conclusion; citations only when sure; one commit per step with
trailers. The tool `envdiff` compares declaration tables before/after: lost/added/changed-type names, module
moves; its class `PROOF-NAMING` (type hash changed but the set of library constants mentioned is unchanged)
is necessary, not sufficient, for "statement unchanged" — you verify by reading both statements.

## Slices

### Slice W1 — wave 1
Check, most important first:
1. **The 39 moves out of `Lib`** (`wave1/morse-d`: `Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/…`,
   `…/SurgeryCollapse/…`, 35 declarations; `wave1/rearrangement`: `…/Rearrangement/{SheetArc,MiddleLevel}`, 4).
   For each moved module: is it true at the head that nothing under `Lib/` mentions any moved name
   (`git grep` each name; and the dump's `uses`)? Are the moved statements verbatim (compare with
   `git show <base>:<old path>`)? Are the `Hopf` consumers' imports right? Were `Lib/AxiomAudit.lean` probes
   of moved names carried to `Hopf/Proof/AxiomAudit.lean` or dropped (compare probe lists at base and head:
   is any theorem that was probed at the base now probed nowhere)?
2. **Verbatimness, independently of the tool**: for THREE monoliths of your choice (at least one of
   `SurgeryCollapse`, `PrismOperator`), reconstruct the multiset of declaration blocks at the base and at the
   head (the pieces + `Hopf/Proof` modules) and diff them modulo the recorded renames and added docstrings.
   Any declaration whose statement or proof text differs beyond that is a FINDING with both texts.
3. **Renames** (`wave-1/rename_all.txt`, 139 lines: prism 20, cross 115, rearrangement 4): direction, every
   new name present at head, every old name absent from `Lib Hopf Solution.lean S6.lean S6Shortcuts.lean
   Challenge.lean`; are the new names sensible Mathlib-style names (e.g. is `PeriodTorusHigherHomology.*` →
   `SingularHomology.*` creating a clash or a misleading name; are the four `Real.smoothTransition.*`/
   `expNegInvGlue.hasDerivAt` names not already Mathlib constants — check with `#check`)?
4. **The 11 lifts** (prism 10, residue's `dualHomotopyEquiv`): `u = 0` statement literally the old one
   (elaborate an `example`), no hypothesis added, real universe parameter (`pp.universes`).
5. **Docstrings**: `wave1/morse-d` added 281. Sample at least 40 across its 25 pieces against the
   declarations (list hypotheses and conclusion, then read the docstring): wrong hypothesis, wrong direction,
   wrong object, invented theorem name, or a citation you believe wrong is a FINDING. Also the module
   docstrings of ten pieces across other branches: do they describe what the file contains?
6. **Facades**: the eleven wave-1 facades contain no declaration and import every piece; `Lib.lean` unchanged.
7. **Receipt claims**: counts in `wave-1/MERGE.md` against git (commits, modules, declarations moved,
   pieces per branch), the 34 `PROOF-NAMING` reconciliation (read the 6 `SingularMayerVietoris.*` statements
   at base and head), "Left" lists reproducible.
8. **Residue branch** (`wave1/residue`): the receipt corrections it made in `Lib/reports/review-7-8/fixes/*.md`
   and `RECEIPT-08.md` quote the original text; the 48 swept docstrings still say something true; the
   Godement demotion.

### Slice W2 — wave 2
Check, most important first:
1. **Visibility widening in `CubeBoundaryThreeCells`** (`wave2/cube3`, commit `099a566a`): 34 declarations
   gained `public`, 11 gained `@[expose]`. Was each one necessary (used by another piece)? The receipt says
   three are public only because DEAD lemmas use them — verify, and verify the "36 dead private lemmas" claim
   (`cube3/notneed.txt`): for each, no use anywhere in `Lib Hopf Solution.lean …` (grep and dump). Did the
   `@[expose]` change what downstream `Lib` modules (`Bricks`, `CubeBoundaryThreeDimension`) can unfold in a
   way that could change their proofs' meaning? Did commit `190d287c` (94 comments → docstrings) change only
   comment delimiters?
2. **The 43 moves out of `Lib`** (`wave2/riemann`, `Hopf/Proof/Analysis/Complex/RiemannMapping/{SectorRoots,
   TriangleNormalization}`): nothing under `Lib/` mentions a moved name; statements verbatim; consumer import;
   probes carried. And the receipt's two deviations from the judgement: are the `logHalfStrip`/
   `onePointDomain`/`halfStripExp` lemmas really general (read them); is `RectanglePrimitive` really absent
   from Mathlib (look in `.lake/packages/mathlib/Mathlib/Analysis/Complex/` for primitives on rectangles /
   `HasPrimitives`)?
3. **Rewritten docstrings**: 322 across six branches in comment-only commits (`riemann` `4398ed1c` 85,
   `windows` 44, `height` `2f5ee556` 47, `existence` `86fde3fb` 9, `cubic` `ab6ac93e` 85, `cube3` `9e1e83b5`
   19, plus field docstrings in `windows`, `existence`, `cleanstrips`). First confirm each such commit is
   comment-only (strip comments, diff). Then sample at least 60 rewritten docstrings (at least 8 per branch)
   against the declarations: is the NEW text exactly the hypotheses and conclusion? A rewrite that is wrong,
   drops a hypothesis, or states more than the theorem proves is a FINDING with both texts and the statement.
   The agents claim 18 old docstrings were factually wrong (e.g. `blend_small`/`blend_large` swapped in
   `windows`): check five of those claims.
4. **Verbatimness, independently of the tool**: for THREE monoliths of your choice (at least one of
   `MorseLemma`, `EmbeddedArcs`), reconstruct the multiset of declaration blocks at base and head and diff
   modulo renames, docstring edits and (for cube3) visibility modifiers.
5. **Renames** (`wave-2/rename_all.txt`, 17 lines): direction, presence/absence, and that the five
   `Real.*tanh*`/`Real.contDiffAt_artanh` names do not collide with Mathlib (`#check` them without importing
   `Lib`: if Mathlib already has `Real.hasDerivAt_tanh` etc., the rename created a duplicate or a clash —
   say which, and compare statements).
6. **The 37 `PROOF-NAMING` changed types** (2 `DiskFraming.*`, 35 `SmoothMorseLemma.*`): read at least 10 at
   base and head; are the statements textually identical?
7. **Facades** (13) and `Transversality/Basic.lean` (pieces beside it, no `Basic/` directory): no
   declarations; every piece imported.
8. **Receipt claims** in `wave-2/MERGE.md` against git (commits, pieces, the model per branch from commit
   trailers, the comparison table's token/tool numbers are not checkable — say so), and "Left" completeness.

## Hygiene (both slices, over the slice's branch diffs)
`sorry`, `axiom`, `admit`, `maxHeartbeats` increases, `unsafe`, `native_decide`, `@[simp]` added/removed,
`noncomputable` added, `private` removed (other than cube3's recorded ones), `import Hopf` under `Lib/`
(allow `public import`), edits under `Lib/reports/`/`Lib/reviews/` beyond a branch's own receipt (except
`wave1/residue`, which was assigned receipt corrections), edits to `TEXTBOOK.md`/`DECOMPOSITION.md`/
`CORRESPONDENCE.md`/`Lib.lean`, missing trailers.

## Output
Write `/home/goblin/.claude/jobs/06995e68/tmp/review-waves/<slice>.md` (`W1` or `W2`; Markdown, at most
~350 lines) with exactly: (1) `# Review of the monolith wave — slice <X>` and one line **Verdict: ACCEPT /
ACCEPT WITH FINDINGS / REJECT** with one sentence why; (2) `## Findings`, numbered, most serious first, each
with where (file:line, commit, declaration), the evidence (both texts), what should happen, and a tag:
`[unsound]`, `[wrong receipt]`, `[incomplete]`, `[docstring]`, `[citation]`, `[rule]`, `[api]` (visibility,
naming clash, duplicate of Mathlib), `[nit]`; (3) `## Claims checked` table: claim | verified / partly /
refuted | how; (4) `## Not checked` and why; (5) `## Tool notes`. Keep a `PROGRESS.md` beside your scratch
files, rewritten after each numbered check (Done / In progress / Next), so a successor can continue if you
are cut off. Return the same content as your final message. Do not soften. If nothing is wrong after real
checking, say so and show the coverage.
