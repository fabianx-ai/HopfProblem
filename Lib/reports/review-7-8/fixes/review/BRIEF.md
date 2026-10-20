# Fresh-reviewer brief — the fix round after the round-7/8 reviewer pass

You are an independent reviewer with no prior context. Eleven "fixer" agents (Opus 5) were given
the findings of twenty-one earlier reviews and told to fix them. Your job is to check ONE SLICE of
that fix round: whether the fixes are SOUND (no statement weakened, every deletion has a genuine
twin, universe lifts preserve the `u = 0` statement), whether the receipts the fixers wrote are TRUE
and COMPLETE, and whether the fixers stayed inside the rules they were given. You are not here to
redo the work or to be polite. A receipt sentence is verified by looking, not by trusting it.

## Where things are (all READ-ONLY for you)

* Source tree, all branches, history: `/home/goblin/hopf-lib-audit` (branch `lib/textbook-extraction`,
  head `8da46f0d`). Use it for `git log/diff/show` and reading files. NEVER edit, commit, checkout,
  reset, stash, or create branches there.
* A fully built copy of the same head: `/home/goblin/hopf-lib-integration` (`8da46f0d`; the oleans
  are of `9a6e125a`, the same Lean sources). You may elaborate a scratch file there with
  `cd /home/goblin/hopf-lib-integration && /home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env lean <absolute path to .lean>`.
  A scratch file may `import Lib.Foo.Bar` / `import Hopf.Proof.Foo` and use `#check`, `#print`,
  `#print axioms`, `set_option pp.universes true`, `example`. Keep scratch files under
  `/home/goblin/.claude/jobs/06995e68/tmp/review-fix/<your-slice>/` (create it). NEVER run
  `lake build` there, never edit files there, never run `lean-agent-ide dump`. At most one `lean`
  process at a time and at most ~10 elaborations in total (three reviewers share the machine).
* Do not use `/tmp`. Do not push anything. Do not touch `/home/goblin/hopf` or any other directory.
* Toolchain Lean v4.33.0 with matching Mathlib. `autoImplicit` is ON in 221 of the 446 `Lib` files
  (no `leanOptions` in `lakefile.toml`); keep that in mind when a binder looks "free".

## The round

Base `62d45257` (`lib/integration` after the reviewer pass). Each fixer worked on branch `fix/<name>`;
all eleven were merged `--no-ff` into `lib/integration` (merges listed in
`Lib/reports/review-7-8/fixes/MERGE.md`, which is the coordinator's merge receipt); the docs commit on
top is `8da46f0d`. A branch's commits: `git log --format='%h %s%n%b' 62d45257..fix/<name>`; its whole
diff: `git diff 62d45257 fix/<name>`. The after-state to compare against is the head `8da46f0d`
(later branches may have touched the same file; say so when it matters).

The rules the fixers were given are reproduced at the end of this brief (section "Fixer rules").
The findings they were closing are in `Lib/reports/review-7-8/<review>.md` (the 21 reviews) and the
fix list `Lib/reviews/REVIEW-7-8.md` §3. Each fixer's own receipt is
`Lib/reports/review-7-8/fixes/<name>.md`. The coordinator's summary of the round is
`Lib/reviews/REVIEW-7-8.md` §5 and `NEXT_STEPS.md` (first paragraph).

Protocol the fixes must obey: a deleted declaration needs a named surviving twin whose statement is
the same or stronger (same proposition, or the deleted one is an instance of it); a rename must be
in `fixes/rename.txt` as `<new name> <old name>`; a universe lift (`.{0}` → `.{u}`, `Type` → `Type*`)
must keep the `u = 0` statement literally the old one and add no hypothesis; a docstring must state
exactly the hypotheses and conclusion of its declaration; a citation must be a textbook item the
fixer was sure of, otherwise a section reference; `Lib` never imports `Hopf`; no `sorry`/`axiom`;
one commit per fix item with trailers `Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>` and
`Claude-Session: https://claude.ai/code/session_01VZt4JDgce67x5QTThwQ3E2`; no edits under
`Lib/reports/` or `Lib/reviews/` except by `fix/receipts` and each fixer's own receipt file.

The round-level environment diff is `Lib/reports/review-7-8/fixes/envdiff.{json,txt}` (base dump of
`62d45257`, after dump of `9a6e125a` under `rename.txt`). Its verdict is FAIL by construction (there
are deletions); `MERGE.md` claims to reconcile it: 5 lost source names, 3 added, 38 changed types all
`PROOF-NAMING`. Note: the tool's `PROOF-NAMING` class only means the set of `Lib`-internal constants
the type mentions is unchanged; it is necessary, not sufficient, for "statement preserved". You
verify statement preservation by reading the two statements.

## Slices

### Slice A — code: universe lifts and binder widenings
Branches `fix/p02` (`Coproduct.lean` made polymorphic via
`CategoryTheory.Abelian.hasFiniteBiproducts`; twelve coefficient pins lifted in
`Lib/AlgebraicTopology/SingularCochains/PositivePrimitives.lean` and `Vanishing.lean`),
`fix/p0304` (six `AdaptedWindows.lean` binders → `Type*`, plus docstrings/citations),
`fix/p10` (two private lemmas in `Lib/Topology/Sheaves/SingularCochainSheaf/PrimitivesH1.lean`
lifted, plus docstrings). Receipts `fixes/p02.md`, `fixes/p0304.md`, `fixes/p10.md`.
Check exhaustively (38 changed types): for EVERY changed declaration, the base statement
(`git show 62d45257:<path>`) against the head statement; the `u = 0` instance must be literally the
old statement, no hypothesis added, no instance argument changed, no `Type` → `Type u` that moved a
downstream declaration to another universe without the receipt saying so. Probe at least five of
them with `#check` under `set_option pp.universes true` at the head to see the real universe
parameters (an "invisible" universe-0 pin can survive a textual lift when an instance argument is
resolved at a universe metavariable). Test the receipts' claims: "proofs unchanged", "12 not 3",
"none of the six binders was forced", "`hasFiniteBiproducts` route needs no new hypothesis". Check
the 38 rows of `envdiff.json` match the receipts' lists exactly (18 + 12 + 6 + 2). Check the count
`293 → 269` of `.{0}` pins (`grep -o '\.{0}' -r Lib --include=*.lean | wc -l` at base and head, or
whatever definition MERGE.md implies; say which). Hygiene over the three branch diffs (§9 below).

### Slice B — structure: deletions, re-additions, moves, probes
Branches `fix/names-dfiles` (new `Lib/GroupTheory/FreeGroup/Invariant.lean` with
`FreeGroup.forall_apply_eq_self_iff` restating the round-8-deleted `freeGroup_invariant_iff`; new
`Lib/Algebra/Group/Ker.lean` with `MonoidHom.apply_eq_apply_of_ker_le` re-adding
`fibre_constant_of_ker_le`; the docstring cause in `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean`;
new `Hopf/Proof/AxiomAudit.lean` probing the four `TopCat.Sheaf.*_sphereTwo` theorems that were moved
to `Hopf/Proof`), `fix/moved` (duplicate imports removed; `LinearEquiv.coordMatrix_eq_toMatrix` added;
`Fin.tailHeadAddEquiv` deleted for its `rfl` twin; two renames; seven docstrings), `fix/dup-dfa` (four
`SingularSmallChains.*_one` lemmas deleted for their `_succ` twins; `RadialFilling` documented;
docstrings). Receipts `fixes/names-dfiles.md`, `fixes/moved.md`, `fixes/dup-dfa.md`, and
`fixes/rename.txt` (3 lines).
Check exhaustively: (1) for each of the 5 deletions, the deleted statement (from `git show
62d45257:<path>`) and the twin at head, side by side; is the twin the same or stronger? For the
`_one` lemmas: is the `_one` case really an instance of `_succ` at `n = 0`, including the exact form
of the index (`0 + 1` vs `1`, `Fin`/`ℕ` coercions)? For `Fin.tailHeadAddEquiv`: is the claimed twin
definitionally equal AS A FUNCTION (both directions), not just as a type? (2) For the two re-added
lemmas: find the ORIGINAL statements that round 8 deleted (`git log -S freeGroup_invariant_iff
--all`, `git log -S fibre_constant_of_ker_le --all`, then `git show <commit>^:<path>`) and compare
with the re-added ones: same or stronger, and are they placed in a sensible module? (3) Consumers:
every use of a deleted or renamed name in `Lib Hopf Solution.lean S6.lean S6Shortcuts.lean
Challenge.lean Lib/AxiomAudit.lean` rerouted (grep the head for the old names). (4) `rename.txt`
direction is `<new> <old>`, entries complete (compare with the `envdiff.txt` moves/lost/added), new
names present at head, old absent. (5) `Hopf/Proof/AxiomAudit.lean`: does it probe exactly the four
moved theorems, is it reachable by some build target (which? is it in any `lakefile.toml` lib's
globs or imported by anything?), and do its `#print axioms` outputs really show only
propext/Classical.choice/Quot.sound (elaborate it yourself). (6) The `AddCommGroup.lean` docstring
cause: it says the instance is load-bearing because `TopCat.Sheaf` is a non-reducible Mathlib `def`;
test the claim (e.g. `#check`/`example` that instance search fails without it, or read Mathlib's
definition). (7) No `import Hopf` under `Lib/`; new modules in `Lib.lean` with module docstrings.
(8) Duplicate imports: which were removed, and are the three MERGE.md says remain really still
there? Hygiene (§9) over the three branch diffs.

### Slice C — prose: docstrings, citations, receipt corrections, coordinator summary
Branches `fix/p01`, `fix/p09`, `fix/p0708`, `fix/p0506` (docstrings, citations, manuscript labels),
`fix/receipts` (22 receipt/review files given dated correction sections). Receipts `fixes/p01.md`,
`fixes/p09.md`, `fixes/p0708.md`, `fixes/p0506.md`, `fixes/receipts.md`. Also the coordinator's
`fixes/MERGE.md`, `Lib/reviews/REVIEW-7-8.md` §5 and the first paragraph of `NEXT_STEPS.md`.
Check: (1) sample at least 25 docstrings changed across the four code branches (say which) against
the declaration each documents — wrong hypothesis, wrong direction, wrong object, invented theorem
name is a FINDING; the fixers were correcting wrong docstrings, so check the correction is right,
not just different. (2) Sample at least 15 changed citations; is the cited item (Hatcher, Bredon,
Bott–Tu, Weibel, Godement, Hartshorne, Kashiwara–Schapira, Brown, Bourbaki, Milnor, Cartan–Eilenberg,
Iversen, ...) really the stated result, and where the fixer demoted to a section reference, is the
section right? Say when you are not sure. (3) The two "reviewer corrected" claims in REVIEW-7-8 §5:
packet 09's fixer says `j_! ⊣ j^*` is the adjunction giving limit preservation (and `j^* ⊣ j_*`
colimits) — check the mathematics and the docstring as written at head; packet 02's "12 not 3" is
Slice A's, but check §5 and `fixes/MERGE.md` report it consistently with `fixes/p02.md`. (4)
`fix/receipts`: for each of the 22 files, does the correction section state the original claim, the
corrected fact, and the source of the correction (which review finding)? Does it mark as
"unverifiable" exactly the claims that depend on the lost per-packet envdiffs, and not use that as
cover for claims that ARE checkable from git? Did it alter the original text silently anywhere
(`git diff 62d45257 fix/receipts -- <file>` shows only additions? If not, why)? (5) Manuscript
labels: the fixers claim `(C8)/(C13)/(C14)/(C24)/(C28)/(C30)` and other labels gone from their
files; grep the head for `\bC[0-9]+[a-z]?\b`, `M[0-9]+`, `textbook`, `Textbook`, `manuscript` under
`Lib/` and compare with what MERGE.md "Left" admits (66 hits in 27 files for textbook; ~15 in
`Cech/DerivedGlobalSections.lean`). Anything left that the receipts do not admit is `[incomplete]`.
(6) `MERGE.md` numbers: 103 non-merge commits, 129 files, +4,080/−518 (`git diff --shortstat
62d45257 9a6e125a`, `git rev-list --count --no-merges 62d45257..9a6e125a`), merge hashes and order,
the check results as far as they are recorded in the receipts (do not rebuild). (7) Is MERGE.md
"Left" the union of the "left" items in the eleven receipts? Anything a receipt left that MERGE.md
dropped is `[incomplete]`. (8) Commit hygiene: one commit per fix item, subject `Lib/<path>: ...`,
body naming the finding closed, both trailers, across the five branches (count violations).

## 9. Hygiene (every slice, for its branches)
`sorry`, `axiom`, `admit`, `set_option maxHeartbeats` increases, `unsafe`, `native_decide`, `@[simp]`
added/removed, `noncomputable` added, `private` removed, `import Hopf` under `Lib/`, edits under
`Lib/reports/`/`Lib/reviews/` by a branch other than `fix/receipts` beyond its own receipt file,
edits to `TEXTBOOK.md`/`DECOMPOSITION.md`/`CORRESPONDENCE.md`, missing trailers.

## Output

Write your review to `/home/goblin/.claude/jobs/06995e68/tmp/review-fix/<slice>.md` where `<slice>` is
`A-code`, `B-structure` or `C-prose` (Markdown, at most ~350 lines) with exactly these sections:

1. `# Review of fix round — slice <X>` then one line **Verdict: ACCEPT / ACCEPT WITH FINDINGS /
   REJECT** and one sentence why.
2. `## Findings` — numbered, most serious first. Each: what is wrong, where (file:line, commit,
   declaration), the evidence (paste both statements for a wrong twin or a changed statement; the
   docstring and the statement for a wrong docstring), what should happen. Severity tags:
   `[unsound]` (statement weakened / hypothesis added / twin not equivalent / proof claim wrong),
   `[wrong receipt]`, `[incomplete]`, `[docstring]`, `[citation]`, `[rule]` (fixer broke a rule it
   was given), `[nit]`.
3. `## Claims checked` — table: claim | verified / partly / refuted | how.
4. `## Not checked` — and why.
5. `## Tool notes` — what would have made this easier or the receipts more trustworthy.

Return the same content as your final message. Do not soften. If after real checking nothing is
wrong, say so and list the coverage.

## Fixer rules (what the eleven agents were told; verbatim)
## Rules (strict, shared by every fix-round agent, 2026-09-21)

You are fixing findings from an independent review pass. Source of truth for what to fix: the review
file(s) named in your assignment under `Lib/reports/review-7-8/<id>.md` (read them in full) and the
fix list in `Lib/reviews/REVIEW-7-8.md` §3. The receipt the review checked is under
`Lib/reports/round-7/…` or `Lib/reports/round-8/…`. Do the fixes; do not re-review, do not widen scope.

- Worktree `/home/goblin/hopf-fix-NAME` (branch `fix/NAME`, base `62d45257` = `lib/integration`, Lean
  v4.33.0, Mathlib v4.33.0); `.lake` seeded with a full build of the base (wait for `.lake/SEEDED` to
  exist before any lake command). Work only there. Scratch `/home/goblin/.claude/jobs/06995e68/tmp/fix-NAME/`
  (create it; never `/tmp`). Never touch `/home/goblin/hopf`, other worktrees, or other branches.
- Never `sorry`, `axiom`, `admit`; never weaken a statement; never add a hypothesis to an existing
  statement. Universe generalisations must keep the `u = 0` instance literally the old statement. A
  deletion needs a surviving twin with the same or stronger statement named in the commit body; a
  rename goes into `$S/rename.txt` as `<new name> <old name>` (after→base, the direction the tool needs).
- Docstring fixes: the docstring must describe exactly the hypotheses and conclusion of the declaration
  (list them first, then write). Citation fixes: cite only a textbook item you are sure of; otherwise
  cite the section ("§2.4") or write "cf." — never invent an item number. A citation you cannot verify
  is left as a section reference, and the commit body says so.
- Every consumer of anything you touch (grep `Lib Hopf Solution.lean S6.lean S6Shortcuts.lean
  Challenge.lean`, and `Lib/AxiomAudit.lean`) is updated. `Lib` never imports `Hopf`. A new module goes
  into `Lib.lean` (or, under `Hopf/Proof`, is imported by its consumer) and has a module docstring.
- Build: `lake build <Module>` per edited Lean module in the foreground (10-minute timeout). For
  docstring-only edits one `lake build <Module>` per file is enough. If you changed a statement, a
  universe, a name, or deleted anything: at the end `lake build Lib`, `lake build Solution S6Shortcuts
  S6 Challenge`, `lake build Lib.AxiomAudit` (only propext / Classical.choice / Quot.sound; no sorryAx)
  and `python3 scripts/lib_stock_census.py --check`, under nohup and polled: `for i in $(seq 1 58); do
  grep -q '^done' log && break; sleep 10; done`, one Bash call at a time, 10-minute timeout per call;
  scripts echo `done <exit>`. Then the environment diff: `lake env
  /home/goblin/lean-agent-ide/.lake/build/bin/lean-agent-ide dump Solution Lib --modules Hopf,Lib`
  before your first edit to `$S/dump_base.jsonl` (several minutes; nohup and poll) and after the last
  (with `--rename $S/rename.txt` if you renamed) to `$S/dump_after.jsonl`, then `python3
  /home/goblin/lean-agent-ide/tools/envdiff.py $S/dump_base.jsonl $S/dump_after.jsonl --receipt
  $S/envdiff.json > $S/envdiff.txt`; every lost source name and every changed type must be explained in
  your receipt. Docstring-only agents skip the dump.
- Lake `/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake` with `GIT_CONFIG_COUNT=1
  GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'`, from the worktree root. Never kill by
  command-line pattern; use the exact pid you started. Never push.
- Commits: one per fix item (one file's docstrings, one citation set, one lift, one deletion), subject
  `Lib/<path>: <what>` (or `Hopf/Proof/<path>: …`), body naming the review finding number it closes
  (e.g. "closes r7-packet-09 finding 1") and any declaration touched, trailers
  `Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>` and
  `Claude-Session: https://claude.ai/code/session_01VZt4JDgce67x5QTThwQ3E2`.
- Do NOT edit any file under `Lib/reports/` or `Lib/reviews/` unless your assignment says so (one agent
  owns all receipt corrections). Your own receipt goes to `Lib/reports/review-7-8/fixes/NAME.md`
  (create the directory): per finding, what was done or why not, the build lines, the envdiff summary if
  any, the commits; commit it last.
- Budget: if it will not fit, stop cleanly at a green commit and list what is left.
- Report: findings closed / left with reasons, build lines, envdiff summary if any, commit range.
  Nothing else.
