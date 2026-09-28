# Monolith wave 1 — rules for every agent (2026-09-27)

You are splitting one (or two) oversized files of `Lib/`, a general-purpose Lean 4 / Mathlib library
extracted from a research formalisation (`Hopf/`, `Hopf/Proof/`, `Solution`). The judgement packet
`Lib/reports/round-7/judgement/monoliths.md` has an entry per file: verdict, textbook twin, findings
(line numbers at an older revision — re-locate by content), and a `suggestion:` line. Your assignment
names your file(s). Read the entry, then the whole file (statements at least; proofs where a cut runs
through them), then cut.

## Where you work
- Worktree `/home/goblin/hopf-w1-NAME`, branch `wave1/NAME`, base = `lib/integration` at `e669bc93`
  (Lean v4.33.0, Mathlib matching). Wait for `/home/goblin/hopf-w1-NAME/.lake/SEEDED` before any lake
  command (the build of the base is being copied in). Work only there. Scratch:
  `/home/goblin/.claude/jobs/06995e68/tmp/wave1/NAME/` (create it). Never `/tmp`. Never touch
  `/home/goblin/hopf`, other worktrees, other branches. Never push.
- Lake: `/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake` with
  `GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'`, from the worktree root,
  no `-j` flag (Lake 5.0.0 has none; default job count). Long commands under nohup, polled:
  `for i in $(seq 1 58); do grep -q '^done' log && break; sleep 10; done`, one Bash call at a time,
  10-minute timeout per call; scripts end with `echo "done $?"`. Never kill by command-line pattern;
  only the exact pid you started.
- The declaration table of the base: `/home/goblin/.claude/jobs/06995e68/tmp/wave1/dump_head.jsonl`
  (read-only; it is complete when `dump_head.err` ends with `done 0`; about ten minutes after you start).
  Same sources as your base, so its line ranges anchor `split_module.py`. It is also your envdiff base.
- Tooling (`/home/goblin/lean-agent-ide`, read `spec/split_module.md`, `spec/dump.md`,
  `spec/envdiff.md` first): `tools/split_module.py --dump D --module M --source F --stay NAMES
  --keep-out K --move-out V --receipt R [--keep-imports] [--move-imports] [--move-doc] [--expose]`
  moves a partition of one module's declarations into a second file verbatim (apply it repeatedly for
  several pieces; keep every receipt JSON in your scratch and copy them beside your receipt). Splitting
  by hand is allowed when the tool refuses (a unit on both sides): say so and how you checked verbatimness
  (e.g. `diff` of the concatenated declaration texts). `lake env
  /home/goblin/lean-agent-ide/.lake/build/bin/lean-agent-ide dump Solution Lib --modules Hopf,Lib` after
  your last edit (nohup; ~9 min, several GB) → `$S/dump_after.jsonl` (with `--rename $S/rename.txt` if you
  renamed; lines are `<new name> <old name>`), then `python3 /home/goblin/lean-agent-ide/tools/envdiff.py
  /home/goblin/.claude/jobs/06995e68/tmp/wave1/dump_head.jsonl $S/dump_after.jsonl --receipt
  $S/envdiff.json > $S/envdiff.txt`. Target: 0 lost, 0 added, 0 changed types, moves = your plan. Note
  the tool lists a changed-type constant as lost AND added; do not call those auxiliaries.

## What to do
1. **Cut by topic** along the auditors' list and your own reading. Every piece is a Mathlib-style module
   `Lib/<dir of the file>/<FileStem>/<Topic>.lean` (or a better existing home if a clearly matching
   module exists — say why) with a module docstring (`/-! # … -/`) stating the mathematics and the textbook
   result, not the history. Pieces import only what they need (start from the original import list and
   drop what `lake build` does not miss, if that is quick; otherwise keep the list and say so).
2. **The original module stays as a facade**: `Lib/<path>/<File>.lean` keeps its module docstring
   (rewritten: what the pieces are) and `import`s the pieces, nothing else. Consumers therefore need no
   change and `Lib.lean` is NOT edited. (Dissolving facades is a later, separate step.)
3. **Move to `Hopf/Proof` what is project material** (dimension-6 hypotheses, `Hemisphere.Sphere 2`,
   `mo1973`, index-2/3 machinery of the W4W1 argument, receipts-as-docstrings), as
   `Hopf/Proof/<same relative path>/<Topic>.lean`, BUT only a declaration that no `Lib` file uses,
   directly or transitively: `Lib` never imports `Hopf`. Decide with the dump's `uses` field over all `Lib`
   modules (a script over `dump_head.jsonl`: the set of constants of your module reachable backwards from
   any constant of another `Lib` module must stay), and confirm by `lake build Lib` at the end. Every `Hopf`
   consumer of a moved declaration gets `import Hopf.Proof.<…>` immediately after its existing
   `import Lib.<your module>` line (this keeps merges clean); `Lib/AxiomAudit.lean` probes of moved names
   move to `Hopf/Proof/AxiomAudit.lean`.
4. **Docstrings**: every non-private declaration that stays in `Lib` gets one if it lacks one. Method: list
   the binders, hypotheses and conclusion first, then write; state exactly them; no invented theorem names;
   cite a textbook item only if sure, else a section ("Milnor, h-cobordism §4") or "cf.". Declarations moved
   to `Hopf/Proof` need no new docstrings (a module docstring per moved file is enough).
5. **Names**: `mo1973`/`_mo1973_` names MUST be renamed (Mathlib style, describing the statement); record
   every rename in `$S/rename.txt` (`<new> <old>`) and update every consumer (`grep -rn` over `Lib Hopf
   Solution.lean S6.lean S6Shortcuts.lean Challenge.lean Lib/AxiomAudit.lean`). Other project vocabulary
   (`native*`, `Native*`, `nativeMorseIndex`, project namespaces) may be renamed when you are sure of a
   Mathlib-style name and the consumer edit is small; otherwise leave and list it in "Left".
6. **Universes**: `{E M : Type}` → `Type*` (or `.{0}` → `.{u}`) only where the proof is unchanged and the
   build passes; the `u = 0` statement must be literally the old one, no hypothesis added. List every such
   declaration in the receipt with a one-line `example` at `u = 0` proved by the lifted constant, checked in
   a scratch file you elaborate (`lake env lean scratch.lean`); envdiff will show them as changed types.
7. **Never**: `sorry`, `axiom`, `admit`; weaken a statement; add a hypothesis; delete a declaration (this
   wave deletes nothing — a duplicate you find goes into "Left" with the twin named); edit
   `TEXTBOOK.md`/`DECOMPOSITION.md`/`CORRESPONDENCE.md`, anything under `Lib/reports/` or `Lib/reviews/`
   except your own receipt, `NEXT_STEPS.md`, `Lib.lean`, or a monolith file that is not yours (list of
   monoliths = the `##` headings of `monoliths.md`; other agents are splitting them now). Drop
   `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … Modular UpperHalfPlane`, unused
   `universe`, and duplicate `import` lines from your pieces when the build passes without them.

## Checks before the receipt (all green, under nohup)
`lake build <every module you created or edited>`; `lake build Lib`; `lake build Solution
S6Shortcuts S6 Challenge`; `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit` (every axiom set ⊆
{propext, Classical.choice, Quot.sound}, no sorryAx); `python3 scripts/lib_stock_census.py --check`
(must print 123 / PASS — moving Lib → Hopf/Proof does not count, moving to `Hopf/` outside `Proof/` would);
`grep -rn '^import Hopf' Lib/` empty; dump + envdiff as above.

## Commits and receipt
One commit per step: the split (tool run, facade), each move to `Hopf/Proof`, docstrings per piece, each
rename set, import trims. Subject `Lib/<path>: <what>` or `Hopf/Proof/<path>: <what>`; body: the
declarations or units concerned, the twin/section cited; trailers
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` and
`Claude-Session: https://claude.ai/code/session_01VZt4JDgce67x5QTThwQ3E2`.
Receipt `Lib/reports/wave-1/NAME.md` (create the directory; commit it last, together with `rename.txt`,
`envdiff.json`, `envdiff.txt` and the `split_module` receipts, in `Lib/reports/wave-1/NAME/`): the cut
(table: piece | lines moved | declarations | textbook topic), the `Hopf/Proof` moves and the closure
argument, renames, lifts with their `example`s, docstring count (computed, not estimated), the build
lines verbatim, the envdiff summary reconciled name by name where it is not "moves only", and "Left"
(each item with the grep that reproduces it at your tip).
Budget: if it will not fit, stop cleanly at a green commit with the receipt saying what is left.
Report back: the receipt path, the commit range, the check lines, "Left". Nothing else.

## Progress file (added 2026-09-28 after a rate-limit cut-off killed all ten agents mid-work)
Keep `/home/goblin/.claude/jobs/06995e68/tmp/wave1/NAME/PROGRESS.md` current. Write it before your
first edit and rewrite it after EVERY step (each commit, each build started/finished, each decision):
three sections — `Done` (with commit hashes), `In progress` (what exactly is half-done, which files are
dirty and why, the pid and log of any running build/dump), `Next` (the ordered remaining steps). It is
what a successor reads if you are cut off, so a stranger must be able to continue from it alone. Prefer
many small green commits over one big one: a cut-off between commits then costs nothing.
