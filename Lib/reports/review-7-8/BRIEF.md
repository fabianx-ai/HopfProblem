# Fresh-reviewer brief — rounds 7 and 8 of the Lib/ textbook extraction

You are an independent reviewer with no prior context. Your job is to check ONE receipt written by
an agent that did cleanup work on a Lean 4 / Mathlib library, and to say whether the receipt is
TRUE, COMPLETE and whether the work it describes is SOUND. You are not here to redo the work, to
polish, or to be polite. A receipt that says "every deletion has a twin" is verified by finding
the twins, not by trusting the sentence.

## Where things are (all read-only for you)

* Source tree, all branches, git history: `/home/goblin/hopf-lib-audit` (branch
  `lib/textbook-extraction`, head `39f1d12b`, the state after both rounds). Use it for `git log`,
  `git diff`, `git show`, reading files. NEVER edit, commit, checkout, reset, stash or create
  branches there.
* A fully built copy of the same head: `/home/goblin/hopf-lib-integration` (same commit).
  You may elaborate a single file or a scratch file there with
  `cd /home/goblin/hopf-lib-integration && /home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env lean <absolute path to .lean file>`.
  A scratch file may `import Lib.Foo.Bar` and use `#check`, `#print`, `#print axioms`, `example`.
  Keep scratch files under `/home/goblin/.claude/jobs/06995e68/tmp/review-pass/<your-id>/`.
  NEVER run `lake build` there, never edit files there, never run `lean-agent-ide dump` (it takes
  ten minutes and gigabytes; the dumps and envdiff outputs you need are already in the repo).
  Run at most one `lean` process at a time and at most ~6 elaborations in total; twenty
  reviewers share this machine.
* Do not use `/tmp`. Do not push anything anywhere. Do not touch `/home/goblin/hopf`.
* The Lean toolchain is v4.33.0 with the matching Mathlib; `autoImplicit` is off repo-wide.

## The library and the rounds

`Lib/` is a general-purpose library extracted from a research formalisation (`Hopf/`,
`Hopf/Proof/`, `Solution`). Rule: `Lib` never imports `Hopf`. The extraction protocol demands that
every structural change be accounted for: a deleted declaration must have a named surviving twin
whose statement is the same or stronger (same proposition, or the deleted one is an instance of
it); a renamed declaration must be in a rename map; a universe lift (`.{0}` → `.{u}`) must keep
the statement at `u = 0` unchanged and add no hypothesis; a move to `Hopf/Proof` must not leave a
`Lib` file importing it; no `sorry`, no `axiom`, no new hypothesis on an existing statement; the
environment diff (`envdiff.json` beside the receipt: lost / added / changed-type names computed
by a tool from the elaborated environments before and after) must be reconciled line by line by
the receipt. Where the receipt says something was NOT done "for a reason", the reason is itself a
claim to test.

Round 7 (base `46c22597`): stage 1 = branches `r7/preamble` (stock preamble removal) and
`r7/names` (name-suffix strip, Mathlib duplicates, Lib.lean imports, Hopf-side cherry-picks),
merged at `9552305f`; stage 2 = ten checklist packets `r7/packet-NN` (manuscript citations →
textbook references, docstrings, universe pins, `: Type` binders; one commit per file), merged at
`d950428a`; docs at `4e15a034`. Round 8 (base `4e15a034`): seven judgement branches `r8/*`
merged in order dup-sheaf, pins, moved, dup-hom, dfiles-c, dfiles-b, dfiles-a; merge receipt
`Lib/reports/round-8/MERGE.md`; head `4ce6d6d3`; docs `39f1d12b`. The coordinator's summaries are
`Lib/reviews/INTEGRATION-7.md` and `Lib/reviews/INTEGRATION-8.md`; the work lists the agents were
given are `Lib/reports/round-7/packets/packet-NN.md` and `Lib/reports/round-7/judgement/*.md`.

Every branch was merged with `--no-ff`, so its commits are `git log <merge>^1..<merge>^2` and its
whole diff is `git diff <merge>^1 <merge>^2` (the merge commits are listed in your assignment).
The after-state you compare against is the current head `39f1d12b` (later branches may have
touched the same files; say so when it matters).

## What to check (in this order; be exhaustive where the list is under ~60 items, otherwise
## check a random sample of at least 20 and say which)

1. **Claims vs history.** Every number and every "did X" sentence in the receipt against the
   actual commits and diff: counts of files, declarations, renames, lines; that one-commit-per-file
   / one-commit-per-chokepoint rules were followed where stated; that commit messages describe
   what the commit does.
2. **Deletions.** For every deleted declaration: does the named twin exist at the head, and is its
   statement the same or stronger? Read both statements (the deleted one from `git show
   <merge>^1:<path>`, the twin from the head). A twin with an extra hypothesis, a weaker
   conclusion, a different universe level that matters, or a different definition (not merely
   defeq-by-unfolding) is a FINDING.
3. **Renames and maps.** Rename map complete, direction consistent with the receipt, every
   entry's new name present at head, old name absent.
4. **Universe lifts / binder widenings.** For a sample: the statement at `u = 0` is literally the
   old statement; no hypothesis added; no `Type` → `Type u` that silently changed which universe
   a downstream declaration lives in without the receipt saying so.
5. **Envdiff reconciliation.** Open the branch's `envdiff.json`/`.txt`. Does the receipt explain
   every lost source name, every added one, every changed type? Is anything in the JSON that the
   receipt does not mention, or vice versa?
6. **Moves to `Hopf/Proof`.** `grep -rn "import Hopf" Lib/` must be empty; the moved file's
   general content really is gone from `Lib` or really is in the "island" the receipt names.
7. **Docstrings and citations (packets especially).** Sample at least 20 added docstrings across
   the branch's files and check each against the declaration it documents: a docstring that
   states a wrong hypothesis, wrong direction, wrong object, or invents a theorem name is a
   FINDING (these were written by a language model; treat them as suspects). Sample at least 10
   replaced citations and check the cited textbook result actually is the stated result
   (Hatcher, Bredon, Bott–Tu, Milnor, Hirsch, Lee, tom Dieck, Godement, Iversen, Spanier,
   Weibel, ... — use your own knowledge; say when you are not sure).
8. **"Not done, because ..."** For every skipped item, test the stated reason: is the Mathlib
   lemma really missing / really different? is the instance really load-bearing? does the
   `ULift` obstruction really exist? Say what you tried.
9. **Hygiene.** `sorry`, `axiom`, `set_option maxHeartbeats` increases, `unsafe`, `native_decide`,
   `@[simp]` added/removed, `noncomputable` added, `private` removed, in the branch diff. Commit
   trailers present. Any `Hopf` import in `Lib`.

## Output

Write your review to `/home/goblin/.claude/jobs/06995e68/tmp/review-pass/<your-id>.md`
(Markdown, no more than ~300 lines) with exactly these sections:

1. `# Review of <receipt path>` then one line: **Verdict: ACCEPT / ACCEPT WITH FINDINGS / REJECT**
   and one sentence why.
2. `## Findings` — numbered, most serious first. Each: what is wrong, where (file:line, commit,
   declaration name), the evidence you have (paste the two statements for a wrong twin; the
   docstring and the statement for a wrong docstring), and what should happen. Severity tag:
   `[unsound]` (statement weakened / hypothesis added / proof claim wrong), `[wrong receipt]`
   (the receipt states something false), `[incomplete]` (something the receipt should list and
   does not), `[docstring]`, `[citation]`, `[nit]`.
3. `## Claims checked` — a table: claim (quoted or paraphrased) | verified / partly / refuted |
   how (command or file you looked at).
4. `## Not checked` — what you did not verify and why (time, size, needed a build).
5. `## Tool notes` — anything about the tooling or the receipt format that would have made the
   review easier or the receipt more trustworthy.

Return the same content as your final message. Do not soften findings; do not pad the claims
table with trivialities. If you find nothing wrong after real checking, say so and list what you
checked so the reader can see the coverage.
