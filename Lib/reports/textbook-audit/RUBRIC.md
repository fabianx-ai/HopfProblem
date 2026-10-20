# Textbook-adherence audit of `Lib/` — rubric (2026-09-20, head f0e28a82)

Purpose: for every file under `Lib/` (except `AxiomAudit.lean`), decide whether it is library
material as a textbook or Mathlib would state it, and what keeps it from being so. The audit is
read-only; nothing is edited. One entry per file, appended to the group's log **as soon as the file is
done** (never batched: the log must survive an interrupted run).

Entry format (exactly this shape; the entries are parsed):

```
## <path>  (<n> declarations, <m> lines)
verdict: <A|B|C|D> (<short reason>)
twin: <textbook reference (author, theorem/section) and/or the closest Mathlib file; or "none: genuine gap">
findings:
- l.<line>[–<line>] <one finding, with the declaration name where it applies>
- ...
suggestion: <the single most useful change, one sentence>
```

Verdicts:
- **A** textbook-ready: generic statements, standard names, docstrings present, no project residue; could be proposed upstream as is.
- **B** minor: docs or names only (stale sentences, missing docstrings, a nonstandard name, unused preamble, an ad-hoc constant that belongs in a `variable`).
- **C** project residue in the mathematics: a statement specialised to the project's objects, ring, universe or dimension where the textbook argument is general; a `Mathoverflow1973`/`W4W1`/`S6`/`SixSphere`/`Center`/`Threefold`-style name or hypothesis; a lemma that only exists to feed one proof step and has no textbook counterpart; a file that mixes two unrelated topics.
- **D** not library material: proof-specific to the project (belongs under `Hopf/Proof` or `W4W1`), or the file's main statement is a special case Mathlib already has (name the Mathlib declaration).

What to check per file (in this order; stop reading a 3,000-line file once the pattern is clear and say so in a finding):
1. The module docstring: does it name the textbook result and its reference? Does it promise declarations that do not exist (grep)?
2. Statements (not proofs): generality of type classes, ring, universes, dimensions; project vocabulary in names, namespaces, hypotheses; hypotheses that are the project's specific data rather than the textbook's.
3. Names and namespaces against Mathlib conventions (`Foo.bar_baz`, `IsFoo`, `foo_of_bar`).
4. Missing docstrings on public theorems and defs (count them).
5. Preamble residue: `open scoped … UpperHalfPlane Modular`, `local notation`, `set_option maxSynthPendingDepth`, `universe` declared but unused, `import Mathlib` where a specific file would do.
6. Placement: is the file where Mathlib would put it (directory, neighbouring files)?

Declaration count: `grep -cE '^(@\[[^]]*\] )?(public )?(private )?(protected )?(noncomputable )?(theorem|lemma|def|abbrev|structure|inductive|instance|class) ' <file>` is good enough.

Do not: rebuild, edit, run Lean, invent references you are not sure of (write "twin: none found" rather than guess), or spend more than about a tenth of the group's effort on any one file.
