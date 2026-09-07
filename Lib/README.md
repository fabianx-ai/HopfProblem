# `Lib/` — reusable mathematics

`Lib/` holds general mathematics formalized in this repository: statements that make no
reference to the six-sphere construction (the threefold, its cusps, period lattices, elliptic
fibres, honeycombs, or any `Fin 6`/`Fin 7`-specific datum). Everything here is written to be
upstream-bound: Mathlib-shaped file paths (`Lib/AlgebraicTopology/…`, `Lib/Geometry/Manifold/…`,
`Lib/Analysis/Complex/…`), Mathlib naming conventions, a docstring on every public declaration
stating the textbook result, and no dependency on the project: **a file under `Lib/` never
imports `Hopf.*`, `S6.*`, `S6Shortcuts`, `Challenge` or `Solution`.** The finished extraction of
the degree-one Hurewicz theorem into `Mathlib/AlgebraicTopology/Hurewicz/*`
(github.com/fabianx-ai/mathlib4, PR #4) is the template for what a `Lib/` file should become;
a copy is in-tree, and the next section says what to copy from it and what not to. Read
`Degree1.lean` lines 12–70 before writing any `Lib/` file.

## Reference example

`Lib/AlgebraicTopology/Hurewicz/` holds the five files of that PR, verbatim apart from import
paths (each file says so in a comment under the copyright block). They prove the Hurewicz
theorem in degree one: for a path-connected space, singular first homology with integer
coefficients is the abelianized fundamental group (Hatcher, Theorem 2A.1), with naturality,
conjugation invariance, the class of an `n`-fold periodic loop, and the dictionary between
characters of `π₁` and of `H₁`. They build unchanged against the Mathlib pinned in
`lake-manifest.json` (all five modules, 8 s wall; `#print axioms` on `hurewiczEquiv`,
`hurewiczEquiv_loopClass`, `h1CharacterOfPi1_comp_map` and
`loopHomologyClass_periodicScaledLoop` gives exactly `propext`, `Classical.choice`,
`Quot.sound`). Read them before starting any lane, `Degree1.lean` lines 12–70 first; a `Lib/`
file is finished when it looks like these.

One thing to know about their history: the Lean came first. The proofs existed in a project
namespace; the textbook outline in the module docstring, the section headers and the
per-declaration docstrings were written afterwards to say what the proofs already do, and the
commits that added them changed no proof term. The extraction lanes are work of the same kind —
recovering the textbook from green Lean and reshaping the file around it — so "textbook before
Lean" in `lean-protocol.md` reads here as: the module docstring and the section headers are
written before the move is committed, and the proofs are not redesigned.

What to imitate:

- **The textbook lives in the module docstring**, in this order: `# Title`; the theorem in one
  paragraph with the exact type of the headline declaration; `## Outline of the proof` as a
  numbered list whose every step names the declarations realizing it; `## Main definitions and
  results`; `## References` with the `references.bib` key; `## Tags` (`Degree1.lean` 12–70).
  Interface files use the shorter form: what is provided, a results list with one-line
  meanings, and who instantiates it (`CycleClasses.lean` 11–33, `H1Character.lean` 10–25). The
  reader knows the mathematics before the first `def`.
- **Section headers narrate the proof.** `/-! ### … -/` in proof order, with two to five lines
  of prose wherever the textbook glosses a step the code had to supply (`Degree1.lean` 417–422,
  507–512; `SimplexPaths.lean` 181–185).
- **One file per textbook step.** `SimplexPaths` (simplices, paths as one-simplices, the
  concatenation triangle, the homotopy square), `CycleClasses` (explicit cycles and classes
  for a complex of modules over any ring), `Degree1` (the theorem), `PeriodicLoop` and
  `H1Character` (consequences). Each docstring says what the file provides and where it is
  used.
- **Mathlib header and layout.** Copyright, license and `Authors:` lines in the Mathlib form
  (no SPDX line), then `module`, minimal `public import`s, one module docstring, the `open`
  lines, `@[expose] public noncomputable section`, one `namespace` block with undotted names,
  `variable`s hoisted once per block; no `set_option` or `universe` line that is not used.
- **Mathlib naming and namespaces.** `AlgebraicTopology.Hurewicz.hurewiczEquiv`,
  `loopHomologyClass_trans`, `SingularH1.map_comp`: namespaces follow the directory, theorem
  names are built from the declarations they relate, `@[simp]` marks the normal forms. Value
  lemmas end in `_apply`, `_val`, `_def`; characterizations in `_eq_iff`, `_eq_zero_iff`;
  `_surjective`, `_injective`; functoriality is `Foo.map`, `Foo.map_id`, `Foo.map_comp`,
  `Foo.map_<generator>`; `<thing>_induction_on` carries `@[elab_as_elim]`; the inverse
  direction of an equivalence gets `<equiv>_symm_<generator>`; the headline theorem's
  docstring opens with `**The … theorem …**` (`Degree1.lean` 964–968, 1005–1012).
- **A docstring on every public declaration** — `def`, `abbrev`, `theorem` and `lemma` alike,
  even where the linter would not complain — stating the mathematical role, not the type
  (`SimplexPaths.lean` 446–449; `Degree1.lean` 838–841, 945–946; an instance that pins a
  diamond says so, `Degree1.lean` 218–222).
- **Lemma granularity.** One face, edge or boundary computation per lemma, each short;
  `private` only for cast normalizations and proof-internal bridges (20 of 224 declarations),
  placed immediately before their single consumer.
- **simp normal forms.** Categorical squares at the morphism level carry
  `@[reassoc (attr := simp), elementwise (attr := simp)]` and the hand-written element form is
  documented but not `@[simp]` (`CycleClasses.lean` 157–168, 258–266); a simp lemma's
  left-hand side is restated in normal form before it is tagged (`Degree1.lean` 970–977).
- **The Mathlib twin.** Before the rename commit, name the existing Mathlib file closest in
  subject and shape and match its binders, `lemma`/`theorem` choice, idioms and API shape.
  `CycleClasses` follows `Algebra/Homology/ShortComplex/ModuleCat.lean` and the single-tier
  structure of `RepresentationTheory/Homological/GroupHomology/LowDegree.lean`;
  `SingularH1.map_eq_singularHomologyFunctor_map` is the `rfl` lemma tying the new object to
  the library's own functor.
- **No project vocabulary.** Nothing in the five files names the construction that motivated
  them; `CycleClasses` was generalized from `ℤ` to any ring on the way, because its twin is
  stated that way and `Degree1` recovers the `ℤ` case by instantiation.
- **One commit per step, from a provenance baseline.** The PR's history reads step by step:
  verbatim baseline, namespaces, split into files, headline names, textbook docstrings, style,
  generalization. The first commit places the moved bytes verbatim, records the SHA-256 of
  every source file or range in its message, and names the only edits (import paths); every
  later commit carries one concern and says whether any proof term or statement changed; a
  commit that changes proof terms names the reason and the twin it follows. Shape a lane's
  branch the same way.

What not to copy:

- the `Authors: PLACEHOLDER` line; write the real author line;
- `(X : Type)` in some blocks and `Type*` in others (`Degree1.lean` 84 vs 516): choose `Type*`
  unless a universe constraint forces otherwise, and say which;
- linter overrides in the tree (the PR adds three lines to Mathlib's directory-dependency
  linter): record an import that reaches a forbidden directory as an open item instead;
- commit messages that cite audits or drafts not present in the tree;
- theorems left without a docstring (`PeriodicLoop.lean` 42–127);
- re-binding an already hoisted variable in a signature (`Degree1.lean` 982, 1008);
- helpers placed after the section they belong to (`SimplexPaths.lean` 412–421);
- files without a `## References` entry (four of the five).

## Placement rule (FREE / CHARGED)

The rule is stated in `lean-protocol.md` at the repository root, **Stage 4: FREE-first file
placement**, with the governing principle in its **Purpose** section and the placement axis in
**Axis 4: presence / geometry**. In short: a result is FREE when its statement does not depend
on the motivating construction; FREE results live under `Lib/` at their natural reusable level.
A result is CHARGED only when it substitutes the explicit objects of the construction into a
FREE theorem; CHARGED results stay under `Hopf/` as thin adapters whose proofs visibly invoke
the `Lib/` interface. "Where would humanity look for this theorem next time?" decides the file.

## Stock rule (the ratchet)

Most of the generic mathematics of this project still lives inside `Hopf/` (see
`Lib/EXTRACTION_PLAN.md`). The number of such *stock* declarations is checked in:

- `scripts/lib_stock_prefixes.txt` — the declaration-name prefixes classified generic by the
  census (one entry per line; `Prefix`, `Prefix.Sub`, or `Hopf/File.lean:Prefix`);
- `scripts/lib_stock_baseline.txt` — the committed count.

**The committed number may only decrease.** The CI / ratchet step is

```sh
python3 scripts/lib_stock_census.py --check      # exit 1 if the count exceeds the baseline
python3 scripts/lib_stock_census.py --update     # after an extraction: lower the baseline
python3 scripts/lib_stock_census.py --by-file    # the per-file / per-prefix table
```

The script needs no Lean toolchain. It also fails if any `Lib/**/*.lean` imports a project
module. A commit that moves declarations out of `Hopf/` runs `--update` and commits the
lowered baseline together with the code; adding an entry to the prefix list is allowed only
with a census row in `Lib/EXTRACTION_PLAN.md` justifying it; raising the baseline by hand must
be justified in the commit message.

## Definition of done for an extraction lane

Lanes are defined in `Lib/EXTRACTION_PLAN.md`. A lane is done when all of the following hold:

1. **Textbook in the file.** Every new `Lib/` file carries its textbook in the module
   docstring — the statement with the exact type of the headline declaration, the reference
   (book, theorem number, `references.bib` key), the proof outline mapped to declaration
   names, `## Main definitions and results` — and `/-! ### … -/` section headers in proof
   order (model: `Lib/AlgebraicTopology/Hurewicz/Degree1.lean` lines 12–70). For a *pure move*
   the correspondence table (source `Hopf/` range → target file → declarations) goes in
   `Lib/reports/<lane>.md`, not in a docstring. For a *generalize-then-move* lane the complete
   textbook proof of the generalized statement is written first in `Lib/docs/<lane>.md`
   (`lean-protocol.md`, Stages 1–3), reviewed once, then the decomposition, then the typed
   ledger, then Lean; the finished proof is transcribed into the module docstring when the
   file lands.
2. No `sorry`, no `axiom`, no `proof_wanted` under `Lib/`; no `PLACEHOLDER` in headers; the
   Mathlib header form (no SPDX line); a docstring on every public `def`, `abbrev`, `theorem`
   and `lemma`.
3. `#print axioms` on every top theorem of the lane (listed in the plan) shows exactly
   `propext`, `Classical.choice`, `Quot.sound`; the probes are added to `Lib/AxiomAudit.lean`.
3a. **Docstring first, twin named.** The module docstring and section headers of each target
   file are written before the move is committed (drafted in `Lib/reports/<lane>.md` if the
   file does not exist yet), and the Mathlib twin file each target follows is named in the
   report and in the rename commit; the file's binder style, `lemma`/`theorem` choice and API
   shape follow it.
4. Every moved declaration is deleted from `Hopf/`; every consumer named in the plan is
   re-routed (`import Lib.…`) and `lake build` of each consumer module is green; the final
   consumers `Hopf.Final` and `Solution` build; the Comparator verdict is unchanged.
5. `python3 scripts/lib_stock_census.py --check` passes and the baseline was lowered.
6. `Lib.lean` imports the new modules; `git diff --check` is clean.
7. A report `Lib/reports/<lane>.md` records what moved, consumers re-routed, census before /
   after, the `#print axioms` output, wall-clock build times, and open items.

## Branch and commit conventions

- One branch per lane, `lib/<lane-id>-<slug>` (e.g. `lib/A-singular-homology`), off
  `lib/textbook-extraction`.
- Commit message prefix `lib(<lane>):`, e.g. `lib(A): move Mayer–Vietoris to
  Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean`. One commit per `Lib` file or
  per independently green unit; each commit builds.
- **Provenance baseline, then one concern per commit.** The first commit of a lane places the
  moved bytes verbatim, records the SHA-256 of every source range in its message, and changes
  only import paths and `namespace` lines, each named. Every later commit carries one concern
  (`move`, `rename`, `doc`, `style`, one `refactor`) and states whether any proof term or
  statement changed ("No proof term changed."); a commit that changes proof terms names the
  reason and the twin file it follows.
- **Transitional namespace rule.** On first landing a moved file may keep
  `namespace Mathoverflow1973` and the original declaration names, with `export`/`alias`
  shims left in `Hopf/` so that consumers with hundreds of references stay green. The rename
  to Mathlib-style names and namespaces is a separate second commit in the same lane
  (`lib(<lane>): rename …`), and the lane is not done until it has landed.
- Statements of moved theorems do not change in a pure-move lane as seen from `Hopf/` (only
  names, namespaces and `variable` binders): the `Hopf/` consumer must recover the original by
  instantiation. The `Lib/` statement may be *more general* when the generalization is
  representation-only — coefficient ring, universe, binder hoisting — and is dictated by the
  twin file; it goes in its own commit with the reason (model: `CycleClasses`, `ℤ` → any ring,
  any universe). Any other statement change is a generalize-then-move item and needs the
  textbook file.
- Never push; leave attribution to the repository owner's instructions.
