# Textbook-to-Lean Protocol

## Purpose

Formalization should enlarge the reusable library of mathematics, not merely discharge one
project goal. Every formal proof begins as ordinary textbook mathematics, is reviewed as
ordinary mathematics, is divided additively into named lemmas, and is only then translated
isomorphically into Lean.

The governing principle is:

> Every formalization builds the library of humanity.

Accordingly, general textbook mathematics belongs in `Lib/` and is **FREE**. A project directory
contains only the genuinely project-specific data and the thin **CHARGED** adapter applying the
free theorem.

## The transformation

The required pipeline is

```text
textbook sentence
    ≅ complete textbook proof
    = sum of reviewed proof sections
    ≅ ordered FREE library files
    ≅ exact typed Lean declaration ledger
    ≅ Lean proof terms
    → thin CHARGED application
```

Do not jump directly from a compressed mathematical sentence to Lean. That missing intermediate
representation allows elaboration problems to choose the mathematics and creates large proof
basins.

## The seven-axis formalization cycle

The physical ground is the textbook proof itself. It exists independently of Lean and is the
conserved mathematical object being transported. The seven axes below successively make that
object formally executable.

### Axis 1: awareness / constant — reproduce the proof

Read the proof as mathematics and expand every compressed sentence into a complete ordinary
textbook argument. A different mathematician reviews it once. Incorporate the accepted
corrections and freeze the result as the canonical proof.

The mathematical content is the constant of the process. Lean is not yet allowed to influence
the proof.

### Axis 2: structure / algebra — factor the proof

Decompose the continuous proof additively into named lemmas

```text
P = L₁ + L₂ + ⋯ + Lₙ.
```

Expose each lemma's hypotheses, conclusion, dependencies, and FREE or CHARGED classification.
Nothing is removed from the textbook proof; structure is added to it.

### Axis 3: focus / calculus — orient the proof

Put the lemmas in exact dependency order and treat each as a directed transformation

```text
inputs(Lᵢ) → output(Lᵢ).
```

Select one smallest meaningful seam at a time. Every dependency points backward to an already
established result. This turns the static algebraic decomposition into a proof process.

### Axis 4: presence / geometry — give every lemma a home

Embed the proof graph into the library:

```text
textbook lemma
    ↔ proof section
    ↔ namespace
    ↔ file
    ↔ declaration
    ↔ downstream consumer
```

General mathematics goes under `Lib/`; construction-specific substitution stays in the project.
Every formal file has a textbook source, and every textbook lemma has a formal destination.

### Axis 5: alignment / logic — identify it exactly with Lean

Before implementation, construct a typed correspondence for every textbook microlemma:

```text
Lᵢ ≅ Tᵢ.
```

Record:

- the exact Lean proposition and declaration signature;
- its universes and hypotheses;
- the existing Mathlib declarations supplying standard inputs;
- any representation-only or coherence lemmas;
- its exact output for the next declaration; and
- its independently green commit boundary.

A page-to-file mapping with only semantic target names is not enough. Do not give an
implementation agent a chapter-sized item and ask it to discover the lemma decomposition, API,
and proof architecture while coding. If an exact typed row cannot yet be written, alignment is
unfinished and implementation must not begin.

### Axis 6: agency / arithmetic — construct the proof term

Translate the aligned microlemma directly into Lean in the main tree. Apply the mapped
declarations, construct the required terms, discharge the explicit component equations, expose
the promised public interface, and prepare each independently shippable unit.

This is finite execution, not mathematical invention. Commit each independently green unit
promptly.

### Axis 7: flexibility / stochastic — loop and confirm

Run Lean and use its response to close the loop:

```text
compile
  ├─ failure
  │    → classify the error
  │    → return to the correct earlier axis
  │    → repair exactly that layer
  │    → compile again
  │
  └─ success
       → the kernel accepts the proof term
       → the proposition is inhabited
       → the proof is true
```

The same seven-axis cycle repeats for every lemma. A genuine mathematical failure returns to the
textbook and review; a decomposition failure returns to axes 2--3; an ownership failure returns
to axis 4; a type or API mismatch returns to axis 5; and a proof-term or elaboration error returns
to axis 6. No compiler error may silently choose different mathematics.

At the end, compile the complete target. Green compilation is the final confirmation that the
transported proof closes:

```text
compile(target) = true.
```

### The non-collapse rule

Do not collapse adjacent axes merely because one agent could perform them together. In
particular, do not collapse file placement (axis 4), typed Lean alignment (axis 5), and proof-term
construction (axis 6) into one exploratory implementation task. The implementation agent should
receive an exact typed lemma ledger and should be translating, not designing, the proof.

## Stage 1: expand the mathematics

An author agent expands the selected sentence into a complete, self-contained textbook proof.

- Write in ordinary mathematical language, with no Lean names, APIs, implementation constraints,
  or references to failed formalization attempts.
- State the exact theorem, hypotheses, definitions, standard background results, and conclusion.
- Specialize only as far as mathematical clarity requires. Separate the reusable theorem from its
  eventual project instance.
- Expand every phrase such as “standard,” “clearly,” or “by dimension” until a reader with the
  named textbook prerequisites can follow the implication.
- Record where a standard theorem is invoked and verify that its hypotheses actually hold.
- Put the work immediately in a durable topic directory under `~/s6-notes/`; never use `/tmp`.

The output of this stage is a continuous proof, not a Lean plan.

## Stage 2: one independent textbook review

A second agent reviews the completed text once as mathematics.

The reviewer checks:

- correctness of every implication;
- hidden separation, compactness, dimension, finiteness, constructibility, coefficient, and
  universe hypotheses;
- whether each cited textbook theorem has the stated form;
- whether the conclusion is exactly strong enough for the project receipt;
- whether a knowledgeable textbook reader can reconstruct all omitted details;
- which claims are genuinely general and therefore belong in `Lib/`.

The review is a separate durable artifact. It should identify exact corrections, not redesign the
proof around Lean. After the review, incorporate the accepted corrections into the canonical
textbook proof before formal decomposition begins.

## Stage 3: additive decomposition

Split the reviewed proof by **adding** structure to it.

- Preserve the full proof and its order; add section headings, named lemmas, and explicit receipts.
- Do not replace the proof with a different implementation-inspired argument.
- Each section must state its inputs and its exact output.
- Each dependency must point backward to a preceding section or to a named standard theorem.
- Choose boundaries small enough to compile and commit independently, but large enough to express
  one recognizable mathematical idea.
- Produce a correspondence table from textbook sections to intended files and declarations.

The sections are the source language for the formalization. File boundaries follow them rather
than inventing a second architecture.

## Stage 4: FREE-first file placement

Classify every section before writing Lean.

### FREE mathematics

A result is FREE when its statement does not depend on the motivating construction. Examples are
general results about sheaves, spectral sequences, covering dimension, local systems, lattices,
homology, or category theory.

- Place it in the appropriate namespace under `Lib/`.
- Give it a discoverable mathematical name and a docstring explaining the textbook result.
- State it at its natural reusable level, without project-specific types or constants.
- Census Mathlib first. Reusing or lightly wrapping an existing theorem is a successful library
  contribution.
- Add focused checks to `Lib/AxiomAudit.lean` when that is the repository convention.

### CHARGED application

A result is CHARGED only when it substitutes the explicit objects of the current construction into
a FREE theorem or proves construction-specific hypotheses.

- Keep it in the project directory.
- Make it a thin adapter whose proof visibly invokes the FREE interface.
- Do not copy general mathematics into the project file to make elaboration easier.
- If a CHARGED proof starts growing a reusable argument, stop and move that argument into `Lib/`.

The default question is not “where can this lemma compile?” but “where would humanity look for
this theorem next time?”

## Stage 5: exact typed alignment

Before any proof-term construction, lower every placed textbook lemma into an exact typed Lean
ledger. This is a read-only census and interface-design stage, not implementation.

For each microlemma, record:

- its exact declaration signature, including universes, typeclasses, and hypotheses;
- the exact earlier declaration or Mathlib theorem supplying every input;
- its output declaration and the next declaration that consumes it;
- any purely representational component, coercion, or naturality lemma;
- the source textbook sentence or named standard theorem; and
- the file and independently green commit boundary.

Signatures must be checked against the current tree. Semantic targets such as “construct the
connecting map” or “prove exactness” are not a completed ledger. If the mapping agent cannot write
the exact signature without choosing new mathematics, return to Stages 1--3 before coding.

The durable typed ledger belongs under `~/s6-notes/`. Any temporary signature probe belongs in the
main tree and must be removed or promoted into the mapped source before the stage ends.

### The certified Axis-5 Challenge handoff

Axis 5 is complete only when it hands over a **machine-elaborated Challenge packet**, not merely a
plausible-looking list of Lean signatures. The unit of handoff is one independently green commit
boundary. A chapter containing several independent boundaries must expose several Challenge
packets, even when they share one ledger.

#### Input handed to the Axis-5 agent

The coordinating agent supplies:

- the canonical textbook-proof path and hash, with the exact source section;
- the reviewed decomposition identifiers and dependency order;
- the Stage-4 FREE/CHARGED classification, destination file, namespace, and intended consumer;
- the repository, branch, expected clean HEAD, and exact already-green dependency commits;
- the authorized scope and the first later section that is explicitly out of scope; and
- the project toolchain path and focused elaboration command.

If any of these inputs is absent or inconsistent, the alignment agent reports the owning earlier
axis instead of filling the gap from implementation intuition.

#### Candidate Challenge packet produced by the Axis-5 agent

For every microlemma, the typed ledger records all fields below without ellipses, unresolved
metavariables, approximate names, or prose standing in for a type:

```text
ChallengeNode
  id                    internal textbook coordinate
  source                exact canonical textbook lemma or sentence
  class                 FREE or CHARGED
  signature             exact Lean declaration, binders, universes, instances, and result
  visibility            exact module/public-section context making each promised output importable
  imports               minimal modules needed for the signature and named APIs
  dependencies          exact green declarations supplying every input
  representation        required coercion, component, naturality, or constructor equations
  destination           namespace, file, and public declaration name
  consumer              exact later node or theorem receiving this output
  commit_boundary       independently green packet containing this node
  focused_check         command that will validate the implemented boundary
  return_seam           earliest axis owning any anticipated mismatch
```

The ledger also gives the acyclic order of the nodes and the exact list of public outputs for each
commit boundary. Existing Mathlib or `Lib/` facts are named by their actual declarations, not by a
description of the theorem one hopes exists.

#### Mandatory aggregate elaboration receipt

Before returning `GO`, the Axis-5 agent must test the entire proposed interface together:

1. Create a disposable `*_InterfaceCheck.lean` provider in the main tree, in an isolated
   namespace, using the same `module` header and exact `public section`/`public` declaration
   context recorded for the intended production file.
2. Import exactly the modules recorded in the ledger.
3. Reproduce every proposed public signature with temporary declarations and `#check` every named
   external API. Also elaborate every representation-only constructor or coherence expression on
   which the implementation recipe depends. Small proofs of purely representational equalities are
   permitted here; substantive mathematical proof construction is not.
4. Create a second disposable `*_InterfaceConsumerCheck.lean` which imports the provider as a
   module and `#check`s every promised public output by its fully qualified name. Compile the
   provider first and then this consumer with the project's pinned Lean toolchain. A same-file
   `#check` does not certify public visibility and cannot replace this import-boundary test.
5. Testing isolated snippets is useful during drafting but does not replace these final aggregate
   producer-and-consumer compiles.
6. Delete both probes and their generated local artifacts, and confirm that the project tree is
   clean and contains no committed `axiom`,
   `sorry`, placeholder, or challenge-only declaration.
7. Write a durable `*_INTERFACE_RECEIPT.md` beside the typed ledger recording the repository HEAD,
   toolchain, both exact compile commands and exit statuses, node and output counts, boundary list,
   ledger hash, import-visible output count, and clean-tree result.

If even one signature or required representation expression has not elaborated, the packet is
`DRAFT` or `NOT GO`; it may not be handed to Axis 6.

#### Independent Axis-5 review and freeze

A different agent reviews the candidate packet before construction. The reviewer checks the
textbook-to-type correspondence, hypothesis conservation, dependency completeness, noncircular
order, FREE/CHARGED placement, and the aggregate elaboration receipt. This is a focused Challenge
review, not a proof implementation or a full-library build.

Any correction invalidates the candidate hash. After corrections, the aggregate probe is compiled
again, the receipt is regenerated, and the reviewer records a final `GO` with the reviewed ledger
hash. That reviewed hash freezes the Challenge. A review which must discover nonexistent names,
repair universes, or elaborate untested signatures is completing Axis 5, not merely reviewing it;
the packet was not ready for handoff.

#### Exact handoff from Axis 5 to Axis 6

The implementation-agent task contains this manifest verbatim:

```text
AXIS-6 CHALLENGE HANDOFF
  scope:
  textbook_source:
  typed_ledger_path:
  reviewed_ledger_sha256:
  interface_receipt_path:
  repository_branch_head:
  commit_boundary:
  ordered_node_ids:
  exact_public_outputs:
  destination_files:
  green_dependency_commits:
  toolchain:
  focused_check:
  deferred_comprehensive_gate_owner:
  explicitly_out_of_scope:
  return_rule:
```

The Axis-6 agent verifies the ledger hash and repository HEAD before editing. It supplies inhabitants
only for the named nodes, preserves their public signatures and recorded visibility context, runs
the focused check, and commits the green boundary. A material type, visibility, API, or dependency
mismatch is returned to Axis 5 with the exact node identifier; the implementation agent does not
edit the frozen Challenge or silently choose a replacement interface. A separate reviewer may run
the comprehensive `Lib` and axiom gates once after a completed group of boundaries.

A Challenge is well posed precisely when all its signatures elaborate together, every promised
public output is visible from a separate importing consumer probe, every dependency resolves at the
recorded HEAD, its dependency graph is acyclic with green inputs, every node has a textbook source
and formal destination, and an independent Axis-6 agent has no remaining mathematical or
interface-design choice. Only then does `Challenge → Solution` become an independently runnable
unit of formalization.

## Stage 6: construct the isomorphic Lean proof term

Translate the aligned microlemmas in order, directly in the main tree.

- Every substantive Lean declaration must correspond to a named textbook lemma or an explicitly
  listed standard theorem.
- The implementation agent receives the exact Stage-5 ledger; it does not design the declaration
  graph or perform a broad architectural census while coding.
- Preserve the mathematical dependency graph and direction of proof.
- Lean helper lemmas may expose definitional or coercion details, but they may not silently add a
  new mathematical idea.
- When Lean reveals a genuinely missing mathematical step, stop. Add that step first to the
  textbook proof, place it in the correspondence table, and only then formalize it.
- Never use an implementation success to retroactively hide a hypothesis or shorten the textbook
  proof.
- If translation begins to feel forced or the correspondence becomes unclear, report the emotional
  signal, return to the last isomorphic boundary, and repair the prose decomposition.

The acceptance test is simple:

> For every formal file, one can point to the textbook section it translates; for every textbook
> section, one can point to its formal image or to a named existing library theorem.

## Stage 7: compile, loop, and ship each independent section

- Work in the main tree when safe; use durable named git worktrees when concurrency requires them.
- `/tmp` is off-limits. All incomplete prose, reviews, mappings, patches, and gap reports go under
  `~/s6-notes/`.
- Keep the tree buildable and placeholder-free.
- Compile the focused target first, then the relevant library/root target and axiom audit.
- Treat each compiler error as feedback to be classified against Axes 1--6. Repair the earliest
  incorrect layer, then run the cycle again; do not accumulate downstream patches around it.
- Run `git diff --check` before committing.
- Commit each independently finished FREE library section promptly; do not wait for the entire
  project theorem.
- Land green commits in the main tree promptly. Never push or send externally.

## Collaboration roles

- The author agent owns the initial textbook expansion.
- The review agent performs the single independent mathematical review.
- The typed-correspondence agent performs the read-only API census and writes the exact Stage-5
  declaration ledger before implementation.
- Formalization agents translate that accepted ledger autonomously in the main tree, or in a
  durable named worktree when actual concurrency requires one.
- The coordinating agent preserves the global correspondence, integrates green commits, reports
  the proof state, and remains available to reason with the user. It should not absorb delegated
  implementation work merely because it can do so.
- Check autonomous agents at sensible timer-based stopping points, not by constant polling.

## Rejection tests

Stop and return to the previous stage if any of the following occurs:

1. A Lean file has no identifiable textbook source section.
2. A textbook step depends on a hypothesis that was never stated.
3. A general theorem is being buried in a project namespace.
4. Project-specific nouns appear inside what should be a reusable theorem.
5. Lean errors are causing the proof to change before the mathematical change is written down.
6. Work exists only in an ephemeral directory or an unrecorded process.
7. A large uncommitted batch contains an independently green library result.

When a rejection test fires, preserve all unfinished work in `~/s6-notes/`, state the exact seam,
and resume from the last reviewed isomorphic boundary.
