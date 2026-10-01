# Wave 2 — `Lib/Geometry/Manifold/Collar.lean` (NAME = collar)

Base `lib/integration` at `3760f829`; branch `wave2/collar`; worktree `/home/goblin/hopf-w2-collar`.
Judgement entry: `Lib/reports/round-7/judgement/monoliths.md` (verdict C, six topics).
Model: Claude Fable 5.1 (`claude-fable-5-1`). Wall clock: started 2026-09-28 ≈23:55 CEST (reading,
closure, tool runs; cut off twice with nothing committed), resumed 2026-10-01 15:39 CEST, ended
2026-10-01 ≈16:15 CEST.

Tooling: `split_module.py` run eight times on the base source, one piece per run (stay set = the
piece); receipts `Lib/reports/wave-2/collar/split_<Piece>.json`, plan `plan.tsv`. The 147 units are
each written exactly once; checked by substring search of every unit's base text (receipt line
ranges against `git show 3760f829:Lib/Geometry/Manifold/Collar.lean`) in its piece: 147 found, 0 missing.
By hand: the piece headers (license, imports, module docstring, `open` lines), removal of the
section headers left empty in each piece, three section headers renamed/added in `Tubular` and
`DiskTubular`.

## The cut

Line numbers refer to the base file (2541 lines, 147 declarations = 162 ranged constants with
structure fields and constructors).

| piece (`Lib/Geometry/Manifold/Collar/…`) | base lines | declarations (ranged constants) | textbook topic |
|---|---|---|---|
| `Tubular.lean` | 69–659, 1573–1583 | 48 (55) | normal bundle of `M ⊂ ℝᴺ`, tubular neighbourhood theorem `NativeEuclideanEmbedding.exists_tubularNeighborhood`, `SmoothRetraction` (Lee, Smooth Manifolds, Thm 6.24, Prop. 6.25, compact `M`); tube lemma `DiskFraming.exists_pos_prod_closedBall_subset` |
| `RangeTransport.lean` | 1018–1318 | 16 (24) | `DiskFraming.SmoothRangeTransportOn`, frames of a range bundle near a star-convex compact set (cf. Hirsch, Differential Topology, Ch. 4 §1–2) |
| `DiskTubular.lean` | 876–1014, 1320–1571, 1585–1676 | 29 (29) | tubular neighbourhood of an embedded closed ball `exists_tubularNeighborhood_in_open_of_embedded_closedBall` (Lee Thm 6.24; Hirsch Ch. 4 §5) |
| `HeightCollar.lean` | 663–874, 1680–1861 | 17 (17) | collar of a regular level adapted to the height, `RegularLevel.exists_heightCollar` (cf. Lee Thm 9.25; Milnor, h-cobordism §3) |
| `SmallPerturbation.lean` | 1865–1980 | 10 (10) | `id + u`, `u` smooth `k`-Lipschitz, `k < 1`, is a diffeomorphism; bump translations (cf. Hirsch Ch. 2 §1) |
| `SupportedDiffeomorph.lean` | 1984–2161 | 16 (16) | extension by the identity of a compactly supported diffeomorphism in a chart (cf. Milnor, Topology from the Differentiable Viewpoint §4) |
| `LevelTransport.lean` | 2165–2520 | 10 (10) | ambient diffeomorphisms between regular levels / sublevels across a band without critical values (Milnor, Morse Theory, Thm 3.1; h-cobordism §3) |
| `SphereCoordinates.lean` | 2522–2541 | 1 (1) | diffeomorphism of unit spheres induced by a linear isometry |

Facade: `Lib/Geometry/Manifold/Collar.lean` keeps a module docstring (rewritten: the pieces; the
"plan's Tubular.lean is folded here" narrative deleted) and `public import`s the eight pieces,
nothing else. `Lib.lean` untouched; no consumer edited.

Imports (trimmed; the base had `Mathlib` + 16 Lib imports + a duplicate Mathlib line):
`Tubular` ← `WhitneyEmbedding`, `VectorBundle.ProjectionBundle`; `RangeTransport` ←
`VectorBundle.ProjectionBundle`; `DiskTubular` ← `Collar.Tubular`, `Collar.RangeTransport`;
`HeightCollar` ← `Collar.Tubular`, `RegularLevel`, `Flow.HeightTranslating`; `SmallPerturbation` ←
`WhitneyEmbedding`; `SupportedDiffeomorph`, `SphereCoordinates` ← `Mathlib` only; `LevelTransport` ←
`Collar.HeightCollar`, `Collar.SmallPerturbation`, `Collar.SupportedDiffeomorph`. The transitive Lib
import closure of the facade equals that of the base file (44 modules, script over the `import` lines),
so no consumer loses an import. Dropped from every piece: `set_option maxSynthPendingDepth 3` (build
passes without, but it changes two elaborated statements, see the reconciliation below; restored in
`RangeTransport` by the fix round, commit `5a03b3bc` on `fix/waves`), the duplicate
`public import Mathlib.Geometry.Manifold.LocalDiffeomorph`.

## Moves to `Hopf/Proof` and the closure argument

None. Script over `dump_head.jsonl` (`uses` edges, backwards from every constant of every other
`Lib` module): all 162 ranged constants of the module are reachable from another `Lib` module (0 not
reachable), so nothing may move; and the file contains no dimension-6 / `Sphere 2` / index-specific
statement. `Lib/AxiomAudit.lean` has one probe into the module
(`exists_tubularNeighborhood_in_open_of_embedded_closedBall`), unchanged.

## Renames

None (`rename.txt` is empty). No `mo1973` name in the module:
`grep -rn mo1973 Lib/Geometry/Manifold/Collar/` is empty.

## Universe lifts

None: every binder is already `Type*`; `grep -rn 'Type}\|\.{0}' Lib/Geometry/Manifold/Collar/` is empty.

## Docstrings

Computed over the eight pieces (lines matching
`^(noncomputable )?(theorem|def|abbrev|structure|instance|lemma)\b` outside comments): 147
declarations, 147 with a docstring, 0 added (the judgement's "0 missing" holds). 8 module
docstrings written (one per piece) and the facade's rewritten.

## Checks (nohup, `taskset -c 6,7,8`), at `f95e27b7`

```
lake build Lib.Geometry.Manifold.Collar      Build completed successfully (8758 jobs).
=== lake build Lib                           Build completed successfully (9286 jobs).
=== lake build Solution S6Shortcuts S6 Challenge
                                             Build completed successfully (9345 jobs).
=== lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
                                             Build completed successfully (9288 jobs).
=== census
stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)
ratchet PASS: 123 <= baseline 1648
=== grep -rn --include=*.lean '^import Hopf' Lib/        (empty)
```

Axiom audit log (23545 lines): `sorryAx` 0 times; axiom sets `[propext, Classical.choice,
Quot.sound]` (1692), `[propext, Quot.sound]` (111), `[propext]` (10), 12 "does not depend on any
axioms". `grep -rn '^import Hopf' Lib/` without `--include=*.lean` hits nine `.md`/`.lean.txt`
files under `Lib/docs/` that are present at the base.

## Dump and envdiff (`envdiff.txt`, verbatim)

```
constants before 38301 after 38303 (keys 38199 38201 )
lost 11 added 13 of which source declarations: 0 0 ; names with changed type 11 of which source: 2
  PROOF-NAMING DiskFraming.exists_smooth_frame_near_starConvex
  PROOF-NAMING DiskFraming.exists_smooth_frame_on_neighborhood_closedBall
auxiliary lost/added/changed (not judged): 11 13 9
module moves (source declarations, 1-to-1):
      29  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.DiskTubular
      17  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.HeightCollar
      10  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.LevelTransport
      22  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.RangeTransport
      10  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.SmallPerturbation
       1  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.SphereCoordinates
      16  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.SupportedDiffeomorph
      55  Lib.Geometry.Manifold.Collar -> Lib.Geometry.Manifold.Collar.Tubular
ambiguous module changes: 0
auxiliary constants that changed module: 123
VERDICT PASS
```

Reconciliation, name by name. Source declarations lost 0, added 0. Two source names are listed
with a changed type hash, both classified `PROOF-NAMING` by the tool (same `uses` up to `_proof_n`):
`DiskFraming.exists_smooth_frame_near_starConvex` and
`DiskFraming.exists_smooth_frame_on_neighborhood_closedBall` — their statement text is unchanged,
but without the dropped `set_option maxSynthPendingDepth 3` it elaborates with different instance
paths (e.g. `Semiring.toMonoid (Ring.toSemiring Real.instRing)` in place of `Real.instMonoid`), so
the type hashes changed, 3226562774 → 3622023359 and 995586449 → 3798691450; the old and new types
are definitionally equal, and the tool's `PROOF-NAMING` class only compared `uses`, which are
identical (corrected 2026-10-02: this said "their statements (text unchanged, verbatim units) embed
an abstracted proof constant whose number depends on what the module elaborated before; in the
smaller module `RangeTransport` the numbering differs"; neither `uses` list contains a `_proof_n`
constant, at base or head. The fix round restores the option in `RangeTransport`, commit
`5a03b3bc` on `fix/waves`, which gives both theorems their base type hashes back; receipt
`Lib/reports/wave-reviews/fixes.md`). They are the 2
missing from `RangeTransport`'s move count: 22 + 2 = 24 = plan. The other counts equal `plan.tsv`
(55, 29, 17, 10, 16, 10, 1; total 162). The remaining lost/added entries are `_proof_n` constants
only: `DiskFraming.SmoothRangeTransportOn.trans._proof_8` (→ `_proof_8`, `_proof_9`) and
`SphereCoordinates.ofLinearIsometry._proof_3 … _proof_10` (→ `_proof_3 … _proof_11`), i.e. proof
abstraction renumbered and split differently (+2 constants: 38301 → 38303). The 123 auxiliary
constants that changed module are `_proof_n`/`match_n`/equation lemmas following their parents.

## Left

1. Statements not generalised (judgement: "state the tubular and collar theorems for non-compact
   `M`"): that changes statements/proofs, outside a verbatim split. `[CompactSpace M]` occurs 13 times in the pieces.
   Reproduce: `grep -c 'CompactSpace M' Lib/Geometry/Manifold/Collar/*.lean`.
2. Project vocabulary kept: `NativeEuclideanEmbedding` (defined in
   `Lib/Geometry/Manifold/WhitneyEmbedding.lean`, not mine) and the `DiskFraming` namespace (used by
   `Immersion/Relative/*`, `Whitney/*`, `Morse/Rearrangement/TransverseChart`, monoliths being split
   concurrently). Reproduce: `grep -rln 'DiskFraming\.' --include=*.lean Lib Hopf`.
3. Root-namespace names in `RangeTransport`: `isOpen_forall_compact`, `homotopyTransportDomain`,
   `mem_homotopyTransportDomain`, `isOpen_continuousHomotopyTransportDomain` (no consumer outside the
   piece; candidates for `DiskFraming.`/a topology file in a later rename pass). Reproduce:
   `grep -rn 'isOpen_forall_compact\|omotopyTransportDomain' --include=*.lean Lib Hopf`.
4. `DiskFraming.exists_pos_prod_closedBall_subset` (tube lemma, six external consumers) sits in
   `Tubular` under the `DiskFraming` namespace although it is pure topology; it belongs in a
   topology file under a neutral name. Reproduce: `grep -rn exists_pos_prod_closedBall_subset --include=*.lean Lib | wc -l`.
5. `SmallPerturbation` imports `WhitneyEmbedding` only for `isLocalDiffeomorphAt_of_contMDiffOn`
   (and `IsLocalDiffeomorph.diffeomorphOfBijective'` from `Lib…LocalDiffeomorph`); moving that lemma
   to `Lib/Geometry/Manifold/LocalDiffeomorph.lean` would free the piece of the Whitney/handle import
   chain. Likewise `Tubular`/`HeightCollar` inherit `Morse.HandleAttachment` etc. through
   `WhitneyEmbedding` (the judgement's import finding; not fixable inside this file). Reproduce:
   `grep -n '^public import' Lib/Geometry/Manifold/Collar/*.lean Lib/Geometry/Manifold/WhitneyEmbedding.lean`.
6. `SphereCoordinates.ofLinearIsometry`'s natural home is next to
   `SphereCoordinates.standardParametrization` in `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean`
   (a monolith being split by another agent; not touched). Reproduce:
   `grep -rn 'def SphereCoordinates' --include=*.lean Lib`.
7. Existing docstrings are terse ("The normal model equivalence."); rule 4 asks only for missing ones,
   none were rewritten. Two lines over 100 columns in `Tubular.lean`, verbatim from the base.
   Reproduce: `awk 'length>100' Lib/Geometry/Manifold/Collar/*.lean | wc -l`.
8. Lake 5.0.0 has no `-j`; builds ran under `taskset -c 6,7,8`.
