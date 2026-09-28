# Monolith wave 1 — merge receipt (2026-09-28)

Base `e669bc93` (`lib/integration` after the fix-round review). Ten Fable agents, one worktree and branch
`wave1/<name>` each, seeded with the base build; rules `RULES.md` beside this file (the fixer rules of the
previous rounds plus the split protocol: cut by topic with `split_module.py`, the original module kept as a
name-preserving facade so no consumer and not `Lib.lean` changes, project material to `Hopf/Proof` only where
no `Lib` module reaches it, docstrings on everything that stays, `mo1973` names renamed, full chain + audits +
census + envdiff before the receipt). Per-agent receipts `<name>.md` and artefacts `<name>/` beside this file.
Merged `--no-ff` in arrival order, zero conflicts (`Hopf/SphereTopology.lean`, `Hopf/Recognition.lean`,
`Lib/AlgebraicTopology/Hurewicz/Straightening.lean` auto-merged):

| # | branch | merge | file(s) | pieces (of which `Hopf/Proof`) | declarations moved | docstrings added | renames | lifts |
|---|---|---|---|---|---|---|---|---|
| 1 | `wave1/residue` | `0de73dd2` | — (REVIEW-FIX §3 list, label sweep over 8 files, 3 citations, 2 duplicate imports) | 0 | 0 | 48 rewritten | 0 | 1 (`dualHomotopyEquiv`) |
| 2 | `wave1/relative` | `590c6867` | `Immersion/Relative` 5,012 lines | 12 (0) | 215 | 1 | 0 | 0 |
| 3 | `wave1/cancellation` | `b80990e7` | `Morse/Cancellation` 3,803 | 12 (0) | 137 | 1 | 0 | 0 |
| 4 | `wave1/connection` | `392c4820` | `Morse/Connection` 8,169 | 18 (0) | 231 | 0 | 0 | 0 |
| 5 | `wave1/mayer` | `b3660423` | `SingularHomology/MayerVietoris` 2,847 | 14 (0) | 249 | 0 | 0 | 0 |
| 6 | `wave1/prism` | `e23d6acb` | `Hurewicz/PrismOperator` 5,301 | 16 (0) | 454 | 0 | 20 (`DegreeTwo.SimplyConnected.*` → `Hurewicz.Prism.*`) | 10 |
| 7 | `wave1/cross` | `2aecbe34` | `SingularHomology/CrossProduct` 4,471 | 9 (0) | 218 | 0 | 115 (`PeriodTorusHigherHomology.*` → `SingularHomology.*`) | 0 |
| 8 | `wave1/hurewicz2` | `77028d76` | `Hurewicz/Subdivision` 2,580, `Hurewicz/CubeChainDecomposition` 2,266 | 16 (0) | 371 | 0 | 0 | 0 |
| 9 | `wave1/morse-d` | `2f06962b` | `Morse/SurgeryCollapse` 5,431, `Morse/OrderedCancellation` 2,097 | 30 (5) | 317 | 281 | 0 | 0 |
| 10 | `wave1/rearrangement` | `8eba3d72` | `Morse/Rearrangement` 2,777 | 12 (2) | 153 | 0 | 4 (`MorseCancellation.*` → `Real.smoothTransition.*`, `expNegInvGlue.hasDerivAt`) | 0 |

76 non-merge commits, 417 files, +411,310 / −44,796 (the bulk is the `split_module` receipt JSON per
piece, ~40 KB each, and the per-branch `envdiff.json`). Eleven of the 24 monoliths are split: 139 new
modules (132 under `Lib/`, 7 under `Hopf/Proof/`), 2,345 declarations moved verbatim (every unit
SHA-256-checked by the tool), 39 of them to `Hopf/Proof` (the dimension-5/6 and index-3 material of
`OrderedCancellation`, `SurgeryCollapse`, `Rearrangement`). Nothing deleted, no statement changed; every
facade keeps every name, so the 59 + 43 + 39 + … consumers and `Lib.lean` are untouched.

Each agent kept a `PROGRESS.md` (Done / In progress / Next) in its scratch after the first launch was cut
off by a rate limit with 0–14 commits per branch; all ten were resumed from those files and their
transcripts without loss. Lake 5.0.0 has no `-j` flag; the agents pinned builds with `taskset` instead.

## Checks on the merged head `8eba3d72` (`final/` logs in the session scratch)

| check | result |
|---|---|
| `lake build Lib` | green, 9,278 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,337 jobs; `mathoverflow_1973` on `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit` | green; 3,298 + 4 probes (+ 12 axiom-free), every set ⊆ `{propext, Classical.choice, Quot.sound}`, `sorryAx` 0 |
| `scripts/lib_stock_census.py --check` | 123, ratchet PASS |
| `grep -rn '^import Hopf' Lib/ --include=*.lean` | empty |
| `.{0}` in `Lib/**/*.lean` | 269 → 278 textually; 268 in source (−1, the `dualHomotopyEquiv` lift) + 9 in two committed lift-check scratch files `prism/lift_examples.lean`, `residue/LiftCheck.lean` |
| files over 1,800 lines under `Lib/` | 14: `Lib/AxiomAudit.lean` (probes) and the 13 monoliths of batch 2 |
| environment diff (`envdiff.{json,txt}` here; base dump of `e669bc93`, after dump of `8eba3d72` under `rename_all.txt`, 139 lines) | 38,248 → 38,301 constants; lost 0 / added 0 source; 2,407 source declarations moved 1-to-1 over 139 module pairs (7 pairs, 39 declarations, into `Hopf.Proof`); 0 ambiguous; 34 source types changed, all `PROOF-NAMING`: the 10 prism lifts, the `dualHomotopyEquiv` lift, 17 `SecondHurewicz.SimplyConnected.*.eq_1` aliases in `Hopf/LibShims.lean` (equation lemmas re-generated under the renamed prism constants), and 6 `SingularMayerVietoris.*` statements whose abstracted proof term is now named `toSmallLeft._proof_1` instead of `smallDifferential._proof_1` because the module boundary moved (`mayer.md` reconciles all six: `uses` without `_proof_n` equal on both sides). Verdict PASS |

The head dump without the rename map (`final/dump_head2.jsonl`, 38,301 constants) is the base for batch 2.

## Left by the agents (each receipt's "Left" carries its reproducing grep; cross-cutting items here)

- **`native*`/`Native*` vocabulary** kept everywhere (Connection 94 declaration names, Subdivision 605
  occurrences, Cancellation 226, SurgeryCollapse 466, Rearrangement, Relative 7): the consumers are the
  other monoliths and `Hopf/LibShims.lean`; a rename wave after the facades are dissolved.
- **Universe 0** stays where `SingularChains.Chains (X : Type)`, `SingularSimplex`, `crossInsertLeft`
  pin it (prism 238, hurewicz2 44, mayer 109 binders, cross all; SurgeryCollapse 173 binder groups): the
  chain-interface decision (NEXT_STEPS (3)).
- **Twins, nothing deleted**: MayerVietoris' formal-chains/subdivision/support/mesh pieces (97
  declarations) vs `SingularSmallChains/Barycentric/*`; `SingularMayerVietoris.homologyBiprodEquiv` vs
  `Coproduct.homologyBiproductEquiv`; `cubeBoundary_productBoundary` vs `subdivisionSquare_boundary_cases`;
  `OnePointCover.spherePunctureHomeomorph` vs `SpherePoint.punctureHomeomorph`;
  `SignedCoordinates.negative_card_split` vs `MorseCancellation.negative_card_split`; three Cancellation
  pairs; CrossProduct's `integerBilinear*` vs `LinearMap.flip/compl₂/lcomp`; `NativeSubdivision.insertPermutation`
  vs `CubeSubdivision.PermutationInsertion.insert`; `exists_lebesgue_number_two` vs Mathlib's
  `lebesgue_number_lemma_of_metric`.
- **Better homes not taken** (facade-dissolving step): `HomologyDescent` → `ModuleHomology`; `formalMap_*`
  → MayerVietoris formal chains; six supported-chain lemmas of hurewicz2 → `SingularHomology`;
  `PathComponents` (Hatcher 2.7) → `SingularHomology`; `PuncturedBall` → beside `PuncturedRadial`;
  `OnePointCover` → `SingularHomology/OnePointCover.lean`; `Negation` → `Morse/Index.lean`;
  `SmoothTransition` → `Lib/Analysis/SpecialFunctions/`; `AmbientTransversality` → `Transversality/`;
  `LogarithmicCutoff` has no analysis home.
- **Statement-level items (not this wave)**: CrossProduct left degree fixed to 1/2 and 1-class-only
  commutativity/associativity; `cancel_of_transverse_level_isotopy`'s ~25 explicit hypotheses;
  MayerVietoris exactness as `range = ker` not `ShortComplex.Exact`; `PlaneImmersion.Plane := ℝ × ℝ`;
  `two_sphere_map_unit_of_homology_bijective` stays in `Lib` on `Hemisphere.Sphere 2` (Lib consumer);
  `MorseCancellation.*` prefixes in Relative (16 names) blocked by monolith consumers.
- **Hygiene carried verbatim**: `import Mathlib` in many pieces; `attribute [local instance] … in` per
  declaration; `open` context lines in every piece; import lists not trimmed in rearrangement/prism; 13
  over-long lines in `TubeMotion.lean`; four pre-existing `unusedSimpArgs` warnings; `taskset` not `-j`.
- **Residue's own**: 21 generic English `textbook` hits judged not labels; chain-side `.{0}` pins (8 + 2 +
  13) unchanged; "Warner 5.32" kept; optional restores of "III Ex. 8.1 (Leray)" and the five "Bredon III §1"
  demotions; `CubeChainDecomposition.lean`'s 4 manuscript refs (now in hurewicz2's pieces, not swept — see
  `hurewicz2.md`, which replaced three) and `SurgeryCollapse.lean`'s duplicate import (removed by morse-d).

## Batch 2 (next)

The 13 remaining monoliths (`Collar`, `MorseLemma`, `RiemannMapping`, `Flow/HeightTranslating`,
`Morse/Cubic` (0 consumers — candidate for a whole move to `Hopf/Proof`), `Morse/Existence`,
`Morse/SurgeryWindows`, `Transversality/Basic`, `Whitney/{CleanStrips, EmbeddedArcs, FrameField,
RankThreeModel}`, `Topology/Dimension/CubeBoundaryThreeCells`) import each other only through facades, so
they split concurrently: twelve agents (EmbeddedArcs + FrameField together), base = the docs commit on
`8eba3d72`, base dump `final/dump_head2.jsonl`.
