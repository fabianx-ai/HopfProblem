# Fix round after the reviewer pass — merge receipt (2026-09-21)

Base `62d45257` (`lib/integration` after the reviewer pass). Eleven Opus 5 agents, one worktree and
branch `fix/<name>` each, seeded with the base build; rules in the session scratch (`fix_rules.txt`);
per-agent receipts beside this file (`p01.md` … `receipts.md`). Merged `--no-ff` in arrival order,
zero conflicts (`Lib.lean` and `Lib/AxiomAudit.lean` auto-merged):

| # | branch | merge | content |
|---|---|---|---|
| 1 | `fix/p01` | `43616eba` | placeholders, Weibel/CE citations, four docstrings |
| 2 | `fix/p09` | `33e1e3bc` | adjunction docstrings, Hartshorne/Bredon/Godement/KS citations, five docstrings |
| 3 | `fix/p0708` | `7ab7a607` | manuscript labels `(C8)/(C13)/(C14)/(C24)/(C28)/(C30)`, citations, docstrings |
| 4 | `fix/p0506` | `9f44225c` | Whitney docstrings, four self-repeats, Brown/Bourbaki/Milnor citations |
| 5 | `fix/receipts` | `e547aaf2` | 22 receipt/review files corrected, dated correction sections |
| 6 | `fix/p10` | `db96d51c` | two private lemmas lifted, docstrings, blank lines, citations |
| 7 | `fix/names-dfiles` | `3f9e921f` | `FreeGroup.forall_apply_eq_self_iff`, `MonoidHom.apply_eq_apply_of_ker_le` re-added; `AddCommGroup.lean` cause; new `Hopf/Proof/AxiomAudit.lean` |
| 8 | `fix/moved` | `84e429bc` | duplicate imports; seven docstrings; `coordMatrix_eq_toMatrix`; `Fin.tailHeadAddEquiv` deleted for its `rfl` twin; two renames |
| 9 | `fix/dup-dfa` | `e284cf45` | four `_one` cochain lemmas deleted for their `_succ` twins; docstrings; `RadialFilling` documented |
| 10 | `fix/p02` | `173cd18d` | `Coproduct.lean` fully polymorphic via `Abelian.hasFiniteBiproducts`; 12 coefficient pins lifted |
| 11 | `fix/p0304` | `9a6e125a` | six `AdaptedWindows` binders widened; docstrings; citations |

103 non-merge commits, 129 files, +4,080 / −518.

## Checks on the merged head `9a6e125a`

| check | result |
|---|---|
| `lake build Lib` | green, 9,146 jobs |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,198 jobs; `mathoverflow_1973` on `[propext, Classical.choice, Quot.sound]` |
| `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit` | green; 3,310 + 4 `#print axioms` probes at the head (the figure "3,302" written here on 2026-09-21 was wrong; corrected after the fix-round review, `review/B-structure.md` finding 3), every axiom set ⊆ `{propext, Classical.choice, Quot.sound}`, no `sorryAx` |
| `scripts/lib_stock_census.py --check` | 123, ratchet PASS |
| `.{0}` pins in `Lib/*.lean` | 293 → 269 |
| environment diff (`envdiff.{json,txt}` here; base dump of `62d45257`, after dump with `rename.txt`, 3 lines) | 38,254 → 38,248 constants; lost 5 source: the four `SingularSmallChains.*_one` lemmas (twins `_succ`/`cochainRestriction_homologyMap_isIso`, `dup-dfa.md`) and `Fin.tailHeadAddEquiv` (twin `(Fin.consLinearEquiv ℤ _).symm.trans (LinearEquiv.prodComm ℤ ℤ _)`, `rfl`, `moved.md`); added 3 source: the two re-added lemmas and `LinearEquiv.coordMatrix_eq_toMatrix`; 38 changed types, all `PROOF-NAMING`: `Coproduct` 18 (8 lifts + 10 downstream `sigma*` declarations whose statements are unchanged and only carry a new `HasBiproduct` proof term) + `SingularCochains` 12 (`p02.md`), `AdaptedWindows` 6 (`p0304.md`), `PrimitivesH1` 2 (`p10.md`); i.e. 28 lifts — the union of the three branch envdiffs, nothing else; 0 moves, 0 ambiguous. Verdict FAIL by construction (deletions), reconciled above |

## Left by the agents (recorded in their receipts; corrected 2026-09-21 after the fix-round review, `review/*.md`)

Each bullet carries the command that reproduces it at the head.

- Manuscript jargon beyond the swept patterns (`git grep -nwE 'M[0-9]+|C29[a-z]' -- 'Lib/**/*.lean'`):
  `Cech/DerivedGlobalSections.lean` 9 hits ("textbook M13", "C29i", bare `C30`; `p0708.md`),
  `Lib/Topology/Sheaves/Cohomology/DerivedGlobalSections.lean` 16 (`M00-D`, `M09`, `M10`, `C29f`, `C29g`),
  `Cech/Ext.lean` 3 (`C29h`, "textbook lines 1831–1849") — the last two files were not named by any
  receipt (`review/C-prose.md` finding 4). `git grep -il textbook -- 'Lib/**/*.lean'`: 27 files, 64 hits.
  The next sweep uses `\bC[0-9]+[a-z]?\b`, `\bM[0-9]+`, `textbook`; the `C14`/`C15` hits in
  `Hurewicz/Naturality.lean` and `Homeomorph/DiskCube.lean` are paths to `Lib/docs/C1{4,5}-*.md` and stay.
- Citation numbers still open: "Exercise 2.4.5" in `CohomologicalDeltaFunctor/Effaceable.lean:19`;
  "Godement II.3.9" in `SingularCochainSheaf/ComparisonPositive.lean:20` (`p09.md`); "Bredon III Thm. 1.1"
  in `SingularCochainSheaf/GlobalUnitPredicates.lean:17` (left by `p10.md`, omitted here before;
  `p0708.md` keeps the same item as correct in `ConstantSheafH1.lean:24`, `p09.md` demoted it elsewhere as
  unverified — the two receipts disagree, `review/C-prose.md` findings 3 and 7). The Weibel "Theorem 2.4.3"
  bullet that stood here was stale: `fix/p01` (`ced4b4db`) had already replaced it in the three
  `Ext/AcyclicResolution*` files (`git grep 'Weibel.*2\.4\.3' -- 'Lib/**/*.lean'` is empty).
- Three further duplicate `import` lines (`Lib.Algebra.Module.IntegerPresentation` in
  `Hopf/SphereTopology.lean`, `Hopf/Proof/SphereTopology.lean`, `SurgeryCollapse.lean`) (`moved.md`).
- Pins the code receipts left and this list omitted before (`review/A-code.md` finding 4): the chain-side
  `.{0}` pins in `SingularCochains/PositivePrimitives.lean` (9, `chains`-bound except `dualHomotopyEquiv`'s
  `{K L}`, which is liftable — its "not local" reason in `p02.md` is refuted) and `Vanishing.lean` (2
  `ULift.{0} ℤ`, forced by the local UCT); 13 in `SingularCochainSheaf/PrimitivesH1.lean` (`p10.md`);
  "Warner 5.32" kept deliberately by `p10.md` in three files.
- The per-packet round-7 `envdiff.json` files cannot be recovered (worktrees and dumps gone); each
  receipt now states which of its claims are unverifiable (`receipts.md`).
- `w4-w1-solution` must reroute `Lib.Topology.Sheaves.Cohomology.SphereTwo` →
  `Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo` when it meets this branch (`names-dfiles.md`).
- Receipt-text errors found by the fix-round review, not yet corrected in the fixers' receipts (a fix item,
  see `Lib/reviews/REVIEW-FIX.md` §3): `p02.md`/`p0304.md`/`p10.md` describe the envdiff lost/added rows as
  auxiliaries (they are the changed-type constants themselves); `p0708.md` and `RECEIPT-08.md` item 7 call
  Hartshorne III Ex. 8.1 the sheafification description of `R^i f_*` (that is Prop. 8.1; Ex. 8.1 is the
  degenerate Leray case, as `fix/p09` cites it); MERGE.md rows 1 and 9 undercount docstrings (5 and 7).
