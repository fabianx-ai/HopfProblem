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
| `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit` | green; 3,302 probes, every axiom set ⊆ `{propext, Classical.choice, Quot.sound}`, no `sorryAx` |
| `scripts/lib_stock_census.py --check` | 123, ratchet PASS |
| `.{0}` pins in `Lib/*.lean` | 293 → 269 |
| environment diff (`envdiff.{json,txt}` here; base dump of `62d45257`, after dump with `rename.txt`, 3 lines) | 38,254 → 38,248 constants; lost 5 source: the four `SingularSmallChains.*_one` lemmas (twins `_succ`/`cochainRestriction_homologyMap_isIso`, `dup-dfa.md`) and `Fin.tailHeadAddEquiv` (twin `(Fin.consLinearEquiv ℤ _).symm.trans (LinearEquiv.prodComm ℤ ℤ _)`, `rfl`, `moved.md`); added 3 source: the two re-added lemmas and `LinearEquiv.coordMatrix_eq_toMatrix`; 38 changed types, all `PROOF-NAMING`: `Coproduct` 18 + `SingularCochains` 12 (`p02.md`), `AdaptedWindows` 6 (`p0304.md`), `PrimitivesH1` 2 (`p10.md`) — the union of the three branch envdiffs, nothing else; 0 moves, 0 ambiguous. Verdict FAIL by construction (deletions), reconciled above |

## Left by the agents (recorded in their receipts)

- Manuscript jargon beyond the swept patterns: ~15 docstrings in `Cech/DerivedGlobalSections.lean`
  ("textbook M13", "C29i", bare `C30`); `grep -rn 'textbook\|Textbook' Lib/ --include=*.lean` 66 hits
  in 27 files (`p0708.md`).
- Weibel "Theorem 2.4.3" in the three `Ext/AcyclicResolution*` files vs the softened "§2.4" elsewhere
  (`p0708.md`, `p0304.md`); "Exercise 2.4.5" in `CohomologicalDeltaFunctor/Effaceable.lean`;
  "Godement II.3.9" in `ComparisonPositive.lean:20` (`p09.md`).
- Three further duplicate `import` lines (`Lib.Algebra.Module.IntegerPresentation` in
  `Hopf/SphereTopology.lean`, `Hopf/Proof/SphereTopology.lean`, `SurgeryCollapse.lean`) (`moved.md`).
- The per-packet round-7 `envdiff.json` files cannot be recovered (worktrees and dumps gone); each
  receipt now states which of its claims are unverifiable (`receipts.md`).
- `w4-w1-solution` must reroute `Lib.Topology.Sheaves.Cohomology.SphereTwo` →
  `Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo` when it meets this branch (`names-dfiles.md`).
