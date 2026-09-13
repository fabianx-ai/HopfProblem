# The `Hopf/` ↔ `Hopf/Proof/` split

Branch `lib/proof-split` off `lib/textbook-extraction` at `2e28cf5b`. Seat: coordinator (Claude
Fable 5.1), by the owner's decision of 2026-09-13. Tool: `lean-agent-ide` (`dump`, `split_module`,
`envdiff`; specifications in that repository under `spec/`), adapter `scripts/proof_split_plan.py`.

## What

Every file under `Hopf/` (except `LibShims.lean`) is divided into

- `Hopf/<path>.lean` — the **stock**: declarations whose names are on the census list
  (`scripts/lib_stock_prefixes.txt`) *and* whose dependency closure inside `Hopf/` stays on that
  list. These are the declarations still to be moved into `Lib/`.
- `Hopf/Proof/<path>.lean` — everything else: the proof of the theorem, and the 475 stock-named
  declarations that are bound to it (`DEMOTED.md`). Two `private` helpers used across the cut lost their `private` modifier
(`*.expose.txt`, recorded in the receipts); the stock files received the `Lib`/Mathlib imports the
proof chain used to provide (`keep_extra_imports` in `plan.json`).

Names, namespaces, statements and proofs are unchanged; only the defining module changes. A file
with no stock declaration moved wholesale (`git mv`): `FiniteCore`, `Shortcuts`, `Final`,
`LCP/LocalModels`, `LCP/AnalyticFillings`, `LCP/GlobalAssembly`. `Solution.lean` now imports
`Hopf.Proof.Final`.

Imports: the stock files form a chain in the original import order (`DifferentialTopology →
SingularHomology → SphereTopology → Hurewicz → LCP/CuspFilling → LCP/Specialization →
LCP/PeriodConstruction → LCP/BoundaryTopology → LCP/IntegralHomology → Recognition`); each proof
file imports its own stock file and the previous proof file. No stock file imports a proof file.

## How

1. `lake env lean-agent-ide dump Hopf.Final Solution --modules Hopf,Lib` on the built base tree:
   31,418 constants, of which 19,929 under `Hopf/` and 13,850 with a declaration range.
2. `scripts/proof_split_plan.py --dump … --apply`: classification (stock 2,328 by name, 1,853
   after closing under dependencies, 475 demoted), `plan.json`, then `split_module` per module:
   units by declaration range extended over docstring, attributes and `… in` prefix commands;
   context (header, `namespace`, `open`, `universe`, `noncomputable section`, `local notation`,
   `end`) written to both files; a standalone `attribute` follows the class of its names.
   Receipts: one JSON per module (`Hopf.<module>.json`) with the line interval and SHA-256 of
   every unit as written; wholesale moves recorded as such.
3. Build of the default targets; `dump` of the split tree; `envdiff` base → split restricted to
   `Hopf`.

## Verification

| Check | Result |
|---|---|
| Column-0 declaration keywords, original vs stay+move | 13,356 = 13,356 in every module (one header comment line counted twice per split file) |
| Receipts: every ranged constant in exactly one unit | 13,850, no duplicate |
| Dangling `… in` prefix or standalone attribute on a moved name in a stock file | 0 |
| `lake build Solution S6Shortcuts S6 Challenge` | green (`build-exit 0`); run 2 built the whole `Hopf` chain 17:58–18:05 and failed on one exposed lemma, run 3 rebuilt from `IntegralHomology` on 18:06–18:08 with exit 0; log `proof_split_build.log` |
| `envdiff` base → split, prefix `Hopf` | VERDICT PASS — lost 10 added 14 of which source declarations: 0 0 ; names with changed type 10 of which source: 0; receipt `envdiff.json` (source = ranged, non-notation constants; auxiliary differences are `_proof_n` renumbering, lazily realized `noConfusion`, equation lemmas and notation artifacts, listed in the receipt) |
| Module map equals the plan | every planned source declaration found in its planned module (`module-map-check.json`: missing 0, wrong module 0) |
| Census `scripts/lib_stock_census.py --check` | the script now skips `Hopf/Proof/` (owner's decision: what is proof-specific is not counted as still to be moved); baseline 2,663 -> 2,113 -> 1648; the prefix list is unchanged |

## Owner decisions (2026-09-13)

- Decided: `Hopf/LCP/` is included; the 475 demoted declarations (`DEMOTED.md`) keep their names
  under `Hopf/Proof/` and are no longer counted by the census; each needs a generalisation before
  it can move to `Lib/`. Owner, 2026-09-13: these are done last, after the stock lanes.
