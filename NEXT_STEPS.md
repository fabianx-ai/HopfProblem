# Next steps (after integration review 5, 2026-09-14)

Owner decision 2026-09-14: the remainder is done by Claude agents; no seat assignment. Head:
`lib/textbook-extraction`, the commit the owner names (`git log -1`). Reviews: `Lib/reviews/INTEGRATION-5.md`
(the parallel round), `INTEGRATION-4.md`. Layout: `Hopf/<path>.lean` holds only the stock still to be
moved into `Lib/`; proof-specific declarations are under `Hopf/Proof/<path>.lean`; the `Mathoverflow1973`
wrapper survives only around the final theorem (`comparator/config.json` names
`Mathoverflow1973.mathoverflow_1973`). Census (`scripts/lib_stock_census.py --check`, counts outside
`Hopf/Proof/`): 123 against baseline 1648 — 1,516 declarations moved this round in 12 agent branches
(receipts in `Lib/reports/integration-4/*-moves.md`, `freed-*.md`, `import-all.md`).

## 1. Review pass (first)

No fresh-context reviewer looked at this round's moves. Run one reviewer per receipt
(`singhom-moves.md` 686 rows, `spheretop-moves.md` 331 + 231, `recognition-moves.md` 87 + 31,
`lcp-moves.md` 94, `freed-wang.md` 73, `freed-circle.md` 16, the E1 split, `import-all.md`): statements
verbatim modulo the disclosed retargets, nothing lost, every claim reproducible. Findings go into
`INTEGRATION-5.md` §5 and are fixed before the next moves. Two points to judge explicitly: the second
SphereTopology pass moved the four `DiskOnePointCollapse.collapse*` rows after finding that their only
"SixSphere" mention is the `SixSphereCube` export alias of `OnePointCollapse` (retarget
`SixSphereCube.X -> OnePointCollapse.X`); and `lib/next-lcp` left a `namespace FirstHurewicz export
SingularChains (...)` alias block in `Hopf/LCP/CuspFilling.lean` for three `Hopf/Proof/` consumers.

## 2. Stock still under `Hopf/` (123 rows)

- `Hopf/Recognition.lean` 95: 34 CHARGED (`SixSphereCube.*` and 13 singletons) stay; 61 were blocked by
  `Hopf/SphereTopology.lean` rows that the second pass has since moved
  (`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`), so most are movable now — third pass, same
  method (`lean-agent-ide dump Hopf.Recognition`, receipts as before).
- `Hopf/SphereTopology.lean` 23, `Hopf/SingularHomology.lean` 2: CHARGED, stay; they are the file's residue
  and should move to `Hopf/Proof/<path>.lean` under the layout rule once nothing stock depends on them.
- `Hopf/Hurewicz.lean` 3: `SixSphereCube.{StandardSphere, euclideanOnePointSphereHomeomorph,
  sphereBasePoint}` are proof-specific but used by stock `Hopf/Recognition.lean`; move them to
  `Hopf/Proof/Hurewicz.lean` together with their Recognition consumers (item above).
- The 24 `PeriodTorusHigherHomology` rows of `FREED.md` left under `Hopf/Proof/LCP/Specialization.lean`
  (`freed-circle.md`, "blocked") were blocked by `Hopf/LCP/*` stock rows that `lib/next-lcp` moved
  (`TorusCoordinates.lean`); move them now.
- Then the stock files are empty or residue-only: say so per file, and retire the empty ones from the
  import chain (the consumers import `Hopf.LibShims` and their `Hopf/Proof/` twin).

## 3. Shims and module system

- De-shim pass, part 2: retire the `topSus` and `Hurewicz.DegreeTwo` aliases in `Hopf/LibShims.lean` and
  the `FirstHurewicz` alias block in `Hopf/LCP/CuspFilling.lean` by re-spelling their `Hopf/Proof/`
  consumers; give the remaining `*_mo1973_*` helpers in `Lib/` real names (`grep -rn '_mo1973_' Lib`).
- `import all` (owner: when convenient): 6 lines left — `RegularLevel.lean` (2; needs a Lib-side
  implicit-function datum with transparent `prodFun`), `SmoothFlow.lean` and `MorseLemma.lean` (mechanical
  switch to `Diffeomorph.toPartialDiffeomorphUniv` from `Lib/Geometry/Manifold/LocalDiffeomorph.lean`;
  MorseLemma is the root of the chain, full rebuild), `Morse/Cubic.lean`, `Morse/CubicFlow.lean` (inherited
  from the old Cancellation file). `Transversality/Basic.lean` can redirect its `toPartialDiffeomorph'`,
  `diffeomorph'` to the `LocalDiffeomorph.lean` versions (one line each).
- The 13 non-`module` Lib files created this round (and the 46 older ones) block `module` importers;
  conversion pass when the moves are done.

## 4. Records

- `Lib/reports/E1.md`, section "Layout split done": replace "still running at 8847/8858" by the final
  green line (8858 jobs). `Lib/reports/I.md` and `NEXT_STEPS.md` history still mention the old name
  `sum_range_shift_of_endpoints_mo1973_27356` (now `_eq`); fine as history.
- `Lib/reports/proof-split/FREED.md` header: the 40 `PeriodTorusHigherHomology` rows were under
  `Hopf/Proof/LCP/Specialization.lean`, not CuspFilling; the table was right.

## 5. Lanes and generalisations (after the above)

J-B/J-C/J-D/J-E certification per `Lib/docs/J.md`, then the product at `(1, n)`; E2 refactor at
`2k+1 ≤ n` per `E2.md`; B: the van Kampen extraction; the 300 demoted rows of `DEMOTED.md`
(after the correction): generalisation, not moves; last.

## Rules

`ps` before `lake build`; never `lake update`/`cache get`/`clean`; never push; Lake, not direct `lean`;
never kill a process by command-line pattern (use `/proc/<pid>/cwd`); reviewer ≠ author (a fresh-context
subagent is a reviewer); probes and evidence in the tree, no `/tmp`, `~`, `/home` citations; a lane report
says "landed" only for declarations that exist in `Lib/` at the head it names; nothing is "COMPLETE"
while its probe theorem is still under `Hopf/`; the Comparator stays deferred until publication.
