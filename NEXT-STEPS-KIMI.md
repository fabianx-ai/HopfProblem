# Next steps — Kimi (after the integration review of 2026-09-12)

Branch: `lib/textbook-extraction`, head 692e7f5f (your C, E2, F, G, J were merged at 856e4762 on top
of GLM's A; builds green, 32/32 axiom probes exact, zero changed statements under `Hopf/`). Start
every new branch from this head. Review: `Lib/reviews/INTEGRATION.md`.

## Owner decisions (all settled 2026-09-12)

- (Settled) **E2 dimension condition:** state the lane's theorem at `2k+1 ≤ n`, which is what
  the tree's perturbation proof proves and covers every project instance (k = 2, n ≥ 5 and
  k = 1, n ≥ 3). Record the classical `2k ≤ n` as a named follow-up requiring the
  Stiefel-bundle argument. The task file's "2k ≤ n" wording is superseded.
- (Settled) **J product shape:** state the Pontryagin product at `(1, n)` now, matching the
  landed cross product; general `(p, q)` is a named follow-up once C's general cross product
  lands.
- (Settled) **SurgeryWindows** is GLM's: GLM splits it along the E1/E2/F target files; the
  E2 refactor (Muse seat) starts from the split files once they are on the branch.

## Lane C — in this order, branches `lib/C-<n>-<slug>` off 856e4762

1. **Finish C10 along the route the report already documents.** `Lib/reports/C.md` §"Open
   items (the exact seams)" records the seam honestly: the inverse side is landed and green
   (`normalizedSimplex`, the class-invariance bridge, `topNormalization`, `towerBelow`,
   `classOperator`), and what remains is the boundary relation, the `hurewiczMap`/`hurewiczInverse`
   round trips, the equivalence, and then the per-degree deletion (`ThirdHurewicz` 633,
   `FourthHurewicz` 150, `FifthHurewicz` 135 in `Hopf/Hurewicz.lean`; `SixthHurewicz` 140 in
   `Hopf/Recognition.lean`). Take the report's own elaboration lesson as the plan: the composed
   tower terms time out under naive unification, so the boundary relation is proved as small
   named lemmas, one per face-value step, each its own commit. C13 follows from C10 and needs
   nothing else. The only correction to the record: the task-level summary and `Lib/docs/C.md`
   §19 must not name C10 among landed results until the equivalence exists.

2. **Interface receipt.** Compile `C_InterfaceCheck.lean` and `C_InterfaceConsumerCheck.lean`
   at 856e4762 and write `Lib/docs/C-INTERFACE_RECEIPT.md`. Rewrite `Lib/docs/C.md` §19 with the
   names that actually landed and put the remaining C10/C13 nodes in the `ChallengeNode` form
   from `lean-protocol.md` (all fields, no prose for types).
3. **FREE rule in `Lib/`:** rename `PeriodTorusLineBundle.ChernCocycle.*`
   (`Lib/AlgebraicTopology/Hurewicz/HomotopyExtension.lean`), the nine `SixSphereCube.*`
   declarations (`…/Hurewicz/CubeSphere.lean`), the degree-2 `SecondHurewicz.SimplyConnected.hurewiczLinearEquiv`
   in `…/Hurewicz/PrismOperator.lean`, and the dimension-general content under `ThirdHurewicz.*`
   and `FourthHurewicz.CubeSubdivision.*`; shims in `Hopf/LibShims.lean`; start the
   `HigherHurewicz → Hurewicz` rename commits, naming the Mathlib twin.
4. **Docstrings:** 9 of 12 new files have no module docstring, 11 of 12 no section headers,
   1,265 of 1,326 public declarations none. `CrossProduct.lean` is your own model; apply it file
   by file, one commit each, "No proof term changed."
5. **Report corrections** in `Lib/reports/C.md`: census 5,170 → 3,893; `Hopf/Hurewicz.lean`
   22,910 → 9,631 lines; SimplexCube range off by one line at both ends; PrismOperator hash taken
   after cutting the sub-block; the non-`module` header of `CrossProduct.lean`.
6. **Commit the Stage-2 review** that `f42b9e6` cites, with the reviewer named, under `Lib/docs/`.
7. Close open item 7: the pinned Mathlib has root `GenLoop`, not `HomotopyGroup.GenLoop`.

## The packets E2, F, G, J — reassigned (2026-09-12)

Lanes J, E2, F and G are now owned by the Muse seat (`TASK-LIB-MUSE.md`), which continues your
packets in `Lib/docs/{J,E2,F,G}.md` as author. You keep lane C only. Do not edit those four
packets or their target files from now on; if C10 produces something a packet needs (the
general cross product for J's `(p, q)` follow-up, C's landed names for G), record it in
`Lib/reports/C.md` and the Muse seat picks it up from there.

8. **Authorship:** all 33 of your commits carry the repository owner as author. Set
   `git config user.name` / `user.email` for your seat so your contributions are attributable.

## Rules that the review found broken; they hold from now on

- No packet "waits for X to land" any more: A, D1, D2 and C are on the branch. Receipts are
  produced at the current head before Lean starts.
- Citations are checked against the reference, by theorem number, before they enter a ledger.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
