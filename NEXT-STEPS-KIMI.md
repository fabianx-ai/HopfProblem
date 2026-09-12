# Next steps — Kimi (after the integration review of 2026-09-12)

Branch: `lib/textbook-extraction` at 856e4762 (your C, E2, F, G, J are merged there on top of
GLM's A; builds green, 32/32 axiom probes exact, zero changed statements under `Hopf/`). Start
every new branch from this head. Review: `Lib/reviews/INTEGRATION.md`.

## Owner decisions you are waiting on (ask in the report if still open; do not guess)

- **E2 dimension condition:** `2k+1 ≤ n` versus `2k ≤ n` for the immersion/embedding rows.
- **J product shape:** the `(p,q)` cross product versus the `(1,n)` instance only.
- (Settled) **SurgeryWindows** is GLM's: GLM splits it along the E1/E2/F target files; your
  E2 starts from the split files once they are on the branch.

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

## The packets E2, F, G, J — none may start Lean until it is GO

Verdicts: J DRAFT (closest), E2 DRAFT, F DRAFT, G NOT GO. What GO requires, per
`lean-protocol.md` Stage 5: a Stage-2 review artifact in the tree; every ledger row with an
exact Lean signature (binders, instances, universes, result) and the full `ChallengeNode`
fields; namespaces that resolve at 856e4762; a compiled producer probe and consumer probe with a
durable `Lib/docs/<lane>-INTERFACE_RECEIPT.md`; and an independent Axis-5 review. In order:

8. **F first, two fixes then two landings.** Correct the two Milnor numbers: the Whitney lemma
   is *Theorem 6.6* (6.4 is the Second Cancellation Theorem) and the Basis Theorem is
   *Theorem 7.6* (7.8 is the middle-dimension product-cobordism theorem). The task file carried
   the wrong numbers and has been corrected. Then land F0a and F0b now: they depend only on
   Mathlib. Replace the `…` inside `primitive_row_has_unit_after_column_additions`; write F7/F11
   as signatures; add the `Smale.` namespaces to `MorseSurgeryData.beltIntersectionSign` and
   `RankThreeWhitneyModel.Space`.
9. **J**: replace the `H₁ G →ₗ[ℤ] Hₙ G` / `⋀[ℤ]^n` notation rows with Lean signatures
   (`exteriorPower` is not an identifier at the pin; the notation `⋀[ℤ]^n M` is); probe, receipt,
   review in tree. Then J's Lean. The 42 coherence declarations in `Hopf/LCP/Specialization.lean`
   (formerly your G-J3) are GLM's now; import them from `CrossProduct.lean` when they land.
10. **E2**: exact signatures for the immersion/embedding rows with their
    `Smale.ManifoldImmersion.` namespace; drop the "Milnor TDV §2 Lemma" pointer (TDV §2 is
    Sard–Brown); probe, receipt, review in tree, `E2-review.md` committed; then the in-`Lib`
    refactor starting from GLM's split of `SurgeryWindows.lean`.
11. **G last**: write the Stage-2 review; bring the ledger body (`G-map.md` §1) into the packet;
    add the `MorseCancel.` namespaces; probe, receipt. G waits on C10 and F by design.
12. **Authorship:** all 33 of your commits carry the repository owner as author. Add a
    co-author line if your contributions are to be attributable.

## Rules that the review found broken; they hold from now on

- No packet "waits for X to land" any more: A, D1, D2 and C are on the branch. Receipts are
  produced at the current head before Lean starts.
- Citations are checked against the reference, by theorem number, before they enter a ledger.
- A lane report says "landed" only for declarations that exist in `Lib/` at the head it names.
