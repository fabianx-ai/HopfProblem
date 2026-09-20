# Round 7 packet 10 — receipt

Worktree `/home/goblin/hopf-r7-p10`, branch `r7/packet-10`, base `9552305f`,
Lean v4.33.0 / Mathlib v4.33.0.  All 24 files of the packet were worked; none left.

## Universe pins: the packet-wide finding

Every `TopCat.{0}` / `AddCommGrpCat.{0}` pin in `Lib/Topology/Sheaves/SingularCochainSheaf/`
is **forced by `AlgebraicTopology.SingularCochains.complex`** (and its neighbours `chains`,
`pullback`, `dualComplex`) in `Lib/AlgebraicTopology/SingularCochains.lean`, which is declared as

```
abbrev chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat.{0} ℤ) ℕ
abbrev complex (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) :
    CochainComplex AddCommGrpCat.{0} ℕ
```

That file is outside packet 10, so per the packet rules the pins are left and recorded here
rather than chased.  The same declaration forces the `{X Y : Type}` binders in
`PrimitivesH1.lean`.  Three *sites* in the packet — `Sheaf.lean`, `LocalKernels.lean`,
`StalkwiseSectionRange.lean`, six declarations between them **(corrected: the receipt's totals line
says "6 declarations generalised", and "three" here counts files, not declarations)** — are *not*
downstream of it and were generalised (see below).

## Per file

Legend: `cite` = module docstring rewritten to the textbook reference with the project narrative
removed; `doc +k/~k` = `k` docstrings added / `k` existing docstrings restated as mathematics;
`pins` = item 3; `binders` = item 4.

| file | citations | docstrings | universe pins | `: Type` binders |
|---|---|---|---|---|
| `SingularCochainSheaf/Presheaf.lean` | cite Bredon III.1 (+ `## Main definitions`) | +4 / ~4 | 20 left: forced by `SingularCochains.complex` | — |
| `SingularCochainSheaf/Sheaf.lean` | cite Bredon III.1, negated claim deleted (+ `## Main definitions`) | +2 / ~5 | **2 generalised** (`sheafification`, `sheafification_additive`); rest forced by `SingularCochains.complex` | — |
| `SingularCochainSheaf/LocalKernels.lean` | cite Iversen II.1 / Hartshorne II Ex. 1.2, "`H¹` comparison" narrative deleted (+ `## Main results`) | ~1 | **3 generalised** (`presheaf_stalk_exact_of_local_kernels`, `sheafificationStalkIso`, `sheafify_exact_of_local_kernels`) | — |
| `SingularCochainSheaf/PrimitivesH1.lean` | cite Hatcher Thm. 2.10 / Bredon III.1, "degrees needed by the `H¹` comparison" deleted (+ `## Main results`) | ~11 (project vocabulary "native"/"literal"/"actual" removed; commit `ab98de39`'s message says "9 docstrings" — the diff and this row's 11 are right, **the commit message is wrong**) | 14 left, **13 of them forced (corrected)**: `PrimitivesH1.lean:162`'s `variable {K L : CochainComplex AddCommGrpCat.{0} ℕ} {f g : K ⟶ L}`, which scopes the two private lemmas `homotopy_apply_closed_one` and `homotopy_apply_closed_zero`, is **not** forced — those are statements about an arbitrary `Homotopy f g` between maps of cochain complexes in `AddCommGrpCat` and mention no singular chains; nothing in `SingularCochains.chains`/`complex` pins them.  They are only *used* at `.{0}`.  The other 13 (`Cochains`, `cochainHom`, …, `nullhomotopic_pullback_closed_*`) take `(X : Type)` or `complex X A` and are forced | `{X Y : Type}` left: forced by `SingularCochains.chains (X : Type)` |
| `SingularCochainSheaf/GlobalUnit.lean` | cite Bredon III.1, negated claim deleted (+ `## Main definitions`) | +1 / ~2 | 2 left: forced | — |
| `SingularCochainSheaf/GlobalSections.lean` | cite Bredon III Prop. 1.1 / Warner 5.31 (+ `## Main results`) | +1 / ~3 | 2 left: forced | — |
| `SingularCochainSheaf/GlobalResolutionH1.lean` | cite Godement II.4.7 / Bredon II.4.1 | ~3 | 8 left: forced | — |
| `SingularCochainSheaf/GlobalUnitH1.lean` | cite Bredon III Thm. 1.1, Hatcher Prop. 2.21 | ~2 | 2 left: forced | — |
| `SingularCochainSheaf/GlobalUnitH1Criterion.lean` | cite Bredon III Thm. 1.1; negated project claims deleted | ~7 | 2 left: forced | — |
| `SingularCochainSheaf/GlobalUnitPositive.lean` | cite Bredon III Thm. 1.1 / Warner 5.31 (+ `## Main results`) | ~6 | 2 left: forced | — |
| `SingularCochainSheaf/LocalExactH1.lean` | cite Bredon III.1 / Warner 5.31 (+ `## Main results`) | ~2 | 3 left: forced | — |
| `SingularCochainSheaf/LocalExactPositive.lean` | cite Bredon III.1 / Warner 5.31 (+ `## Main results`) | ~1 | 2 left: forced | — |
| `SingularCochainSheaf/ResolutionH1.lean` | cite Bredon III.1, negated claim deleted | ~1 | 3 left: forced | — |
| `SingularCochainSheaf/ResolutionPositive.lean` | cite Bredon III.1 / Warner 5.31–5.32 (+ `## Main results`) | +2 / ~5 | 3 left: forced | — |
| `SingularCochainSheaf/OpenRestriction.lean` | cite Bredon III.1 / Warner 5.32, proof-plan sentence deleted (+ `## Main results`) | ~8 | 7 left: forced | — |
| `SingularCochainSheaf/Vanishing.lean` | cite Bredon III Thm. 1.1, "This FREE owner" sentence deleted (+ `## Main results`) | ~1 | 7 left: forced | — |
| `SingularCochainSheaf/Pullback/Presheaf.lean` | cite Bredon III.1 | +4 / ~3 | 6 left: forced | — |
| `SingularCochainSheaf/Pullback/Sheaf.lean` | cite Bredon III.1 (+ `## Main definitions`, `## Main results`) | +2 / ~5 | 8 left: forced | — |
| `SingularCochainSheaf/Pullback/Global.lean` | cite Bredon III.1 (+ `## Main results`) | +2 / ~4 | 3 left: forced | — |
| `SingularCochainSheaf/Pullback/ComparisonH1.lean` | cite Bredon III.1 / Warner 5.32, conditional project sentence deleted | ~1 | 4 left: forced | — |
| `SingularCochainSheaf/Pullback/FiniteClosedH1.lean` | cite Bredon III.1, H1-pipeline residue deleted | ~5 | 13 left: forced | — |
| `SingularCochainSheaf/Pullback/FiniteClosedPositive.lean` | cite Bredon III.1 / Warner 5.32 (+ `## Main results`) | +1 / ~6 | 3 left: forced | — |
| `StalkwiseSectionLift.lean` | cite Hartshorne II Ex. 1.2 / Iversen II.1 (+ `## Main results`) | — | already universe-polymorphic (`X : TopCat.{v}`) | the audit's ×1 is `{C : Type u}`, already a universe variable — nothing to widen |
| `StalkwiseSectionRange.lean` | cite Hartshorne II Ex. 1.2 / Iversen II.1 (+ `## Main results`) | ~1 | **1 generalised** (`app_exists_preimage_iff_stalkwise_exists_preimage`: `TopCat.{0}`/`AddCommGrpCat.{0}` → `.{u}`) | — |

Totals: 24 module docstrings rewritten with a textbook reference (project narrative, seat/lane
sentences and negated project claims removed), **19 docstrings added**, **87 docstrings restated**,
**6 declarations generalised in universe**, 0 `: Type` binders widened (both occurrences are
either already a universe variable or forced), 0 items left with an unexplained obstacle.

No declaration was deleted, no hypothesis added, no statement weakened or strengthened beyond the
six universe generalisations; no `sorry`/`axiom`/`admit`.

## Universe generalisations in detail

* `TopCat.SingularCochainSheaf.sheafification (X : TopCat.{u}) : TopCat.Presheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X`
  (was `.{0}`), and the `sheafification_additive` instance with it.  Callers instantiate at `u = 0`
  unchanged.
* `TopCat.SingularCochainSheaf.sheafify_exact_of_local_kernels` and its two private helpers
  `presheaf_stalk_exact_of_local_kernels`, `sheafificationStalkIso` over `TopCat.{u}` /
  `AddCommGrpCat.{u}`; this needed explicit `stalkFunctor AddCommGrpCat.{u}` /
  `TopCat.Sheaf.forget AddCommGrpCat.{u}` annotations (the default elaboration picked `.{0}`).
* `TopCat.Presheaf.app_exists_preimage_iff_stalkwise_exists_preimage` over `TopCat.{u}` /
  `AddCommGrpCat.{u}` (`universe u` added to the file).

## Builds

```
lake build Lib                                 Build completed successfully (9150 jobs).   exit 0
lake build Solution S6Shortcuts S6 Challenge   Build completed successfully (9189 jobs).   exit 0
lake build Lib.AxiomAudit                      Build completed successfully (9150 jobs).   exit 0
```

`Lib.AxiomAudit` axiom sets, over all reported declarations:
`[propext]`, `[propext, Quot.sound]`, `[propext, Classical.choice]`,
`[propext, Classical.choice, Quot.sound]` — nothing outside
`propext` / `Classical.choice` / `Quot.sound`.
`Solution.lean:61` reports `Mathoverflow1973.mathoverflow_1973` depends on
`[propext, Classical.choice, Quot.sound]`.

## envdiff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl`:

```
constants before 21719 after 21720 (keys 21713 21714 )
lost 20 added 21 of which source declarations: 0 0 ; names with changed type 20 of which source: 6
auxiliary lost/added/changed (not judged): 20 21 14
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

**0 source declarations lost, 0 added.**  All 6 source declarations with a changed type are
exactly the universe generalisations above:

| changed type | explanation |
|---|---|
| `TopCat.SingularCochainSheaf.sheafification` | `TopCat.{0}`/`AddCommGrpCat.{0}` → `.{u}` (Sheaf.lean) |
| `TopCat.SingularCochainSheaf.sheafification_additive` | instance for the generalised `sheafification` |
| `TopCat.SingularCochainSheaf.presheaf_stalk_exact_of_local_kernels` | `.{0}` → `.{u}` (LocalKernels.lean, private) |
| `TopCat.SingularCochainSheaf.sheafificationStalkIso` | `.{0}` → `.{u}` (LocalKernels.lean, private) |
| `TopCat.SingularCochainSheaf.sheafify_exact_of_local_kernels` | `.{0}` → `.{u}` (LocalKernels.lean) |
| `TopCat.Presheaf.app_exists_preimage_iff_stalkwise_exists_preimage` | `.{0}` → `.{u}` (StalkwiseSectionRange.lean) |

The 20 lost / 21 added constants are auxiliary (`_proof_*`, equation lemmas) attached to the
recompiled declarations; the one extra constant is **`TopCat.SingularCochainSheaf.unit._proof_1`
(corrected; the receipt said "the auxiliary of the new `universe`-generalised `sheafification`
definition")**.  `sheafification._proof_1` existed *before* this packet — it is among the names with
a changed hash on both sides — whereas `unit` (`toSheafify … (presheaf X A n)`), whose target now
elaborates through the `.{u}` `sheafification`, gained a new proof auxiliary.  It is a consequence
of the generalisation, but a different declaration from the one named.  No unexplained changed type
remains.

## Commits (`9552305f..HEAD`, one file each)

```
c5170dd3 Lib/Topology/Sheaves/SingularCochainSheaf/Presheaf.lean
d7c363c9 Lib/Topology/Sheaves/SingularCochainSheaf/Sheaf.lean
1aace75d Lib/Topology/Sheaves/SingularCochainSheaf/LocalKernels.lean
ab98de39 Lib/Topology/Sheaves/SingularCochainSheaf/PrimitivesH1.lean
988c9f09 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnit.lean
1f7ba535 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalSections.lean
b4d1e79a Lib/Topology/Sheaves/SingularCochainSheaf/GlobalResolutionH1.lean
7234e152 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitH1.lean
4f7bcf63 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitH1Criterion.lean
a6761d38 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitPositive.lean
4d004671 Lib/Topology/Sheaves/SingularCochainSheaf/LocalExactH1.lean
af45b2b5 Lib/Topology/Sheaves/SingularCochainSheaf/LocalExactPositive.lean
8650f309 Lib/Topology/Sheaves/SingularCochainSheaf/ResolutionH1.lean
4cf3ae7a Lib/Topology/Sheaves/SingularCochainSheaf/ResolutionPositive.lean
caa3f032 Lib/Topology/Sheaves/SingularCochainSheaf/OpenRestriction.lean
815cfaa9 Lib/Topology/Sheaves/SingularCochainSheaf/Vanishing.lean
12126271 Lib/Topology/Sheaves/SingularCochainSheaf/Pullback/Presheaf.lean
65b1fce0 Lib/Topology/Sheaves/SingularCochainSheaf/Pullback/Sheaf.lean
a27902bd Lib/Topology/Sheaves/SingularCochainSheaf/Pullback/Global.lean
7117905f Lib/Topology/Sheaves/SingularCochainSheaf/Pullback/ComparisonH1.lean
ad4c14c3 Lib/Topology/Sheaves/SingularCochainSheaf/Pullback/FiniteClosedH1.lean
111164f9 Lib/Topology/Sheaves/SingularCochainSheaf/Pullback/FiniteClosedPositive.lean
ebf0cc9d Lib/Topology/Sheaves/StalkwiseSectionLift.lean
22163675 Lib/Topology/Sheaves/StalkwiseSectionRange.lean
```

## Notes for the owner

The auditors' suggestions that restructure the tree (delete `GlobalUnitH1.lean`,
`GlobalUnitH1Criterion.lean`, `ResolutionH1.lean`, `Pullback/ComparisonH1.lean`,
`Pullback/FiniteClosedH1.lean`; move `globalCochainComplex` to `Sheaf.lean`; move
`LocalKernels.lean` to `Lib/Topology/Sheaves/SheafifyExact.lean`; make the private local-primitive
lemmas public) are outside the four work items of this packet and were not carried out.  The
`H¹`-only forks remain duplicates of the `_succ` results in the positive-degree files.

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-packet-10.md` (ACCEPT WITH FINDINGS; every count,
every generalisation and the forcing claim check out against the history and one probe elaboration;
no deletion, no rename, hygiene clean).  These corrections are to this receipt's text only; no Lean
file was changed by them.

1. **The "one extra constant" is `TopCat.SingularCochainSheaf.unit._proof_1` (finding 1), not the
   auxiliary of `sheafification`.**  Corrected in place in the environment-diff section.  The packet's
   own `envdiff.json` was never committed (unlike the round-8 branches), so this was reconstructed
   from `Lib/reports/round-7/envdiff-merged-d950428a.json` restricted to the three modules this
   packet changed types in (`SingularCochainSheaf.Sheaf`, `.LocalKernels`,
   `StalkwiseSectionRange`): lost-only = ∅, added-only = `…unit._proof_1`, and 20 names with a
   changed hash on both sides, among them `…sheafification._proof_1` — which therefore existed
   before the packet.  Commit the per-packet `envdiff.json` beside the receipt (round-8 rule, now
   standing for all rounds, `Lib/reviews/REVIEW-7-8.md` §4).

2. **One of `PrimitivesH1.lean`'s "14 forced" pins is not forced (finding 2).**  Corrected in the
   per-file row: the `variable {K L : CochainComplex AddCommGrpCat.{0} ℕ} {f g : K ⟶ L}` at
   `PrimitivesH1.lean:162` scoping the private `homotopy_apply_closed_one` /
   `homotopy_apply_closed_zero` is not downstream of the `SingularCochains` chokepoint; it could be
   `.{u}`.  Still 14 at head `39f1d12b`; lifting the two is on the fix list
   (`Lib/reviews/REVIEW-7-8.md` §3, packet 10).

3. **The forcing claim needs splitting by binder — and one half of it changed under this packet's
   feet.**  "Every remaining pin is forced by `SingularCochains.complex (X : Type)
   (A : AddCommGrpCat.{0})`" was true at base `9552305f`.  Packet 01 (`c31bbc73`), merged after this
   packet, lifted `complex`'s coefficient to `AddCommGrpCat.{w}`, so at the merged state the `A`-side
   pins are no longer forced *by `complex`*.  They are nevertheless still forced: the reviewer's probe
   shows `presheafToSheaf (Opens.grothendieckTopology (TopCat.of Unit)) AddCommGrpCat.{1}` fails with
   `failed to synthesize HasWeakSheafify …` while `.{0}` succeeds, so **for every file that
   sheafifies, `A : AddCommGrpCat.{0}` is forced by `X : Type` through Mathlib's sheafification
   universe constraint**.  Only the presheaf-level `A`-pins (`Presheaf.lean`'s `cochainFunctor` /
   `presheaf`, `PrimitivesH1`) are now liftable in isolation, to no practical benefit.  The `X`-side
   pins are forced by `chains (X : Type)` throughout, unchanged.  A receipt saying "forced by X" must
   say *which binder* is forced by what; `Lib/reviews/INTEGRATION-7.md` did not note the cross-packet
   effect of `c31bbc73` on this packet (and on 09 and the other `SingularCochainSheaf` holders)
   either.

4. **Internal inconsistencies (finding 6), corrected in place.**  (a) "Three declarations in the
   packet are *not* downstream of it" counts **sites** (three files); the totals line's "6
   declarations generalised" counts declarations.  (b) Commit `ab98de39` says "drop project
   vocabulary from 9 docstrings" for `PrimitivesH1.lean`; the diff has **11** restated docstrings and
   this receipt's "~11" is right — the commit message is wrong.  (c) "87 docstrings restated" is
   right but not reproducible by a one-line grep: the diff has 86 `-/-- ` first lines plus one
   docstring changed only on its second line (`unit_app_surjective`).

5. **Docstring and citation findings are code fixes, not receipt fixes.**  `Vanishing.lean`'s module
   docstring says "paracompact" where both theorems require `[MetrizableSpace X]` (the
   declaration-level docstrings say metrizable, correctly, and `ResolutionPositive.lean`'s module
   docstring words the same point honestly); `OpenRestriction.lean`'s "hereditarily paracompact"
   gloss does not match the hypotheses `[∀ V : Opens X, NormalSpace V] [∀ V : Opens X,
   ParacompactSpace V]`; four stray blank lines were inserted inside declaration signatures by the
   docstring edits (`GlobalUnit.lean:75`, `GlobalUnitPositive.lean:138`, `Presheaf.lean:96`,
   `Pullback/Sheaf.lean:100`, all still at head); and the Iversen II.1 / Bredon III "Prop. 1.1" vs
   "Thm. 1.1" / Warner 5.32 item numbers are unconfirmed.  All are on the
   `Lib/reviews/REVIEW-7-8.md` §3 list for the packet-10 fix agent.
