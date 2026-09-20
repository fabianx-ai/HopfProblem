# Round 7 packet 06 — receipt

Worktree `/home/goblin/hopf-r7-p06`, branch `r7/packet-06`, base `9552305f`, Lean v4.33.0.
All 15 files of `Lib/reports/round-7/packets/packet-06.md` were worked; nothing is left.

## Per file

| file | citations replaced | docstrings added | pins generalised | binders widened | items left |
|---|---|---|---|---|---|
| `Lib/Geometry/Manifold/Whitney/EmbeddedArcs.lean` | module docstring (stock-move provenance, family list, "Twin") → Milnor §§5–6 | 88 (0/88 before) | none present | none (`Type*` throughout) | — |
| `Lib/Geometry/Manifold/Whitney/FrameField.lean` | module docstring (same provenance block) → Milnor §§5–6 | 121 (0/121 before) | none present | none (`Type*` throughout) | — |
| `Lib/Geometry/Manifold/Whitney/RankThreeModel.lean` | module docstring (same provenance block) → Milnor §§5–6 | 160 (0/160 before) | none present | none (`Type*` throughout) | — |
| `Lib/GroupTheory/Abelianization/SemidirectProduct.lean` | `## References` added (Brown, *Cohomology of Groups*, Ch. II) | 4 | none | 0 of 3 counted: `{K : Type u} {Q : Type v}` are already universe-polymorphic (the count matched `Type u`, not `Type`) | — |
| `Lib/GroupTheory/GroupExtension/Abelianization.lean` | `## References` added (Brown, Ch. II) | 0 (all present) | none | 0 of 3 counted: `Type u`/`Type v`/`Type w` already polymorphic | — |
| `Lib/LinearAlgebra/ColumnKernel.lean` | 5: module docstring (`CENTER_COLUMN_KERNEL_TEXTBOOK.md`, CK1–CK7, `CENTER_NATIVE_H5_INJECTIVITY_TEXTBOOK.md`, HI7) and four declaration docstrings | 0 (all present, all restated) | none | none | the `ℤ`-only statements and the two spurious instance arguments (`[Module ℤ (A × B)]`, `[Module ℤ (ker F)]`): generalising the ring is a restatement, not a universe or binder item |
| `Lib/LinearAlgebra/ExteriorPower/ExteriorProductCoordinates.lean` | `## Main definitions`/`## Main results`/`## References` (Bourbaki A III §8.5) and the sign convention | 1 (`coe_wedge`) | none | 0 of 2 counted: `(R : Type u)`, `{M : Type v}` already polymorphic | — |
| `Lib/LinearAlgebra/ExteriorPower/MatrixCoordinates.lean` | provenance paragraph (`Hopf/LCP/Specialization.lean`, `Solution.lean` monolith lines) deleted → Bourbaki A III §8.5–8.6 | 1 (`finCoordinates_apply`) | none | 0 of 1 counted: `(R : Type u)` already polymorphic | — |
| `Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean` | module docstring (`Hopf/LCP/Specialization.lean`, boundary J-A of `Lib/docs/J.md`) → Bourbaki A III §8.6 and Horn–Johnson §0.8.7 | 2 (`sortedSubsetFintype`, `sortedSubset_card`) | none | none | the `ℤ`-only duplicates of `MatrixCoordinates.lean` and the `PeriodTorusHigherHomologyExterior` namespace: deleting or renaming declarations is outside the four items |
| `Lib/LinearAlgebra/ExteriorPower/ReindexedCoordinates.lean` | `## Main definitions`/`## Main results`/`## References` (Bourbaki A III §8.5–8.6) | 3 | none | 0 of 14 counted: `Type u`/`Type v₁`/`Type v₂` already polymorphic | — |
| `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` | `## Provenance` section (move from `Hopf/Recognition.lean`, lane F0a, planned rename) → Milnor §7 | **10 (0/10 before) (corrected)** | **0 (corrected)** — the file contains no explicit universe pin at the base; the "6 declarations generalised" were the same six binder widenings, counted twice | 6 binders `{A : Type}`, `{H : Type}`, `{H K : Type}` → `Type*` | `MorseCancellation.*` names kept (a rename deletes declarations); `import Mathlib` kept (not one of the four items) |
| `Lib/RepresentationTheory/FreeGroupCoinvariants.lean` | audit disclaimer ("no center family, monodromy matrix, sheaf, …") deleted → Brown II.3 | 0 (all present) | none | 0 of 3 counted: `Type u`/`Type v`/`Type w` already polymorphic | — |
| `Lib/RepresentationTheory/FreeGroupGeneratorCokernel.lean` | planning paragraph ("cellular edge orientations or slit-cover transitions", "the algebraic endpoint needed by a future … Poincare-duality comparison", disclaimer) deleted → Brown II.3 | 3 | 1 pin documented as forced: `freeGroupGeneratorCokernelEquivGroupHomologyH0 {S B M : Type u}` is **forced by Mathlib's `groupHomology` (corrected)**, declared under `variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)` (`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean:122`).  It is **not** forced by `Rep`, which is three-universe polymorphic in this Mathlib (`structure Rep (k : Type u) (G : Type v)` with carrier `V : Type w`, `Mathlib/RepresentationTheory/Rep/Basic.lean:30`).  The pin is genuine; the reason first given was wrong | 0 of 5 counted: the other binders are already polymorphic | the single universe of the `H₀` statement (forced, recorded in its docstring) |
| `Lib/Topology/Covering/FiberFrameCentralizer.lean` | module docstring rewritten without "fibre frame" prose → Hatcher §1.3 (Prop. 1.39) | 0 (both present, both restated) | none | 0 of 3 counted: `Type uG`/`Type uE`/`Type uX` already polymorphic | file not renamed to `Covering/MonodromyCommute.lean` (a rename is outside the four items) |
| `Lib/Topology/Covering/QuotientConnectedness.lean` | `## References` added (Hatcher §1.3) | 0 (present) | none | 0 of 3 counted: already polymorphic | — |

Totals **(corrected)**: manuscript/provenance citations replaced in 9 files (5 declaration-level
citations in `ColumnKernel.lean` plus 8 module docstrings), **392 docstrings added** (the receipt
said 395), **0 universe pins generalised** (the receipt said 6: no pin existed in
`TransvectionReduction.lean`, and the six edits were the binder widenings, counted a second time),
**6 `: Type` binders widened to `Type*`**, 1 pin recorded as forced.  See the corrections section at
the end.

## Builds

```
lake build Lib                                  -> ✔ [9149/9150] Built Lib (4.4s); Build completed successfully (9150 jobs).
lake build Solution S6Shortcuts S6 Challenge    -> ✔ Built Solution; Build completed successfully (9189 jobs).
   info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms:
         [propext, Classical.choice, Quot.sound]
lake build Lib.AxiomAudit                       -> Build completed successfully (9150 jobs).
   axiom sets over the whole audit: [propext, Classical.choice, Quot.sound], [propext,
   Classical.choice], [propext, Quot.sound], [propext] — no other axiom appears.
```

## Environment diff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl`:

```
constants before 21719 after 21719 (keys 21713 21713)
lost 8 added 8 of which source declarations: 0 0 ; names with changed type 8 of which source: 6
module moves: 0   ambiguous: 0   auxiliary constants that changed module: 0
VERDICT PASS
```

0 source declarations lost, 0 added. Changed types, all explained:

| name | explanation |
|---|---|
| `MorseCancellation.classCoordinateMatrix` | `{A : Type}` → `{A : Type*}` |
| `MorseCancellation.classCoordinateMatrix_mulVec` | `{A : Type}` → `{A : Type*}` |
| `MorseCancellation.classCoordinateMatrix_surjective` | `{A : Type}` → `{A : Type*}` |
| `MorseCancellation.functional_class_row_surjective` | `{H : Type}` → `{H : Type*}` |
| `MorseCancellation.transported_classes_of_matrix_product` | `{H K : Type}` → `{H K : Type*}` |
| `MorseCancellation.functional_rows_of_matrix_product` | `{H K : Type}` → `{H K : Type*}` |
| `MorseCancellation.classCoordinateMatrix.eq_1` (auxiliary) | equation lemma of the generalised `classCoordinateMatrix` |
| `MorseCancellation.canonicalMiddleMatrix.eq_1` (auxiliary) | equation lemma in `Lib/Geometry/Manifold/Morse/CutTransport.lean` whose right-hand side mentions the now universe-polymorphic `classCoordinateMatrix`; `canonicalMiddleMatrix` itself is unchanged |

No unexplained changed type.

## Commits (base `9552305f`, in order)

```
48052b61 Lib/LinearAlgebra/ColumnKernel.lean: replace manuscript citations by the statement
265ee952 Lib/GroupTheory/Abelianization/SemidirectProduct.lean: cite Brown, document 4 simp lemmas
32d9f567 Lib/GroupTheory/GroupExtension/Abelianization.lean: cite Brown for the split-extension H₁
43347be7 Lib/Topology/Covering/QuotientConnectedness.lean: cite Hatcher §1.3
17638f59 Lib/Topology/Covering/FiberFrameCentralizer.lean: cite Hatcher §1.3, drop "frame" prose
b480e23f Lib/LinearAlgebra/ExteriorPower/MatrixCoordinates.lean: cite Bourbaki A III §8.5-8.6, drop provenance
85942d28 Lib/LinearAlgebra/ExteriorPower/ExteriorProductCoordinates.lean: cite Bourbaki A III §8.5
318c9097 Lib/LinearAlgebra/ExteriorPower/ReindexedCoordinates.lean: cite Bourbaki, document 3 simp lemmas
573742ab Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean: cite Bourbaki/Horn-Johnson for Cauchy-Binet
845398cf Lib/RepresentationTheory/FreeGroupCoinvariants.lean: cite Brown II.3, drop the audit disclaimer
8fa00a4f Lib/RepresentationTheory/FreeGroupGeneratorCokernel.lean: cite Brown II.3, document 3 declarations
81255bfb Lib/LinearAlgebra/Matrix/TransvectionReduction.lean: cite Milnor §7, document 10 declarations, widen Type binders
9b1dcdf4 Lib/Geometry/Manifold/Whitney/FrameField.lean: cite Milnor §§5-6, document 121 declarations
78b1fa6a Lib/Geometry/Manifold/Whitney/EmbeddedArcs.lean: cite Milnor §§5-6, document 88 declarations
b13cb556 Lib/Geometry/Manifold/Whitney/RankThreeModel.lean: cite Milnor §§5-6, document 160 declarations
```

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-packet-06.md` (ACCEPT WITH FINDINGS; the code changes
are sound — docstrings, module docstrings and six `Type` → `Type*` widenings only, no statement
weakened, no hygiene issue, the six envdiff changed types explained).  These corrections are to this
receipt's text only; no Lean file was changed by them.

1. **The one structural change was counted twice (finding 1).**  "6 universe pins generalised" and
   "6 `: Type` binders widened" are the **same six edits**.  The base
   `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` contains no explicit universe pin at all
   (`grep -nE '\.\{|Type 0'` on it at `9552305f` is empty); the only universe-related change in the
   whole branch diff is `{A : Type}` ×3, `{H : Type}`, `{H K : Type}` ×2 → `Type*` in commit
   `81255bfb`.  Correct figures: **0 pins generalised, 6 binders widened, 1 pin recorded as forced**.
   The per-file row and the Totals line are corrected in place.  `Lib/reviews/INTEGRATION-7.md`
   inherited the double count and is corrected there.

2. **Docstring counts (finding 2).**  (a) `TransvectionReduction.lean`: the receipt said "9 (1/10
   before)".  The base file has **0** declaration docstrings (only the `/-!` module docstring) and
   the commit adds **10** — as commit `81255bfb`'s own message says.  The "1/10" was an error in the
   audit input that this receipt copied instead of correcting.  (b) The per-file column sums to
   **392**, not the 395 in the Totals line: 88 + 121 + 160 + 4 + 1 + 1 + 2 + 3 + 10 + 2 = 392
   (`FreeGroupGeneratorCokernel` = 2 new + 1 rewritten, reported as 3).  No combination of this
   receipt's own numbers gives 395.  Both corrected in place.

3. **The forced-pin reason named the wrong Mathlib declaration (finding 6).**  What pins
   `freeGroupGeneratorCokernelEquivGroupHomologyH0 {S B M : Type u}` is **`groupHomology`**
   (`variable {k G : Type u} … (A : Rep.{u} k G)`,
   `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean:122`), not `Rep`, which is
   three-universe polymorphic here.  The pin is genuinely forced for a statement about
   `groupHomology (Rep.of rho) 0`; the conclusion stands and only the reason was wrong.  Corrected
   in place; the declaration docstring, which names `Rep`, is a code fix on the
   `Lib/reviews/REVIEW-7-8.md` §3 list.

4. **Coverage per file was not recorded (finding 8a).**  Declarations documented / total, which the
   other receipts state: `EmbeddedArcs` 88/88, `FrameField` 121/121, `RankThreeModel` 160/160,
   `TransvectionReduction` 10/10 — full coverage in all four.

5. **The 8 lost / 8 added auxiliary constants are named nowhere and cannot be reconstructed
   (finding 8b).**  The envdiff summary line above reports them; this receipt lists none, and the
   dumps and per-packet `envdiff.json` were never committed (only the round-wide
   `Lib/reports/round-7/envdiff-merged-d950428a.{json,txt}` is in the tree, and it mixes all ten
   packets).  Whenever the auxiliary count is non-zero the names must be listed; committing the
   per-packet `envdiff.json` beside the receipt is the standing rule from round 8 on
   (`Lib/reviews/REVIEW-7-8.md` §4).

6. **Two table cells are mislabelled (finding 8c) and one change is described as a replacement when
   it was a deletion (finding 8d).**  (c) `ExteriorProductCoordinates.lean` and
   `ReindexedCoordinates.lean` appear under "citations replaced", but nothing was replaced there — a
   `## References` block was *added*.  The Totals line counts only 9 files, so the totals are right
   and only the column header is wrong.  (d) The three Whitney module docstrings already cited
   Milnor §§5–6 before this branch; the actual change is the deletion of the
   provenance / family-list / "Twin: no Mathlib counterpart" paragraphs plus a prose rewrite.  The
   "Twin" information — that these files have no Mathlib counterpart — was **dropped, not carried
   over**, and this receipt did not say so.

7. **Docstring and citation findings are code fixes, not receipt fixes.**  Four docstrings repeat
   their own sentence verbatim (`FrameField.lean:1865, 2233`, `RankThreeModel.lean:1051, 1358`);
   `isCompact_innerBigonCollar` states `0 < r`, which is not assumed, and omits `0 < h`;
   `nonempty_belt_tubularBigon` says "embedded two-sphere" where the statement asks only for a smooth
   map and omits `[CompactSpace M]` and the null-homotopy hypothesis; Brown "Ch. II" is cited for the
   LHS five-term sequence (VII.6), "II.3" for coinvariants (II.2) and the free-group resolution
   (I.4); Bourbaki A III §8.5 is cited for the exterior-algebra product formula (§7.8 — §8.5 is
   "Minors of a matrix", which is the right citation for `MatrixCoordinates`).  All are on the
   `Lib/reviews/REVIEW-7-8.md` §3 list for the packet-06 fix agent.
