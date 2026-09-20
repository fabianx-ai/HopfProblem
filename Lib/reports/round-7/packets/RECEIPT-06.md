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
| `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` | `## Provenance` section (move from `Hopf/Recognition.lean`, lane F0a, planned rename) → Milnor §7 | 9 (1/10 before) | 6 declarations generalised (see table below) | 6 binders `{A : Type}`, `{H : Type}`, `{H K : Type}` → `Type*` | `MorseCancellation.*` names kept (a rename deletes declarations); `import Mathlib` kept (not one of the four items) |
| `Lib/RepresentationTheory/FreeGroupCoinvariants.lean` | audit disclaimer ("no center family, monodromy matrix, sheaf, …") deleted → Brown II.3 | 0 (all present) | none | 0 of 3 counted: `Type u`/`Type v`/`Type w` already polymorphic | — |
| `Lib/RepresentationTheory/FreeGroupGeneratorCokernel.lean` | planning paragraph ("cellular edge orientations or slit-cover transitions", "the algebraic endpoint needed by a future … Poincare-duality comparison", disclaimer) deleted → Brown II.3 | 3 | 1 pin documented as forced: `freeGroupGeneratorCokernelEquivGroupHomologyH0 {S B M : Type u}` is **forced by Mathlib's `Rep`/`groupHomology`**, which put ring, group and module in one universe | 0 of 5 counted: the other binders are already polymorphic | the single universe of the `H₀` statement (forced, recorded in its docstring) |
| `Lib/Topology/Covering/FiberFrameCentralizer.lean` | module docstring rewritten without "fibre frame" prose → Hatcher §1.3 (Prop. 1.39) | 0 (both present, both restated) | none | 0 of 3 counted: `Type uG`/`Type uE`/`Type uX` already polymorphic | file not renamed to `Covering/MonodromyCommute.lean` (a rename is outside the four items) |
| `Lib/Topology/Covering/QuotientConnectedness.lean` | `## References` added (Hatcher §1.3) | 0 (present) | none | 0 of 3 counted: already polymorphic | — |

Totals: manuscript/provenance citations replaced in 9 files (5 declaration-level citations in
`ColumnKernel.lean` plus 8 module docstrings), **395 docstrings added**, **6 universe pins
generalised** (all in `TransvectionReduction.lean`), **6 `: Type` binders widened to `Type*`**,
1 pin recorded as forced.

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
