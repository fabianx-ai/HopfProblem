# Review of Lib/reports/round-7/packets/RECEIPT-06.md

**Verdict: ACCEPT WITH FINDINGS** — the code changes are sound (docstrings, module docstrings and
six `Type` → `Type*` widenings only; no statement weakened, no hygiene issue, envdiff changes
explained), but the receipt double-counts its one structural change (six binder widenings are
reported both as "6 universe pins generalised" and "6 binders widened"), its docstring totals do
not add up, and a handful of generated docstrings are wrong or self-duplicating.

Reviewer: r7-packet-06. Branch `r7/packet-06`, base `9552305f`, merge `681bd906`
(`681bd906^2` = `e2a5867e`). Head compared against: `39f1d12b`. Later branches touched three of the
fifteen files (`EmbeddedArcs`, `RankThreeModel`: 1 line each, no docstring change;
`TransvectionReduction`: round-8 rename `MorseCancellation.*` → `Matrix.*`, commit `93781a7c`); all
checks below were made on the branch head `681bd906^2` unless stated.

## Findings

1. **[wrong receipt] "6 universe pins generalised" and "6 `: Type` binders widened" are the same
   six edits, counted twice.** The base `TransvectionReduction.lean` contains no explicit universe
   pin (`grep -nE '\.\{|Type 0'` on `9552305f:Lib/LinearAlgebra/Matrix/TransvectionReduction.lean`
   is empty); the only universe-related change in the whole branch diff is
   `{A : Type}` (×3), `{H : Type}`, `{H K : Type}` (×2) → `Type*` in commit `81255bfb`. The receipt's
   per-file row puts these six under *both* "pins generalised" ("6 declarations generalised (see
   table below)") and "binders widened" ("6 binders … → `Type*`"), and the Totals line then
   reports "**6 universe pins generalised** (all in `TransvectionReduction.lean`), **6 `: Type`
   binders widened**" as if twelve changes were made. The coordinator's summary ("6 pins lifted /
   1 forced, 6 binders widened") inherits the error. Correct figures: 0 pins generalised, 6 binders
   widened, 1 pin recorded as forced.

2. **[wrong receipt] Docstring counts.** (a) `TransvectionReduction.lean`: receipt says "9 (1/10
   before)"; the base file has 0 declaration docstrings (only the `/-!` module docstring) and the
   commit adds 10 — the commit message itself says "document 10 declarations". The packet's
   "docstrings 1/10" was an audit error that the receipt copied rather than corrected.
   (b) The per-file column sums to 392 (with 9) or 393 (with 10); the bold total says **395**.
   Counting genuinely new `/--` blocks in the branch diff: 88+121+160+4+1+1+2+3+10+2 = 392
   (`FreeGroupGeneratorCokernel`: 2 new + 1 rewritten, reported as 3). No combination of the
   receipt's own numbers gives 395.

3. **[docstring] Four docstrings repeat their own sentence verbatim** (unreviewed generation):
   `FrameField.lean:1865` (`TubularBigon.rankThree_corner_sheet_charts_coincide`),
   `FrameField.lean:2233` (`StripNormalData.bijective_tubularTransitionDerivative`),
   `RankThreeModel.lean:1051` (`StripNormalData.retimedDomain_contains_center`),
   `RankThreeModel.lean:1358` (`TubularBigon.RankThreeTangentAdaptedChart.shearedCoordinates`).
   E.g. line 2233: "The transition derivative is bijective, being the derivative of a transition
   between two charts. The transition derivative is bijective, being the derivative of a transition
   between two charts." Found by a scan of all 379 docstrings in the four documented files for a
   repeated sentence; these are the only four. Fix: delete the second sentence in each.

4. **[docstring] Wrong hypothesis.** `EmbeddedArcs.lean:496`
   `/-- For `0 < r`, the collar cut off by the contraction is compact. -/`
   `theorem WhitneyPairModel.isCompact_innerBigonCollar {h r : ℝ} (hh : 0 < h) (hr : r ≠ 0) : IsCompact (innerBigonCollar h r)`.
   The statement assumes `0 < h` and `r ≠ 0`; the docstring states `0 < r` (not assumed) and omits
   `0 < h`.

5. **[docstring] Over-claim / omitted hypotheses.** `EmbeddedArcs.lean:3155`
   `ManifoldMorse.MorseSurgeryData.nonempty_belt_tubularBigon`: docstring says "a clean bigon
   boundary between an *embedded* two-sphere and the belt sphere bounds a tubular bigon"; the
   statement takes only `g : C(Hemisphere.Sphere 2, d.UpperLevel)` with `ContMDiff … g` — no
   injectivity or immersion hypothesis (contrast line 306, whose statement does carry `_hinj`,
   `_hi`, `_ht`) — and additionally requires `[CompactSpace M]` and `hnull : ∀ g : C(Sphere 1,
   d.LowerLevel), ∃ q, g.Homotopic (const q)` (lower level has null-homotopic circles), neither
   mentioned. Should say "a smooth two-sphere" and name the null-homotopy hypothesis.

6. **[docstring] / [wrong receipt] The stated reason for the forced pin is wrong, although the
   conclusion is right.** `FreeGroupGeneratorCokernel.lean:143` and the receipt say the single
   universe of `freeGroupGeneratorCokernelEquivGroupHomologyH0 {S B M : Type u}` is "forced by
   Mathlib's `Rep` (hence `groupHomology`), which put ring, group and module in one universe". In
   this Mathlib, `structure Rep (k : Type u) (G : Type v)` with carrier `V : Type w`
   (`Mathlib/RepresentationTheory/Rep/Basic.lean:30`, `Rep.of : Rep.{w} k G` line 62) is
   three-universe polymorphic. What forces the pin is `groupHomology`, declared under
   `variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)`
   (`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean:122`). The pin is genuinely
   forced for a statement about `groupHomology (Rep.of rho) 0`; the docstring should name
   `groupHomology`, not `Rep`.

7. **[citation] Brown chapter numbers are approximate at best.** (i)
   `SemidirectProduct.lean` / `GroupExtension/Abelianization.lean`: "[Brown], Ch. II (the
   low-degree Lyndon–Hochschild–Serre sequence gives `H₁(K ⋊ Q) ≅ H₁(Q) ⊕ (H₁(K))_Q`)". In Brown,
   *Cohomology of Groups*, the LHS spectral sequence and the five-term exact sequence are Ch. VII
   §6 (Cor. VII.6.4); Ch. II contains `H₀`, `H₁ = Gᵃᵇ` and Hopf's formula but no LHS. The receipt
   copied the audit's "Ch. II Ex./LHS in low degree" without checking. (ii) `FreeGroupCoinvariants`
   / `FreeGroupGeneratorCokernel`: "II.3 (coinvariants presented by a set of generators;
   `H₀(F(A); M) = M_F`)" and "II.3 (the beginning of the free resolution of ℤ over ℤF)". In Brown
   co-invariants are II.2, `H₀(G, M) = M_G` is III.1 (homology with coefficients), and the free
   resolution `0 → ⊕_S ℤF → ℤF → ℤ` for a free group is I.4 (Example 3); II.3 is the definition of
   `H_*G` with trivial coefficients. I am confident about (i); for (ii) I am confident that
   coinvariants are II.2 and the free-group resolution is in Ch. I, less sure of the exact
   example number. (iii) `ExteriorProductCoordinates.lean`: "Bourbaki, A III §8.5 (multiplication
   in the exterior algebra of a free module on a basis)". In Bourbaki *Algebra* Ch. III, the
   exterior algebra of a free module and the product formula `e_H e_K = ±e_{H∪K}` are §7.8; §8.5
   is "Minors of a matrix" (which is the right citation for `MatrixCoordinates`'s compound matrix).
   Moderately confident. Hatcher §1.3 / Prop. 1.39, Milnor §§5–6 (Whitney lemma, Thm. 6.6) and §7
   (Thm. 7.6, basis theorem — the Euclidean column reduction is the algebraic step of its proof),
   Horn–Johnson §0.8.7 (Cauchy–Binet) are correct topics as far as I can tell.

8. **[incomplete] Things the other receipts record that this one does not.** (a) No
   "declarations documented / total" per file (RECEIPT-05 style); I computed it: EmbeddedArcs
   88/88, FrameField 121/121, RankThreeModel 160/160, TransvectionReduction 10/10 — full coverage,
   but the receipt does not say so. (b) The envdiff summary line reports "lost 8 added 8" auxiliary
   constants; the receipt names none of them and says nothing about them (the other receipts with
   non-zero auxiliary counts list or characterise them). The dumps are not committed, so this
   cannot be reconstructed. (c) `ExteriorProductCoordinates` and `ReindexedCoordinates` are listed
   under "citations replaced" but nothing was replaced there — a `## References` block was added
   (the receipt's own Totals count only 9 files, so the totals are right and the table column is
   mislabelled). (d) The three Whitney module docstrings already cited Milnor §§5–6 before the
   branch; the actual change is deletion of the provenance/family-list/"Twin: no Mathlib
   counterpart" paragraphs and a prose rewrite. The "Twin" information (no Mathlib counterpart)
   was dropped rather than kept; the receipt does not say so.

9. **[nit]** The `[text][brown1982]`, `[hatcher02]`, `[milnor65]`, `[bourbaki1989]`,
   `[horn_johnson2012]` link keys dangle: the repository has no `.bib` file at `39f1d12b`
   (`git ls-tree -r 39f1d12b | grep -i '\.bib'` empty). Repo-wide convention (62 Lib files use
   `[hatcher02]`), not specific to this packet.

## Claims checked

| claim | status | how |
|---|---|---|
| 15 files worked, 16 commits (15 + receipt), one commit per file | verified | `git log --oneline 9552305f..681bd906^2`; `git diff --stat` — 15 `.lean` files + receipt, each commit touches one file |
| Commit messages describe the commit | verified | read all 16 subjects against per-file diffs; only discrepancy is receipt "9" vs commit "document 10 declarations" (finding 2) |
| Docstrings added: 88 / 121 / 160 (Whitney) | verified | `grep -c '^\s*/--'` before (0) / after / at head; declaration counts 88/121/160 → 100% coverage |
| 4 docstrings `SemidirectProduct`, 1 `ExteriorProductCoordinates`, 1 `MatrixCoordinates`, 2 `MinorCoordinates`, 3 `ReindexedCoordinates` | verified | `+/--` lines in branch diff per file |
| `TransvectionReduction` "9 (1/10 before)", total 395 | refuted | see finding 2 |
| "6 universe pins generalised" | refuted | no pin existed; the six edits are the binder widenings (finding 1) |
| 6 `: Type` binders → `Type*` in `TransvectionReduction` | verified | branch diff: `classCoordinateMatrix`, `_mulVec`, `_surjective`, `functional_class_row_surjective`, `transported_classes_of_matrix_product`, `functional_rows_of_matrix_product`; statements otherwise identical, no hypothesis added |
| "0 of N counted: already polymorphic" for 10 files | verified | grepped every `: Type` binder at head in the 15 files: all are `Type u`/`Type v`/`Type w`/`Type uG…`/`Type v₁`/`Type v₂`/`Type*`; no bare `Type` remains except the forced `{S B M : Type u}` |
| Forced pin `{S B M : Type u}` for the `H₀` statement | verified (reason misattributed) | Mathlib `groupHomology` variables `{k G : Type u} (A : Rep.{u} k G)`; `Rep` itself is `(k : Type u) (G : Type v)`, carrier `Type w` (finding 6) |
| Envdiff: 6 source changed types = the six widened declarations | verified | branch diff; also present in `Lib/reports/round-7/envdiff-merged-d950428a.json` under `changed_type_proof_naming` / `changed_type_all` |
| `classCoordinateMatrix.eq_1` changed type | plausible, not elaborated | equation lemma of a def that gained a universe parameter |
| `canonicalMiddleMatrix.eq_1` changed type, `canonicalMiddleMatrix` itself unchanged | verified (structurally) | `681bd906:Lib/Geometry/Manifold/Morse/CutTransport.lean:178-182`: body is `classCoordinateMatrix B (fun j => middleSectionClass (γ j))`, binder `{M : Type}` untouched by this branch; both `eq_1` names are in the merged `changed_type_all`, neither in `changed_type_source` |
| 0 source declarations lost / added | verified for source | merged envdiff `changed_type_source` empty; no `-theorem`/`-def` lines in the branch diff |
| "lost 8 added 8" auxiliary | not verifiable | dumps not committed (finding 8b) |
| Citations replaced in 9 files (8 module docstrings + `ColumnKernel` 1 module + 4 declaration) | verified | branch diff: manuscript/provenance text removed in EmbeddedArcs, FrameField, RankThreeModel, ColumnKernel, MatrixCoordinates, MinorCoordinates, TransvectionReduction, FreeGroupCoinvariants, FreeGroupGeneratorCokernel |
| `ColumnKernel`: ℤ-only statements and spurious `[Module ℤ (A × B)]`, `[Module ℤ (ker F)]` left untouched | verified | diff context lines 56-77 still carry them; statements unchanged |
| `FiberFrameCentralizer` not renamed, `MorseCancellation.*` names kept, `import Mathlib` kept | verified | `git diff --stat` shows no rename; branch file still `import Mathlib`; (round 8 later renamed `MorseCancellation.*`, commit `93781a7c`) |
| Names cited in new module docstrings exist | verified | `finBasis_wedge_of_(not_)disjoint`, `permOfDisjoint`, `toMatrix_map`, `finCoordinates_map`, `toMatrix_map_reindexed`, `reindexedFinCoordinates_map`, `reindexedFinMatrix`, `primitive_row_has_unit_after_column_additions`, `mul_transvection_list_surjective`, `coinvariants_ker_eq_freeGroupGeneratorRelations`, `freeGroupGeneratorCokernelEquiv*`, `Splitting.semidirectProductMulEquiv`, `fundamentalGroupToMulOpposite_surjective`, `TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs`, `TubularBigon.exists_rankThree_relative_cancellation` — all present at `681bd906^2` |
| Hygiene: no `sorry`/`axiom`/`maxHeartbeats`/`unsafe`/`native_decide`/`@[simp]` change/`noncomputable` added/`private` removed | verified | grep over `git diff 9552305f 681bd906^2 -- '*.lean'` for `^[+-]` lines: empty |
| Trailers on every commit | verified | `Co-Authored-By` + `Claude-Session` present on all 16 |
| No `import Hopf` in `Lib/` | verified | `git grep 'import Hopf' 39f1d12b -- Lib/` hits only `Lib/docs/*.md` prose |
| Builds (`lake build Lib`, `Solution …`, `AxiomAudit`) | not verifiable | no logs committed; consistent with the fully built integration copy existing at head |

### Docstrings sampled (55; those not listed under Findings check out)

*Whitney files, every 10th docstring (offset 3) plus every 25th (offset 11), statements read in
full:* EmbeddedArcs 79 `normalJacobian_mul_chartDet`, 306 `opposite_beltIntersectionSigns_iff_Whitney_corners`,
424 `innerBigonMap_one`, 496 (finding 4), 1139 `exists_weighted_immersive_patch_with_property`,
1269 `common_kernel_preserved_on_zero_set`, 1486 `fderiv_endpointFunction` (checked against
`endpointFunction t = t (1 - t)`), 1915, 2207, 2226 `exists_clean_strip_matching_local_germs`,
3155 (finding 5), 3408, 3434; FrameField 55 `hasDerivAt_upperBoundaryArc` (checked against
`upperBoundaryArc h t = (2t-1, h(1-(2t-1)²))`), 157, 185 `upper_sheetDifferential_arc`, 311, 398,
429 `jointBlock_apply`, 659 `upper_sheetFrame`, 951, 1169 `eq_det_smul_id_of_finrank_one`, 1193,
1493, 1842, 1883 `rankThreeSheetPairDet_eq` (factor `8h(2t-1)` matches), 2044
`opposite_intersectionDet_iff_normalDet`, 2233 (finding 3), 2386 `normalDetector_comp_sheet_eq_zero`,
2451 `opposite_rankThree_corners_iff_normal_sheet_determinants`; RankThreeModel 56, 242, 267, 361,
498, 515, 559, 604, 937, 951, 1040, 1216, 1249, 1316, 1553, 1713, 1750, 2014, 2286, 2367, 2592, 2855.
*Group theory / exterior powers / matrices, all new or rewritten docstrings read:* the 4
`abelianizationMulEquiv_*` simp lemmas (product order `Abelianization Q × coinvariants`, `Q`
acting on `Abelianization K` through `φ` — matches `H₁(Q) ⊕ (H₁ K)_Q`), the 2
`FiberFrameCentralizer` theorems (points `e` and `h • e`, `fiberEquivGroup e e'` — direction
correct), the 3 `FreeGroupGeneratorCokernel` docstrings (`Pi.single a (…)` family matches),
`coe_wedge`, `finCoordinates_apply`, `sortedSubsetFintype`, `sortedSubset_card`, the 3
`ReindexedCoordinates` simp lemmas, all 10 `TransvectionReduction` docstrings (conclusions of
`functional_class_row_surjective`, `transported_classes_of_matrix_product`,
`functional_rows_of_matrix_product` read in full; the `∑ i, P i j • v i` and row-times-`P`
descriptions are correct), the 4 rewritten `ColumnKernel` docstrings (`(a, -e.symm (f a))`
matches). Module docstrings: `ExteriorProductCoordinates` sign convention (`permOfDisjoint` is the
shuffle relating the concatenated enumerations to the enumeration of the union — matches),
`FreeGroupGeneratorCokernel` (`ρ(x⁻¹)-1` and `ρ(x)-1` same range — correct), `EmbeddedArcs`
("ambient dimension at least five" — `5 ≤ Module.finrank ℝ E` does occur 4×).

## Not checked

* The packet's own `envdiff.json` and the two dumps (`dump_base.jsonl`, `dump_after.jsonl`) are
  not in the repository; I could not confirm "lost 8 added 8" or that exactly these 8 names
  changed type in isolation. I used the merged `envdiff-merged-d950428a.json`, which mixes all
  ten packets.
* No elaboration was run (nothing in this branch changes a statement beyond `Type` → `Type*`,
  which the diff shows directly); the `eq_1` explanations were checked structurally only.
* Build lines in the receipt: unverifiable, no logs.
* The remaining ~320 Whitney docstrings outside the 55 sampled.
* Textbook section numbers were checked from memory (see finding 7 for confidence levels); I did
  not have the books.

## Tool notes

* Receipts should be forbidden from listing the same edit under two work items; a per-file
  "before → after" count per item (as RECEIPT-01 does: "pins 23 → 0", "binders 10 → 1") would
  have made the double count impossible to write.
* The per-packet `envdiff.json` should be committed next to the receipt (as `names/` and
  `preamble/` did); the auxiliary lost/added names should be listed whenever non-zero.
* A trivial lint for repeated sentences inside a docstring would have caught finding 3 before
  merge; a "docstring mentions a hypothesis the statement does not have" check is harder, but a
  reviewer prompt of "list every hypothesis of the statement, then compare" would catch finding 4.
* The receipt copied the audit's numbers ("1/10", "Ch. II") without re-deriving them; receipts
  should state which packet inputs were found to be wrong rather than repeat them.
