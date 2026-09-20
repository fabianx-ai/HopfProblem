# Fresh-reviewer pass over rounds 7 and 8 (2026-09-21)

Twenty-one independent reviewers (Claude Fable 5.1, no prior context, one receipt each, read-only;
brief in `Lib/reports/review-7-8/BRIEF.md`) over the twelve round-7 receipts, the seven round-8 branch
receipts, the round-8 merge receipt, and the two coordinator reviews with the round-7 merged-head
environment diff. Reviews in `Lib/reports/review-7-8/<id>.md`, each with a claims table, a "not checked"
list and tool notes. Head reviewed: `39f1d12b`.

## 1. Verdicts

All twenty-one: **ACCEPT WITH FINDINGS**. No reviewer found a weakened statement, an added hypothesis, a
lost declaration without a twin whose content is gone, a `sorry`/`axiom`, or a merge that dropped a line
from either parent. What they found is in the receipts, the docstrings and the citations, not in the
mathematics: hand-typed counts that disagree with the receipts' own tables, "not done, because …" reasons
that do not survive an elaboration, docstrings that state the wrong hypothesis or the wrong adjoint,
textbook numbers copied from the audit without checking, and evidence claimed that is not in the tree.

| receipt | reviewer file | headline |
|---|---|---|
| r7/preamble | `r7-preamble.md` | `autoImplicit` is **on** in 221 of 446 `Lib` files, all 96 minimised ones included; compile-success was therefore not evidence that a dropped `open scoped` was unused (an identifier-like scoped token becomes an auto-bound implicit); the envdiff caught the one case (`SquareRoot`, `ω`). Removing `maxSynthPendingDepth` also changed definition *bodies* (`CrossProduct.lean` `_proof_n` churn, benign), which the receipt filed as notation artifacts. Four restored files verified. |
| r7/names | `r7-names.md` | `Contragredient.lean`: five declarations deleted with no twin, and `contragredient`'s named twin `Representation.dual` has a different type (linear maps, not equivalences); no consumers, but INTEGRATION-7's "true Mathlib duplicates" is wrong for this file. `AddCommGroup.lean` reason misstated (`Sheaf.H` is an `abbrev`; the instance is load-bearing for another reason, see dfiles-c). Cherry-picks reproduce their originals byte-for-byte but carry no `(cherry picked from …)` line. |
| packet 01 | `r7-packet-01.md` | Two references shipped with literal placeholders: "Weibel, Exercise 1.3.x" (`CochainTransgression.lean:27`) and "Exercise 2.4.x" (`ExactFunctorComparison.lean:27`). Pin counts 116/27, not 119/24. Generators envdiff row explained by the wrong declaration. `moduleDual`/`dualComplex` land in `max u w`, unstated. Two docstrings loose (`rectangleHorizontalVertical` says the opposite of the file's convention). |
| packet 02 | `r7-packet-02.md` | Two "forced" claims refuted by elaboration: `Coproduct.singularChainsFiniteBiproducts` lifts with `Abelian.hasFiniteBiproducts` (one token, two places); the `AddCommGrpCat.{0}` coefficient pins in `PositivePrimitives`/`Vanishing` are not forced by the cochain interface (packet 01 lifted it) and three of them restate at `.{w}` with identical proofs. Totals row wrong (103 of 134, 31 left). 63 docstrings checked, none wrong. |
| packet 03 | `r7-packet-03.md` | `neighborhoodCohomologyEquiv_symm_apply` docstring says "inverse to the forward comparison" where the statement says it *is* the forward comparison (`rfl`). Weibel 2.4.6(a)/(b)/(c) lettering and "Theorem" vs "Definition" 2.5.1 inconsistent. `CanonicalPositiveCofinalExt.lean` silently skipped. Forced-by claims were true at base and stale at the merge. |
| packet 04 | `r7-packet-04.md` | `exists_clean_two_sheet_arc` documented as "two disjoint surfaces"; the theorem has no disjointness hypothesis. Six `: Type` binders in `AdaptedWindows.lean` neither widened nor listed. Hirsch "Ch. 8" (Isotopy) cited for immersion theorems; Godement II.1.1 for a stalk criterion it does not state. The +1 auxiliary never named. |
| packet 05 | `r7-packet-05.md` | Comment-stripped sources byte-identical before/after (docstrings only). `cornerScale` docstring inverts the geometry ("nearer corner"; it is the far one). `CleanBigonBoundary` overstates its clean clause. Milnor TDV §7 cited for `π_m(Sⁿ)=0`, which is §§2–3. |
| packet 06 | `r7-packet-06.md` | The six `Type` → `Type*` widenings counted twice (as pins and as binders); 0 pins existed. Four docstrings repeat their own sentence verbatim (`FrameField.lean:1865,2233`, `RankThreeModel.lean:1051,1358`). `isCompact_innerBigonCollar` docstring states `0 < r` (not assumed), omits `0 < h`. Brown "Ch. II" cited for LHS (it is VII.6); Bourbaki §8.5 for exterior products (§7.8). |
| packet 07 | `r7-packet-07.md` | Three manuscript labels survive: `(C13)`, `(C14)` in `CochainSheafResolution.lean:1009,1042`, `(C8)` in `Cech/DegreeZero.lean:699`; "receipts" jargon at `CubeBoundaryThreeDimension.lean:261`. Hatcher Ex. 1.22 and Weibel Thm 2.4.6 doubtful. Header counts off by small amounts. `pushforwardAdditive` lift verified by elaboration. |
| packet 08 | `r7-packet-08.md` | Headline numbers wrong (108/226/35 and section counts 100/133, not 118/217/33/92/141) and propagated into the commit message and INTEGRATION-7. The five `ConstantProduct*`/`ConstantSheafH1` files were attributed to `pullback` as forcer; round 8 lifted `pullback` and they stayed pinned (real forcer: `SingularCochains.chains`). One `(C24)` survives at `Cech/LongExact.lean:47`. Five lifts re-elaborated at `u = 0` against the base signatures: identical. |
| packet 09 | `r7-packet-09.md` | `OpenEmbeddingCohomology.lean:79–89`: both adjunction docstrings name the wrong adjoint (the `OpenRestriction.lean` pair is right). Hartshorne "III Prop. 2.4" does not exist; III Ex. 4.1/8.2 are scheme exercises cited for a topological fact (Ex. 8.1 is the one); Bredon III "Prop. 1.1" and "Thm. 1.1" both cited; KS "2.3.?" filled in as 2.3.6 without evidence. Forced-by lists omit the files' own chokepoints, which round 8 had to rediscover. |
| packet 10 | `r7-packet-10.md` | The +1 constant is `unit._proof_1`, not `sheafification`'s. One of `PrimitivesH1`'s "14 forced" pins is not forced. `Vanishing.lean` module docstring says "paracompact" where the theorems need `[MetrizableSpace X]`. Stray blank lines inside four signatures. Probe: for every file that sheafifies, `A : AddCommGrpCat.{0}` is forced by `X : Type` through Mathlib's `HasWeakSheafify` universe constraint, so the coefficient pins are forced even after packet 01's lift. |
| r8/pins | `r8-pins.md` | Counts 1,024/99 → 320/48 reproduced. Whole-diff residue check: after normalising universe annotations, the only residue is `universe u` lines, seven `(C := AbelianSheaf Y)` and one docstring word, so every `u = 0` instance is the old statement. Chokepoint 8's mechanism is misstated: bare `{X : TopCat}` binders elaborate polymorphic; what pinned `germ_stalkIso_hom_nearbyRestrictionUnit` is `TopCat.Presheaf.germ`'s `[HasColimits AddCommGrpCat.{?v}]` argument, resolved with `?v := 0` while still a metavariable. §3's `ULift ℤ` obstruction is real *and* a protocol obstruction (no `ModuleCat.{u} ℤ` object has carrier literally `ℤ` for `u > 0`); the clean route is a new polymorphic `chains` beside the pinned one plus a `u = 0` comparison, an addition. §3 counts 26/271/8 are 32/280/9. |
| r8/dup-sheaf | `r8-dup-sheaf.md` | All 28 deletions checked one by one; nine `_one` twins are literally the `n = 0`/`n = 1` instances (by `example`), none carries `[MetrizableSpace X]`; the three unifications are `rfl`. Five `PROOF-NAMING` names in the envdiff, receipt explains two. `AxiomAudit.lean` edit (119 lines) unmentioned. `GlobalUnitPredicates.lean` docstring names the wrong module for one predicate. |
| r8/dup-hom | `r8-dup-hom.md` | 17 ported van Kampen statements token-identical modulo `Cocone.` and line wrapping; proofs byte-identical. Table B names a wrong twin for `CoverNaturality.smallConnecting_naturality` (the named one has six extra hypotheses and is about a different map); the true twin is `SingularMayerVietoris.connectingMap_naturality` at `chainSequenceMapOfMapsTo`, from which the reviewer re-proved the deleted statement in one term. Monolith is 1,810 lines, not 1,823. The blocker for the degree-one lemmas (`GlobalUnitH1Criterion.lean`) was deleted by dup-sheaf later in the round, so those can now go. Item-2 refusal (pre-PR chain tower) judged right. |
| r8/dfiles-a | `r8-dfiles-a.md` | `split-*.json` covers every declaration of the base files (sha256 per unit verified); closure claims 96/115 and 120/143 recomputed exactly from the base dump. Counts: Belt 42 remain, not 40; MinimalSystem had eight importers, not seven; CutTransport 42 vs envdiff 52 = ten structure projections, unreconciled. Merge-time edit in `Hopf/Proof/…/MiddleBlocks.lean` (a `moved` rename) not in MERGE.md. |
| r8/dfiles-b | `r8-dfiles-b.md` | `fibre_constant_of_ker_le` deleted with no named twin (the "twin" is a subtype packaging, not a declaration; no Mathlib lemma of that shape; four-line content, no consumer). Mathlib file for `liftOfSurjective` is `Subgroup/Basic.lean`, not `Ker.lean`. All seven moves verbatim and judged project-specific; extracted islands stand alone. Stock `Hopf/Recognition.lean` now imports `Hopf.Proof` (unmentioned). |
| r8/dfiles-c | `r8-dfiles-c.md` | The instance `instAddCommGroupH` is load-bearing, confirmed by `#synth` — but the stated cause ("resolution does not see through `Sheaf.H`", "upstream change to `Sheaf.H`") is wrong: with a site-typed `CategoryTheory.Sheaf` the Mathlib instance fires; the gap is Mathlib's `TopCat.Sheaf` being a non-reducible `def` (making it locally reducible also fixes it). "Remain axiom-audited transitively" is false: `#print axioms` follows dependencies, not imports; the four moved theorems are probed by nothing. Two Mathlib file attributions in new docstrings wrong. `SphereTwo` placement under `Hopf/Proof` judged right. `w4-w1-solution` imports the old module path and will need a reroute. |
| r8/moved | `r8-moved.md` | All 34 renames exact, both splits partition their sources. Item 3's "docstrings were added on this branch's base" is false: `LocalContributionsNaturality.lean` has 0 docstrings at base and at head. Duplicate `import` lines left in `Lib.lean` (×3), `Hopf/Recognition.lean`, `SurgeryCollapse.lean` by a commit whose message names none of them. `LinearEquiv.coordMatrix` equals `(Basis.ofEquivFun B.symm).toMatrix v` (Mathlib twin); `Fin.tailHeadAddEquiv` is `rfl` to a Mathlib composite. `SimplyConnectedSpace` refusal right. |
| MERGE | `r8-merge.md` | All seven merges replayed with `git merge-tree`; the committed trees differ from the auto-merge only in the conflicted files plus the disclosed CutTransport fix — nothing from either parent dropped. `envdiff.py` re-run reproduces `envdiff.json` field for field; 221 lost names all attributed (sub-counts 170 A + 2 D, not 171 + 1); the 127 breakdown's parenthetical sums to 88, not 99. Merge commit `5ad9ec3c` carries three `d-files-{a,b,c}.md` files from no branch. Six `dfiles-a` rename lines inert (wrong direction). "Abbreviation of its survivor" too strong for two `FunctionSheaf`/`topEvaluation` respellings; `rfl` holds. |
| INTEGRATION-7/8, merged-head envdiff, NEXT_STEPS | `r7-merged-head.md` | The merged-head "PASS" with 1,028 `PROOF-NAMING` names is necessary, not sufficient, evidence of statement preservation: the class means the `Lib`-internal `uses` set is unchanged, which an added `[MetrizableSpace X]` or a weakened conclusion naming only Mathlib constants also satisfies (demonstrated on a two-row table). Mitigation: 120 of the 1,028 sampled, headers identical modulo universes; none of the 74 binder widenings reuses an existing universe parameter. Two INTEGRATION-7 cells misquote (packet 01 "407" is 314 source; packet 03 "61" appears nowhere). "MinimalSystem deleted" in INTEGRATION-8 is a move. NEXT_STEPS omits several receipt "left" items (§3 below). |

## 2. Cross-cutting

1. **Nothing unsound.** Twenty-one reviewers, ~600 docstrings read against statements, all 28 + 251 + 3
   deletions twinned by name, the merges replayed mechanically, the universe lifts residue-checked over
   the whole round-8 diff: the library after rounds 7 and 8 proves what it proved before, and the twins
   are the same or stronger except where a reviewer says "definitionally equal" (three respellings, all
   `rfl`). The one deletion class with no twin is dead code with no consumer (`Contragredient` ×5,
   `fibre_constant_of_ker_le`).
2. **Receipts are worse than the work.** Every round-7 packet receipt has at least one number that
   disagrees with its own per-file table, and two headline figures propagated into commit messages and
   INTEGRATION-7. Reasons given for "not done" were wrong or incomplete in six receipts (packet 02 ×2,
   packet 08, packet 10, names, dfiles-c) even where the conclusion was right. Fix: totals computed
   from tables by script; "forced by X" must quote X's signature and name the binder; "not done" must
   ship the one-file reproduction.
3. **Evidence claimed but not in the tree.** None of the ten packet receipts committed its `envdiff.json`;
   reviewers reconciled against the merged file instead, which cannot attribute downstream changes to a
   packet. Round 8 committed them and those reviews were the cheapest to do.
4. **Docstrings and citations are where the model errs.** Wrong hypothesis (packet 04, 06), wrong
   direction/adjoint (packet 03, 09), inverted geometry (packet 05), self-repetition (packet 06 ×4),
   placeholders (packet 01 ×2), manuscript labels surviving (packet 07 ×3, packet 08 ×1), and about
   fifteen textbook item numbers copied from the audit's twin column without checking (Hartshorne III
   "Prop. 2.4", Ex. 4.1/8.2; Brown Ch. II; Bourbaki §8.5; Weibel 2.4.3/2.4.6 lettering; Bredon III
   1.1 ×2; Milnor TDV §7; Hirsch Ch. 8; Godement II.1.1/II.3.1/II.4.3). The number of wrong docstrings
   found is about fifteen in ~600 read, i.e. 2–3 %, concentrated in prose glosses of formulas.
5. **Two tool findings corrected.** (a) `autoImplicit` is on in half of `Lib` (no `leanOptions` in
   `lakefile.toml`); the brief's and the preamble receipt's premise was wrong, and any compile-based
   minimisation must set it off first. (b) The "invisible pin" is not a bare-binder effect but an
   instance argument resolved at a universe metavariable (`germ`'s `HasColimits`); a `.{0}` grep
   census cannot find it, `#check` with `pp.universes` can. Both go to `lean-agent-ide` (`spec/dump.md`
   corrected in the tool repo).
6. **`envdiff`'s `PROOF-NAMING` class is misnamed and under-powered** (two reviewers independently):
   it should hash the type with universes instantiated at 0 and include Mathlib constants in `uses`, so
   a pure lift verifies mechanically and a hypothesis change is a distinct class. Until then the
   per-packet receipt is the evidence, and the merged-head PASS is a consistency check only.
7. **Axiom probes.** The four moved `SphereTwo` theorems are probed by nothing (dfiles-c's "transitively"
   reason is false). Standing rule proposed by two reviewers: a move to `Hopf/Proof` carries its
   probes to a `Hopf/Proof/AxiomAudit.lean`; four lines, not an owner decision.

## 3. Fix list (mechanical, one commit each, from the reviews)

Code and docstrings:
- packet 01: replace "Exercise 1.3.x" / "2.4.x" (`Ext/CochainTransgression.lean:27`,
  `Ext/ExactFunctorComparison.lean:27`); Weibel "Theorem 2.4.3" → Exercise 2.4.3 or Hartshorne III.1.2A
  alone (three files); `rectangleHorizontalVertical`/`VerticalHorizontal` docstrings.
- packet 02: lift `Coproduct.lean`'s two biproduct instances via `Abelian.hasFiniteBiproducts`, then the
  seven abstract pins; restate the `PositivePrimitives`/`Vanishing` coefficient lemmas at `.{w}`.
- packet 03: `neighborhoodCohomologyEquiv_symm_apply` docstring; Weibel 2.4.6/2.5.1 citations;
  `CanonicalPositiveCofinalExt.lean` module docstring.
- packet 04: `exists_clean_two_sheet_arc` docstring (+ module bullet); six `AdaptedWindows.lean`
  binders (widen or record); Hirsch Ch. 8 → Ch. 2–3; Godement II.1.1 → drop.
- packet 05: `cornerScale`, `CleanBigonBoundary`, `CleanStripPatch` docstrings; Milnor TDV §7 → §2.
- packet 06: four self-repeating docstrings; `isCompact_innerBigonCollar` and
  `nonempty_belt_tubularBigon` docstrings; Brown Ch. II → VII.6, II.3 → II.2/I.4; Bourbaki §8.5 → §7.8
  (exterior products); `freeGroupGeneratorCokernelEquivGroupHomologyH0` docstring names `groupHomology`.
- packet 07: `(C13)`, `(C14)`, `(C8)` docstrings; "receipts" at `CubeBoundaryThreeDimension.lean:261`;
  Hatcher Ex. 1.22, Weibel 2.4.6 checks.
- packet 08: `(C24)` at `Cech/LongExact.lean:47`; `basedFibreInclusion_isClosedMap` docstring;
  Hartshorne III Ex. 8.1 → 8.2 in `FiniteClosedPushforward/AcyclicResolution.lean`.
- packet 09: the two adjunction docstrings in `OpenEmbeddingCohomology.lean:79–89` (copy from
  `OpenRestriction.lean`); Hartshorne "III Prop. 2.4" → drop, "Ex. 4.1 / 8.2" → Ex. 8.1, "II Ex. 1.19"
  → drop; Bredon III item numbers; KS 2.3.6 → "cf. §2.3"; `h1Comparison` docstring (hypothesis);
  `SheafificationLocalGerm.lean` `stalkFunctor_map_germ` sentence; `OpenRestriction.lean` module
  docstring (`j_!` vs `j_*`); `DegreeZeroAcyclic.lean` title; `ComparisonPositive.lean` "paracompact".
- packet 10: `Vanishing.lean` module docstring (metrizable); four stray blank lines inside signatures
  (`GlobalUnit.lean:75`, `GlobalUnitPositive.lean:138`, `Presheaf.lean:96`, `Pullback/Sheaf.lean:100`);
  lift the two private `PrimitivesH1.lean:162` homotopy lemmas; `OpenRestriction.lean` "hereditarily
  paracompact" wording.
- names: restate `freeGroup_invariant_iff` in a `FreeGroup` file (audit asked for a move) or record the
  five twin-less deletions explicitly; correct the `AddCommGroup.lean` reason.
- dfiles-c: rewrite the `AddCommGroup.lean` module docstring (cause: `TopCat.Sheaf` non-reducible; two
  Mathlib paths); `SheafificationLocal.lean` reference path (`Sheafify.lean`); add
  `Hopf/Proof/AxiomAudit.lean` with the four `SphereTwo` probes; note the `w4-w1-solution` reroute.
- dfiles-b: record `fibre_constant_of_ker_le` as "deleted, no twin, reason" in the receipt and MERGE.md
  (or re-add it, four lines); Mathlib path `Subgroup/Basic.lean`.
- dfiles-a: `Hopf/Proof/…/CutTransport.lean` docstring inventory (+`passageNormalProduct_det`);
  `RadialFilling.lean` twelve declaration docstrings; Milnor §3 parenthesis.
- dup-hom: table B twin for `smallConnecting_naturality` → `connectingMap_naturality`; retire the
  `_one` cochain lemmas now that `GlobalUnitH1Criterion.lean` is gone.
- dup-sheaf: `GlobalUnitPredicates.lean` docstring (`GlobalUnitSurjective` is discharged in
  `SingularCochainSheaf/GlobalSections.lean`).
- moved: remove the duplicate `import` lines (`Lib.lean` ×2 extra, `Hopf/Recognition.lean`,
  `SurgeryCollapse.lean`); add the seven `LocalContributionsNaturality.lean` docstrings; replace
  `LinearEquiv.coordMatrix` by `Basis.toMatrix` and `Fin.tailHeadAddEquiv` by the Mathlib composite (or
  document the twins); rename `LinearMap.exists_split_of_ker_eq_range`, `LinearEquiv.natAbs_apply_one`
  to say what they are.
- preamble: nothing in the code; the receipt's method section must state the `autoImplicit` fact.

Receipts (counts and wording; one commit for all):
- packet 01 116/27; packet 02 103/134/31; packet 03 binder total; packet 04 80 left; packet 06 0 pins /
  6 binders, 392 docstrings, `TransvectionReduction` 0 → 10; packet 07 62 binders, `AcyclicResolutionH1`
  16, `OverBase` 40 + 22; packet 08 108/226/35 and A/B 100/133 and the `ConstantProduct*` forcer;
  packet 09 317; packet 10 `unit._proof_1`; pins §3 32/280/9, chokepoint-8 mechanism, "proof-text
  edits"; dup-hom 1,810; dfiles-a 42 and 8 importers; MERGE 170 + 2, the 99 residue by module, the
  three `d-files-*.md` in `5ad9ec3c`, `dup-hom`'s four moves, six inert map lines; INTEGRATION-7 cells
  for packets 01 and 03 and "one commit per file"; INTEGRATION-8 "MinimalSystem deleted" → moved.

NEXT_STEPS additions from the receipts' "left" sections that the previous version dropped: the 40 Jev
disagreements and ten low-confidence calls; the remaining project namespaces (`nativeMorseIndex` 226
lines, `NativeTransversality` 86, `ThreefoldGluing` 154, `SpecialPeriods.Threefold.Star` 102,
`MorseCancellation.` 931); dup-hom items 3–6; dup-sheaf items 1–5; dfiles-c `sheaf`/`unit` removal;
moved's `Matrix.Pivot`/`Module.Presentation`/`sheetSum` items; the ~17 unattributed remaining pins.

## 4. Protocol changes adopted from the tool notes

- Every receipt commits its `envdiff.json`/`.txt` beside itself (round-8 rule, now for all rounds).
- Totals are computed from the per-file table; occurrence vs declaration counts are labelled.
- "Not done, because X" ships a scratch file that reproduces X; "forced by X" quotes X's signature.
- Compile-based minimisation runs with `autoImplicit` off.
- A move to `Hopf/Proof` carries its axiom probes to `Hopf/Proof/AxiomAudit.lean`.
- Merge receipts include the `git merge-tree` one-liner per merge; cherry-picks carry
  `(cherry picked from commit …)`.
- Docstring waves get a second pass that re-reads each prose gloss against the unfolded definition and a
  lint for repeated sentences; citations copied from the audit are marked "cf." unless checked.
