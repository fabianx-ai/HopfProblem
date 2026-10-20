# Review of Lib/reports/round-7/packets/RECEIPT-09.md

**Verdict: ACCEPT WITH FINDINGS** — the structural work (77 lifts, 10 binder widenings, 83 added docstrings, 35 commits, no proof changes beyond one disclosed heartbeat bump) checks out against the diff and the environment, but the packet-09 `envdiff.json` was never committed, several textbook citations are wrong or invented, and two adjunction docstrings state the wrong adjoint.

## Findings

1. **[docstring] Both adjunction docstrings in `OpenEmbeddingCohomology.lean` name the wrong adjoint.** Commit `dd08933b`, `Lib/Topology/Sheaves/OpenEmbeddingCohomology.lean` (branch tip l.79–89).
   - `restriction_rightAdjoint : (restriction f hf).IsRightAdjoint` is documented as "Restriction along an open embedding is a right adjoint, namely of the inverse image." Restriction *is* the inverse image `j^*`; its left adjoint (the witness used, `sheafPullbackConstruction.sheafAdjunctionContinuous`) is extension by zero `j_!`.
   - `restriction_leftAdjoint : (restriction f hf).IsLeftAdjoint` is documented as "also a left adjoint, namely of extension by zero." `j^*` is the *left* adjoint of the pushforward `j_*` (witness `sheafAdjunctionCocontinuous`); it is the *right* adjoint of `j_!`.
   The same two declarations in `OpenRestriction.lean` (commit `5294fb3a`, l.180–186) are documented correctly ("right adjoint, namely of extension by zero `j_!`" / "left adjoint, namely of the pushforward `j_*`"), so the OpenEmbeddingCohomology pair should be replaced by that wording.

2. **[citation] `FiniteClosedPushforward/Exact.lean` cites a non-existent proposition for "`f_*` preserves injectives".** Commit `b1b0ab0b`, module docstring and `pushforward_preservesInjectiveObjects`: "(Hartshorne III Prop. 2.4 and its proof)". Hartshorne III has no Prop. 2.4; III **Lemma** 2.4 states "an injective `O_X`-module is flasque" and its proof uses `j_!`, not `f^{-1}`. The adjunction argument "right adjoint of an exact functor preserves injectives" is not a numbered Hartshorne result for `f_*`; it appears for `j^*` in III Lemma 6.1 (correctly cited by `OpenRestriction.lean`).

3. **[citation] `FiniteClosedPushforward/{Cohomology,Composition}.lean` cite scheme-theoretic exercises for a topological statement.** Commits `d13b6f69`, `a657e638`: "`H^n(X,F) ≅ H^n(Y,f_*F)` (Hartshorne III Ex. 4.1 and III Ex. 8.2)". Both exercises are about an *affine morphism of noetherian schemes* and *quasi-coherent* sheaves. The topological statement for sheaves of abelian groups with `R^i f_* F = 0` is III **Ex. 8.1** (Leray). The packet inherited the wrong numbers from the audit's twin column, but the checklist item was to *verify* the reference. Likewise "Hartshorne II Ex. 1.19" for exactness of `f_*` (Exact.lean) is the extension-by-zero exercise (stalks of `i_*` for a *closed embedding*); it covers fibres of size ≤ 1 only.

4. **[citation] Bredon III "Prop. 1.1" and "Thm. 1.1" are both cited; at most one exists.** `GlobalPatch.lean`, `GlobalPatchLocal.lean` (commits `d57007fb`, `540d8ed1`): "Bredon III Prop. 1.1"; `ComparisonH1.lean`, `ComparisonPositive.lean` (commits `1ecc505e`, `c78bd851`): "Bredon III Thm. 1.1". Bredon numbers all statements consecutively within a section, so item 1.1 of III §1 is either a proposition or a theorem. One of the two families is misnumbered (my recollection is that the comparison theorem is III.1.1; the surjectivity/kernel statement is a later item). Similarly "Godement II.4.3" (Flasque.lean) and "Godement II.3.1" (DegreeZeroAcyclic.lean) are cited for the *same* fact (flasque ⇒ acyclic); Godement II §3 is the flasque-sheaf section, II §4 the cohomology section, so at most one number is right.

5. **[citation] A "?" in the audit was filled in with a specific number without evidence.** `OpenRestriction/StalkCriterion.lean` (commit `4cc4b122`): the audit twin says "Kashiwara–Schapira Prop. 2.3.?"; the module docstring now says "Prop. 2.3.6". I cannot confirm that KS 2.3.6 is the stalk criterion for `F ⟶ j_*j^*F`; nothing in the receipt says how the number was found. Treat as unverified.

6. **[incomplete] The packet's `envdiff.json` is not in the repository.** The receipt reports `envdiff.py … --receipt envdiff.json` with 159 changed types, but `Lib/reports/round-7/packets/` contains no envdiff for any packet; only the stage-2 merged `envdiff-merged-d950428a.{json,txt}` exists. I reconciled the receipt's 159-name table against the merged JSON instead (see Claims): every name the receipt lists is present, and the only extras in packet-09-owned modules are auxiliaries (`_proof_*`, `eq_1`, `congr_simp`). The extras in the downstream modules (`ConstantNormalization` +4, `NestedOpenCohomology` +2, `SingularCochainSheaf.OpenRestriction` +1, `Pullback.Sheaf` +2) cannot be attributed to this packet or to packets 07/08 without the per-packet dump.

7. **[incomplete] "Forced by X" names an upstream blocker but omits the file's own pins that were also blockers.** Every named forcer was genuinely `.{0}`-pinned at base `9552305f` and is referenced by the file (verified per file, see Claims), so no attribution is *false*. But:
   - `H1Vanishing/Flasque.lean` ("37 left, forced by `cohomologyAddCommGroup`"): the file's own `private instance abelianSheaf_hasExt : HasExt.{0} …`, `Ext.mk₀.{0}`, `ULift.{0} ℤ` were an independent chokepoint; round 8 had to lift them as a separate item (`f5a50893`).
   - `OpenRestriction/Cohomology.lean` ("27 left, forced by `integralSheaf` / `integralHomGlobalEquiv`"): those two were lifted by packet 08 in parallel, yet the file stayed pinned because its own `freeOpen`, `freeHomEquiv`, `cohomologyEquiv` were chokepoints (round 8 `ccf092a2`). The receipt does not mention them.
   - `OpenEmbeddingCohomology.lean`: `openImage` in this file was itself listed as a chokepoint by round 8 (`6973220d`).
   The receipt's "each forced by an imported interface outside the packet" is therefore not the whole story for these three files.

8. **[docstring] `SingularCochainSheaf/ComparisonH1.lean`, `h1Comparison` (commit `1ecc505e`)**: "For a locally contractible space `X`, the first cohomology group of the constant sheaf `A_X` is isomorphic to … `H¹(X; A)` (Bredon III Thm. 1.1)." The declaration takes `[IsIso (homologyMap (globalCochainComparison X A) 1)]` — the theorem's real content — as a hypothesis; the docstring reads as if the textbook theorem were proved. (The module docstring does say "assumed invertible"; the declaration docstring does not.)

9. **[docstring] `SheafificationLocalGerm.lean` (commit `b5abef44`)**: "(`TopCat.Presheaf.stalkFunctor_map_germ`, which is an isomorphism for sheafification)". `stalkFunctor_map_germ` is an equation lemma; what is an isomorphism is the stalk map of the sheafification unit. Wording is nonsensical as written.

10. **[docstring] `OpenRestriction.lean` module docstring**: "Both facts [exactness and preservation of injectives] come from the left adjoint, extension by zero `j_!`". Preservation of finite *limits* is `infer_instance` from `restriction_rightAdjoint`, i.e. from `j^* ⊣ j_*`, not from `j_!`. Only the injectives half comes from `j_!`.

11. **[nit] `DegreeZeroAcyclic.lean` title now overstates.** Old title "…acyclicity in H¹" was accurate; new title "Acyclicity of the degree-zero singular-cochain sheaf" suggests all degrees, but only `zeroCochainSheaf_h1_subsingleton : Subsingleton (H (sheaf X A 0) 1)` is proved. `ComparisonPositive.lean` module docstring similarly states the textbook hypothesis "paracompact" while the code requires `[MetrizableSpace X]` (the declaration docstring says metrizable, correctly).

12. **[nit] Pin count for `GlobalPatch.lean` is 7 in the receipt; the file has 8 `.{0}` occurrences (6 lines) at base and at the tip**, and nothing was lifted there. So "316 left" should read 317 by the audit's occurrence count. Every other per-file count reproduces.

## Claims checked

| claim | status | how |
|---|---|---|
| 35 commits (34 files + receipt), one commit per file, base `9552305f` | verified | `git log 9552305f..f4c22446^2`; `git show --name-only` per commit: each touches exactly 1 file |
| commit trailers present | verified | all 35 have `Co-Authored-By` and `Claude-Session` |
| 34 module docstrings rewritten | verified | every file in the diff has a `/-!` hunk; SkyscraperSupport's is new |
| 260 docstring blocks in diff, 177 replaced, 83 added | verified | `grep -c '^+/--'`=260, `'^-/--'`=177; per-file net matches the receipt table exactly (13 OpenRestriction, 14 CyclicComponentSections, 9 DegreeZeroFunctions, …) |
| "every public declaration in the 34 files is now documented" | verified (heuristic) | awk scan for `theorem/def/…` not preceded by `-/`: 3 hits, all false positives |
| 77 pins lifted in 8 files, 316 left | partly | occurrence counts: lifted 6+1+1+5+14+12+4+34 = 77 (excluding `Category.{0,u}`); left = 317 (GlobalPatch is 8, not 7 — finding 12) |
| each named forcer was pinned at base and used by the file | verified | `git grep` at `9552305f` for each definition (all `TopCat.{0}` / `AddCommGrpCat.{0}` / `Type`); grep of forcer name in each file at tip (all ≥1; `pushforwardAdditive` is an instance used implicitly via `ShortComplex.map`, imported directly) |
| forced pins were the *only* blockers | refuted for 3 files | finding 7; round 8 pins receipt §1 and judgement `chokepoint-pins.md` |
| StalkCriterion blocked by `germ_stalkIso_hom_nearbyRestrictionUnit` (bare `{X : TopCat}` in NearbyRestrictionGerm) | verified | round-8 pins receipt confirms the invisible pin; the receipt's quoted `Sheaf.{0,0,1}` mismatch is the expected symptom |
| lifts keep the `u = 0` statement, add no hypothesis | verified (sample 25) | read all 11 lift/widen hunks in the diff: every change is `.{0}`→`.{u}`, bare `AddCommGrpCat`→`.{u}`, `Type`→`Type u`/`Type*`, `Category.{0,u}`→`Category.{u',u}`; `lake env lean` scratch: `#check … .{0}` for `restriction`, `extension_preservesMonomorphisms`, `stalk_hom_ext_of_cofinal`, `skyscraperBiprodIsoOfTwoPointSupport`, `deckMonodromyHom_translate_range`, `patchedCochain`; `restriction U = U.sheafRestrict` by `rfl` at `u=0` |
| `{G : Type uG} {E X : Type u}` → `{G E X : Type*}` in DeckTranslate | verified | diff l.2357–2360; `#check` shows three independent universes |
| `{E X M : Type u}` cannot become `Type*` in PrincipalCoverLocalSystem | verified (reasoning) | `TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)` ties `X`, `M` and the sheaf universe; the four "binders" are already `Type u` (l.39, 228, 262), none is bare `Type` |
| only proof-side change is `synthInstance.maxHeartbeats 80000` on `extension_preservesMonomorphisms` | verified | grep of added lines for `maxHeartbeats/sorry/axiom/unsafe/native_decide/@[simp]/noncomputable/private/admit`: only that line and two `private` lines whose only change is `.{u}` |
| no `sorry`/`axiom`; axiom audit clean | verified (sample) | `#print axioms` on 7 generalised declarations: `propext, Classical.choice, Quot.sound` only |
| no `import Hopf` in `Lib` | verified | `grep -rn "import Hopf" Lib/` hits only `Lib/docs/*.md` prose |
| `open scoped AlgebraicGeometry` dropped in Exact.lean | verified | diff l.162 |
| envdiff: 0 source lost/added, 159 changed types, all listed | partly | no per-packet JSON (finding 6); merged JSON contains every listed name; 100 generalised + 59 downstream = 159 arithmetic checks |
| `## Main results` names exist | verified | `restrict_bijective_of_commuting_component_transport`, `sectionEvaluation`, `stalkEvaluation_bijective`, `cohomologyEquiv_restrict`, `intrinsicOpenClass_restrict`, `restrictionIso` all found at tip |
| Hartshorne II Ex. 1.17 (skyscraper stalks), III Prop. 2.5 (flasque ⇒ acyclic), III Lemma 6.1 (`j^*` preserves injectives), Hatcher Prop. 2.21 (small chains), Hatcher §3.H (local coefficients) | verified | own knowledge |
| Hartshorne III Ex. 4.1 / Ex. 8.2, III Prop. 2.4, II Ex. 1.19 | refuted / not the stated result | finding 2, 3 |
| Bredon III Prop. 1.1 vs Thm. 1.1; Godement II.4.3 vs II.3.1 | refuted (mutually) | finding 4 |
| Hatcher Prop. 1.39 / Spanier 2.6 for "changing the fibre point conjugates monodromy" | partly | Hatcher 1.39 is `G(X̃) ≅ N(H)/H`; the conjugation statement is in the surrounding text of §1.3, not the proposition itself. Spanier 2.6 (covering transformations) is the right section |
| Mathlib names cited (`skyscraperSheaf`, `skyscraperPresheafStalkOfSpecializes`, `skyscraperPresheafStalkOfNotSpecializesIsTerminal`, `isIso_of_stalkFunctor_map_iso`, `stalk_hom_ext`, `stalkFunctor_map_germ`, `stalkPullbackIso`, `sheafifyLift`, `toSheafify_sheafifyLift`, `StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf`) | verified | all used in the file bodies or in Mathlib at v4.33 |
| "Suggestions not carried out" list | verified | none of the listed refactors appear in the diff; no rename/merge/delete |

Docstrings sampled (34 module + 30 declaration docstrings read against their statements): all 34 module docstrings; `cohomologyForward`, `cohomologyEquiv_symm_apply`, `cohomologyForward_equiv`, `pushforwardHom_comp`, `pullback_comp`, `pullback_preservesFiniteLimits`, `pushforward_preservesInjectiveObjects`, `skyscraperAtTopIso`, `sectionsBiprodIso`, `toSkyscraperAt_top`, `skyscraperAt_stalk_isZero_of_ne`, `isIso_stalkFunctor_map_toSkyscraperBiprod`, `restrictionIso`, `restrictionIso_hom_app`, `openImage_cocontinuous` (both files), `restriction_rightAdjoint`/`restriction_leftAdjoint` (both files), `lan_preservesMonomorphisms`, `representingUnit`, `cohomologyEquiv` (OpenRestriction), `nearbyStalkPushforward_isIso`, `globalRestrictionIsoOfIsIsoOutside`, `presheafStalkIso`, `stalkIso_inv_germ`, `globalSectionsEquivInvariantCoefficients`, `CyclicComponentData`, `sectionsEquiv`, `deckMonodromyHom_translate`, `stalkIsoCoefficientAtLift`, `sheafifyPullback_naturality`, `constantCochain`, `h1Comparison`, `constantSheafCohomologyIsoSingular`, `zeroCochainSheaf_h1_subsingleton`, `globalCochainUnit_eq_zero_iff_local`, `patchedValue`, `patchedCochain_restrict_of_compatible`. Wrong ones are findings 1, 8, 9, 10, 11; the rest match their statements.

## Not checked

- The receipt's three `lake build` lines and the `Lib.AxiomAudit` run (would need a build; the head is built and the sampled `#print axioms` are clean).
- The exact error messages quoted for StalkCriterion (l.73 mismatch, `whnf` timeout) and PrincipalCoverLocalSystem (`HasLimitsOfSize…` at l.122, l.218) — not reproduced; the StalkCriterion cause is corroborated by round 8.
- The 59 downstream changed-type entries beyond name presence: without the packet's own dump I cannot confirm that *only* universe arguments moved, nor attribute the extra entries in the merged envdiff (finding 6).
- The audit's `: Type` binder counts (8/18/1/4/2/2/2) — the counting method is not stated; my regex gives different totals, so I did not re-derive "37 left".
- Godement and Kashiwara–Schapira numbering (findings 4, 5) beyond the internal inconsistency; Warner 5.31/5.32 and Iversen II.5/II.6 accepted as plausible without checking the books.
- Whether round 8's later lifts of these files preserved statements (out of scope; head is `39f1d12b`).

## Tool notes

- Per-packet `envdiff.json` must be committed beside the receipt (the brief assumes it). Reconciling against the stage-2 merged diff is only possible for packet-owned modules; downstream entries are unattributable.
- A receipt that says "forced by X" should list *every* pinned declaration the file depends on, including its own, and should say which ones were being lifted by a parallel packet (07/08). Round 8 had to rediscover that information.
- The `Type` binder item should state the counting rule (bare `Type` vs `Type u`); for `PrincipalCoverLocalSystem*` the "binders left" are already universe-polymorphic, which the receipt says only indirectly.
- Citations copied from the audit's twin column were not re-verified; the audit's own "?" marks (KS 2.3.?) should survive into the docstring as "cf." rather than be filled in.
- Docstring counts and one-commit-per-file were trivially checkable from the diff and reproduced exactly; that part of the receipt format works well.
