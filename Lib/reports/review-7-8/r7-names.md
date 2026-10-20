# Review of Lib/reports/round-7/names/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — every number, deletion, rename, import and cherry-pick I checked
reproduces from the history and the head; the one substantive gap is that the `Contragredient.lean`
deletion is not a "Mathlib duplicate" in the protocol's sense (five of its seven declarations have no
twin at all and `contragredient`'s named twin has a different type), which the receipt half-discloses
but the file-level table and the coordinator summary present as a clean duplicate.

## Findings

1. `[incomplete]` **`Lib/LinearAlgebra/Dual/Contragredient.lean` (commit `86377b36`): five
   declarations deleted with no surviving twin, and the named twin for the other two is not the same
   statement.** The receipt's Piece B table lists the file with "Mathlib twin `Representation.dual`";
   the lost-source table then admits "no replacement" for `ofMultiplicativeEquiv`,
   `ofMultiplicativeEquiv_apply`, `ofMultiplicative`, `ofMultiplicative_apply`,
   `freeGroup_invariant_iff`. The protocol requires a named surviving twin for every deletion; the
   audit row (AUDIT.md l.520) asked to *move* `freeGroup_invariant_iff` to a `FreeGroup` file, not
   delete it. For the two that do have a twin, the statements differ:
   ```
   deleted:  contragredient {G} [Group G] {R} [CommSemiring R] {N} [AddCommMonoid N] [Module R N]
               (ρ : G →* (N ≃ₗ[R] N)) : G →* (Module.Dual R N ≃ₗ[R] Module.Dual R N)
   Mathlib:  Representation.dual [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
               (ρV : Representation k G V := G →* V →ₗ[k] V) : Representation k G (Module.Dual k V)
   ```
   (Mathlib/RepresentationTheory/Basic.lean:678). Input is `→* (V →ₗ V)` not `→* (V ≃ₗ V)`, output is
   linear maps not linear equivalences; the audit row itself says "composing with
   `LinearEquiv.toLinearMap`". A weaker-typed twin is a FINDING under the brief. Mitigation: no
   consumer anywhere (verified: only `Lib/AxiomAudit.lean` probed the names; the only other grep hit
   is the word "contragredient" in two docstrings of `SingularCochains/DualEvaluation/CoordinateChange.lean`).
   What should happen: either restate `freeGroup_invariant_iff` (and, if wanted, the `Multiplicative`
   helpers) in a Lib file, or record these five explicitly as "deleted unused code, no twin, protocol
   exception" in the receipt's Piece B table (not only in the envdiff table), and say the `contragredient`
   twin is up to `LinearEquiv.toLinearMap`. `Lib/reviews/INTEGRATION-7.md` l.14 ("true Mathlib
   duplicates, no consumers") should be corrected for this file.

2. `[wrong receipt]` (minor) **Mechanism stated for the `AddCommGroup.lean` reason is not what the
   source says.** The receipt says "`Sheaf.H` is not reducible to `Ext` for instance search". In this
   Mathlib `CategoryTheory.Sheaf.H` is an `abbrev` (Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean:59),
   so it is reducible. The *observable* claim (Mathlib's instance does not fire) is nevertheless true:
   with only the file's three Mathlib imports, `example … : AddCommGroup (Sheaf.H.{0} F n) := inferInstance`
   and `… : Add (Sheaf.H.{0} F 0) := inferInstance` both fail with `failed to synthesize`, while the
   explicit term `Ext.instAddCommGroup` elaborates (scratch `r7-names/addcomm.lean`). The instance is
   load-bearing; the likely cause is the `HasExt.{w'}` universe argument, not reducibility. The
   receipt's conclusion stands; the stated reason should be corrected.

3. `[nit]` **Cherry-picked commits do not cite their originals.** None of the ten Piece D commit
   messages contains the `center-solution` hash it replays (checked all sixteen messages for the twelve
   hashes); the mapping exists only in the receipt table. Author name/email are preserved but author
   dates are the replay dates (e.g. `7416076` Aug 30 → `77af0c88` Sep 20), so `git log` cannot tell
   these are replays. A `(cherry picked from commit …)` line would make the receipt's table verifiable
   from the history alone.

4. `[nit]` **`77af0c88` deletes one blank line more than the union of its two originals.** The
   Hopf-side hunks of `7416076` + `240fe7dd` and of `77af0c88` are identical as line multisets except
   one extra `-` (empty line) in the branch commit — the by-hand context conflict the receipt describes.
   Harmless; recorded so the "byte-identical" expectation is precise.

No `[unsound]` finding. No `sorry`, `axiom`, `maxHeartbeats`, `unsafe`, `native_decide` in the branch
diff; the only `@[simp]` removals are on the deleted Hopf duplicates (Lib copies still carry `@[simp]`,
checked six) and on the deleted `Contragredient.lean`; the only `noncomputable` line removed is
`DegreeZero.lean`'s section header; `private` is neither added nor removed except on the 19 renamed
private declarations. All sixteen commits carry both trailers. `grep -rn "import Hopf" Lib/ --include=*.lean`
is empty at the branch tip and at head.

## Claims checked

| claim | status | how |
|---|---|---|
| 16 commits A, B1–B3, C, D1–D10 (+ receipt) with the listed shas/subjects | verified | `git log 46c22597..aa1ee3e7^2` |
| Piece A: 28 declarations, 12 Lib files, 86 occurrences, 19 private | verified | `git show b1ffa17e --stat` (12 Lib files + 1 Hopf + rename.txt); `-` lines carry 89 `_mo1973_` tokens = 86 Lib + 3 Hopf; 19 `+private` lines; 28 distinct new decl names |
| rename.txt: 28 lines, old→new, new names present, old absent | verified | `grep -rn _mo1973_ Lib/ --include=*.lean` empty at head; every new short name declared exactly once in `Lib/`+`Hopf/` at `aa1ee3e7^2` (loop over rename.txt) |
| only Lib consumer outside Lib is `IntegralHomology.lean`, 3 call sites | verified | `git show b1ffa17e -- Hopf/` (3 lines) |
| "`Hopf/` has 1,020 further `_mo1973_` occurrences" | verified (as lines) | `git grep -c _mo1973_ 46c22597 -- 'Hopf/*.lean'` sums to 1020 lines (1081 tokens) |
| DegreeZero: both defs are `(pushforward f).rightDerivedZeroIsoSelf` and `.app F`; twin `Functor.rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F` | verified, same statement | `git show 46c22597:…/DegreeZero.lean`; `higherDirectImage` is an `abbrev` for `(pushforward f).rightDerived n` (ResolutionTransgression.lean:82); Mathlib RightDerived.lean:376 |
| DegreeZero consumers: none but Lib.lean and 2 AxiomAudit pairs | verified | `git grep -l higherDirectImageZero… 46c22597` → only the file and AxiomAudit; AxiomAudit diff shows exactly 2 pairs |
| Contragredient twin `Representation.dual`/`dual_apply`; 7 AxiomAudit pairs; no consumers | partly (see Finding 1) | Mathlib Basic.lean:678/687; AxiomAudit diff shows 7 pairs |
| `range_tanh` (`Set.range tanh = Ioo (-1) 1`) replaced by `← Set.image_univ, Real.tanh_bijOn.image_eq` at its two uses, no statement changed | verified, twin stronger | `git show 7504253c`; Mathlib Artanh.lean:152 `tanh_bijOn : BijOn tanh univ (Ioo (-1) 1)` |
| `hasDerivAt_tanh`/`contDiffAt_artanh` absent from this Mathlib | verified | `grep -rln tanh Mathlib` = 9 files; the only derivative hit is `Real.logDeriv_cosh`; `Artanh.lean` declaration list stops at bijOn/injective/surjOn + monotonicity; no `ContDiff` lemma for tanh/artanh |
| `AddCommGroup.lean` instance load-bearing | verified (reason wording off, Finding 2) | scratch elaboration with the three Mathlib imports only; 10 call sites of `cohomologyAddCommGroup` outside AxiomAudit at tip (7 files), 8 importers |
| `SheafificationLocal.lean`: Mathlib has the 2 cited facts, not the 3 proved | verified | Mathlib names exist (receipt `#check`ed; not re-elaborated); file declares `exists_local_representative`, `germ_unit_eq_iff`, `exists_restriction_eq_of_germ_unit_eq` (l.95/108/119); consumers of the three at head: `GlobalSections` (2), `GlobalKernelLocal` (1), plus 4 Leray files importing the module; AUDIT.md l.523 asks to keep `exists_local_representative` |
| `SplitExtension.lean`: Mathlib's equivalence is `N ⋊[s.conjAct] G ≃* E`, consumer needs `⋊[D.fundamentalGroupAction hq b]` | verified | Mathlib GroupExtension/Basic.lean:179; `Hopf/Proof/LCP/BoundaryTopology.lean:12271-12294`; unused import in `CentralTwist.lean:7` present as stated |
| Piece C: 13 imports added; 443 imports = 443 modules, 0 duplicates, 0 orphans | verified | `git show dd6d4154 -- Lib.lean` (13 `+` lines, the named modules); `git ls-tree aa1ee3e7^2 Lib/` minus AxiomAudit vs `Lib.lean` imports: identical sorted lists |
| D2–D10 reproduce the cited originals' Hopf hunks | verified, byte-identical | all 12 cited hashes exist; for each of the 9 pairs, `git diff X^ X -- Hopf/` normalised equals the branch commit's (0 differing lines) |
| D1 = `7416076` + `240fe7dd` Hopf hunks, import conflict resolved as described | verified (Finding 4) | sorted `+/-` line multisets differ by one blank line; branch diff is 1 insertion (`import Lib.Geometry.Manifold.Gluing.OverBase`) / 457 deletions; `Hopf.Proof.LCP.AnalyticFillings` import kept (tip l.65) |
| `380ddd11` already applied: none of its 22 declarations under `Hopf/` | verified | 22 declaration names from its diff; none declared in `Hopf/*.lean` at tip |
| D2–D6, D10: "proof body only, no declaration removed" | verified | 0 removed `theorem/def/...` lines in each of those commits' Hopf hunks |
| D7–D9 twins exist with same statements | verified | `kerEquivOfColumnIso`, `surjective_of_columnIso` in `Lib/LinearAlgebra/ColumnKernel.lean` (identical binders/hypotheses); `signed_residual_coordinate_zero` identical text in `Lib/Data/Int/SignedResidual.lean` at tip — note round 8 (`cd893c55`) later moved it to `Hopf/Proof/Data/Int/SignedResidual.lean` as `ThreefoldHomology.signed_residual_coordinate_zero`, so the receipt's "`Int.signed_residual_coordinate_zero`" is no longer true at head |
| envdiff: lost 184/added 27, source 86/6, changed-type 16/10 PROOF-NAMING, moves 0, ambiguous 70 | verified | parsed `envdiff.json`; `changed_type_proof_naming` is exactly the ten names listed; every non-auxiliary lost name falls into the receipt's seven groups (DegreeZero 2, Contragredient 7, Cubic 1, IntegralHomology 4 + 2 changed-type, GlobalAssembly duplicates incl. `Input.disjoint`/`.mk`); nothing unexplained either way |
| `Star.Input` structure blocks byte-identical in Hopf and Lib at base | verified (40 lines) | `diff` of the two `structure … Input` blocks at `46c22597` (GlobalAssembly.lean:379, OverBase.lean:217) |
| Added source names (6) pre-existed in tree, newly reachable | verified | all six declared in files whose modules were not in `Lib.lean` before `dd6d4154` |
| AxiomAudit: 3,352 probes = 3,361 − 9 | consistent | source `#print axioms` count drops by exactly 9 (3374→3365, 3373→3364 top-level); the 3,361 figure is the build-output count from the preamble receipt, not a source count |
| `Challenge.lean` one pre-existing `sorry` | verified | `git show aa1ee3e7^2:Challenge.lean` — one `sorry` (l.46, receipt says l.42; both refer to the same statement) |

## Not checked

* The builds (`lake build Lib`, `Solution S6Shortcuts S6 Challenge`, `Lib.AxiomAudit`) and the census
  ratchet — no build allowed; I rely on the built copy at head compiling.
* The "two conflicts" narrative for `77af0c88` beyond its visible outcome.
* Whether `Input.disjoint`'s differing type hash between the Hopf and Lib copies has a cause other
  than differing `open` scopes — not determinable without a dump; the receipt's "nothing is gone" is
  consistent with the JSON (the Lib key survives).
* The receipt's `#check` scratch file for the Mathlib names (not in the repo); I confirmed the names
  by reading the Mathlib sources instead.
* Docstrings/citations: this branch adds none (Piece A only renames; the cherry-picks copy existing
  Hopf hunks), so item 7 of the brief does not apply.
* The 40 auxiliary module changes and 98/21/6 auxiliary lost/added/changed in envdiff.

## Tool notes

* The receipt should carry the `(cherry picked from commit …)` hash in each replayed commit's
  message; otherwise the table is the only link and a reviewer has to diff hunk-by-hunk.
* The Piece B "Deleted" table should list per-declaration twins, not per-file twins; the five
  twin-less deletions in `Contragredient.lean` are only discoverable from the envdiff section.
* Probe counts mix build-output counts (3,352/3,361) with source counts elsewhere; state which.
* Naming the actual failing instance goal and the `HasExt.{w'}` universe in the AddCommGroup
  reason would make it reproducible in one scratch file, which it is (4 lines).
