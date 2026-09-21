# Review of fix round — slice A (code: universe lifts and binder widenings)

**Verdict: ACCEPT WITH FINDINGS** — all 28 lifted/widened statements are literally the old statements
at `u = 0` (checked token by token against `62d45257` and by `#check`/`example` at the built head), no
hypothesis or instance argument changed, the 38 envdiff rows are exactly the receipts' lists, hygiene is
clean; what is wrong is receipt text: one "not local" reason for a pin left in place is refuted by
elaboration, the three receipts misdescribe the envdiff lost/added rows as "auxiliaries", and the
coordinator's "38 universe lifts" counts 10 downstream declarations whose statements did not change.

Branches: `fix/p02` (`ec1e2f77`, `fdfd786b`, `302c89fa`, receipt `8052b81c`), `fix/p0304` (code commit
`9a0fcff7`, receipt `b8ce6129`), `fix/p10` (code commit `69ffe4aa`, receipt `3200978f`). Head compared:
`8da46f0d`. The five code files are byte-identical between each branch tip and `8da46f0d` (`git diff
fix/<b> 8da46f0d -- <file>` empty; `git log 62d45257..8da46f0d -- <files>` shows only these commits and
their merges), so branch-tip and head statements coincide.

## Findings

1. `[wrong receipt]` **`fixes/p02.md` and commit `fdfd786b`: the reason for leaving
   `dualHomotopyEquiv`'s chain-side pin is false.** Receipt ("Left pinned, with the reason") and the
   commit body say `dualHomotopyEquiv`'s `{K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}` is "the chain side,
   which goes through `SingularCochains.chains X`" and "not local to these files". `dualHomotopyEquiv`
   (`PositivePrimitives.lean:72-81`) mentions no chains: it is `HomotopyEquiv K L → HomotopyEquiv
   (dualComplex A L) (dualComplex A K)` for arbitrary `K L`, proved from `dualMap`, `dualMap_comp`,
   `dualMap_id`, `dualHomotopy`, all of which take `K : ChainComplex (ModuleCat.{u} ℤ) ℕ`. A verbatim
   copy with `{K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}` and the identical proof body elaborates at the
   head (`A/Probe3.lean`, exit 0):
   ```
   dualHomotopyEquivLifted.{u_1, u_2} : (A : AddCommGrpCat.{u_2}) → {K L : ChainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, 0} ℤ) ℕ} →
     HomotopyEquiv K L → HomotopyEquiv (dualComplex.{u_1, u_2} A L) (dualComplex.{u_1, u_2} A K)
   ```
   Leaving it is defensible (finding 2 of `r7-packet-02` was about the coefficient binder, and the
   `pointFreeModule`/`single₀` pins really do go through `chains Unit` via `pointChainHomotopyEquiv`),
   but the stated reason is the same kind of "forced" claim the review round existed to remove. What
   should happen: the receipt says "left as out of scope; liftable" for this one pin, or the pin is
   lifted (one token, private def, no consumer outside the file).

2. `[wrong receipt]` `[nit]` **All three receipts misread the envdiff "lost/added" rows as auxiliaries.**
   `p02.md`: "The 39 non-source lost/added entries are the corresponding auto-generated auxiliaries
   (`_proof_n`, `.eq_1`)"; `p0304.md`: "the six auxiliary lost/added constants are the corresponding
   proof-term auxiliaries re-elaborated at the new universes"; `p10.md`: "the 2 lost/2 added auxiliaries
   are their own proof auxiliaries under the same names". The fixers' own `envdiff.txt` files (read
   read-only in `…/tmp/fix-p02`, `fix-p0304`, `fix-p10`) and the round-level `fixes/envdiff.json` show
   that the lost/added lists are the changed-type constants themselves: for p0304 the six entries are
   the six *theorems* (`AdaptedWindows.exists_relative_level_surgery_system` … with old/new type hash),
   theorems generate no `_proof_n`; for p10 the two entries are the two lemmas; for p02 the 39 are the
   30 source names plus 9 genuine auxiliaries (`dualHomotopyEquiv._proof_1/2`,
   `homologyBiproductEquiv._proof_1..5`, `sigmaChainComplexInverse._proof_1`,
   `sigmaChainInverseDegree.eq_1`). Round level: lost 56 = 47 changed-type + 5 deleted + 4
   `Fin.tailHeadAddEquiv._proof_n`; added 50 = 47 + 3. Nothing unsound follows (the tool's verdict lines
   are quoted correctly), but the prose explanation of the evidence is wrong in all three receipts.

3. `[wrong receipt]` `[nit]` **`Lib/reviews/REVIEW-7-8.md` §5: "38 universe lifts".** Only 28 of the
   38 changed types are lifts (Coproduct 8 + SingularCochains 12 + AdaptedWindows 6 + PrimitivesH1 2).
   The other 10 are `Coproduct.sigmaChainComplexMap`, `_inclusion`, `sigmaChainInverseDegree`,
   `_inclusion`, `_comp_inclusion`, `sigmaChainComplexInverse`, `_inclusion`,
   `sigmaChainComplexMap_comp_inverse`, `sigmaChainComplexInverse_comp_map`, `sigmaChainComplexIso`,
   whose *statements are unchanged* — `#check` with `pp.universes` at head shows every universe still
   `0` (`biproduct.{0, 0, 1}`, `Quiver.Hom.{0, 1}`, `Iso.{0, 1}`); only the `[HasBiproduct _]` proof
   term inside `biproduct` changed (Prop-valued, `Biproducts.lean:328`, so definitionally equal).
   `fixes/MERGE.md` says "38 changed types, all PROOF-NAMING" and `fixes/p02.md` explains the split
   correctly; §5 should say "28 lifts, 10 downstream instance-term changes". (Slice C owns §5; recorded
   here because the number is this slice's.)

4. `[incomplete]` **`fixes/MERGE.md` §"Left" omits what these three receipts left.** Not in MERGE.md's
   list: p02's chain-side pins in `PositivePrimitives.lean` (9 `.{0}` at head: `pointFreeModule`, three
   `single₀ (ModuleCat.{0} ℤ)`, `dualHomotopyEquiv`'s `K L`, two in the proof of
   `dualPointSingle_exactAt`, one in the module docstring) and the two `ULift.{0} ℤ` pins in
   `Vanishing.lean`; p10's 13 remaining pins in `PrimitivesH1.lean`; p10's untouched citations
   ("Warner … 5.32" in `Pullback/FiniteClosedPositive.lean:18`, `Pullback/ComparisonH1.lean:18`,
   `ComparisonPositive.lean:19,65`; "Bredon III Thm. 1.1" in `GlobalUnitPredicates.lean:17` — all
   still at head). The receipts admit them; MERGE.md does not. (Slice C item 7; flagged from this side.)

5. `[nit]` **`fixes/MERGE.md` row 10: "`Coproduct.lean` fully polymorphic".** The file has no `.{0}`
   left (verified, 9 → 0), but the `sigma*` half is at universe 0 by construction (`{ι : Type} (X : ι →
   Type)`), and the lifted `homology*` declarations keep `{ι : Type}` (correctly — Mathlib's
   `HasFiniteBiproducts` gives `HasBiproductsOfShape J` for `J : Type`). "No `.{0}` pin left" is exact;
   "fully polymorphic" is not.

6. `[nit]` **Pre-existing duplicate the fixer touched without noting.**
   `Coproduct.singularChainsFiniteBiproducts` and `Coproduct.homologyFiniteBiproducts` have identical
   statements and, after `ec1e2f77`, identical proof terms (envdiff type hash `3595687190` for both);
   the docstring "Homology chain complexes admit finite biproducts" describes nothing. Not introduced
   by this round; out of the fixer's scope; a one-line "twin, kept for the local-instance attributes"
   in the commit body would have been enough.

No `[unsound]` finding. No `[rule]` finding.

## Claims checked

| claim | status | how |
|---|---|---|
| Coproduct: 8 declarations, 9 `ModuleCat.{0}` occurrences → `ModuleCat.{u}`, proofs otherwise unchanged | verified | `git diff 62d45257 fix/p02 -- Coproduct.lean`: 9 token changes in 8 signatures, `universe u` added, two proof terms replaced (`of_hasFiniteProducts` → `Abelian.hasFiniteBiproducts`), nothing else |
| `Abelian.hasFiniteBiproducts` route adds no hypothesis | verified | `#check @CategoryTheory.Abelian.hasFiniteBiproducts : ∀ {C} [Category C] [Abelian C], HasFiniteBiproducts C`; the two instance theorems have no binders before and after; Mathlib `Abelian/Basic.lean:275` (`theorem hasFiniteBiproducts`, not an instance — hence the `attribute [local instance]` lines still needed) |
| Coproduct `u = 0` instances are the old statements | verified | `A/Probe.lean`: `example : HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) := Coproduct.singularChainsFiniteBiproducts` and `…homologyFiniteBiproducts` accepted; fixer's `Chk2.lean` (read-only) does the same for `homology_π_ι_self`/`homologyBiproductEquiv` |
| Coproduct lift is real (not textual) | verified | `Coproduct.singularChainsFiniteBiproducts.{1} : HasFiniteBiproducts.{1,2} (ChainComplex (ModuleCat.{1,0} ℤ) ℕ)`; `homologyBiproductEquiv.{1}` elaborates |
| "The seven downstream declarations go through with no proof change" | verified | diff shows no change below the signatures; build claimed green; envdiff lists them PROOF-NAMING |
| The 10 `sigma*` downstream changed types keep every universe at 0 | verified | `pp.universes` on `sigmaChainComplexMap`, `sigmaChainComplexIso`, `sigmaHomologyEquiv` (finding 3) |
| `HasBiproduct` is Prop-valued | verified | `#check @CategoryTheory.Limits.HasBiproduct : … → Prop`; `Biproducts.lean:328 class HasBiproduct … : Prop` |
| PositivePrimitives: 7 `A : AddCommGrpCat.{0}` → `.{w}`, proofs unchanged | verified | 7 hunks (`dualHomotopyEquiv`, `pointCochainHomotopyEquiv`, `dualPointSingle_exactAt`, `pointCochain_exactAt_positive`, `pointCocycle_boundary`, `pullback_closed_succ`, `nullhomotopic_pullback_closed_succ`), each one token; `universe u` → `universe u w`; module docstring; `.{0}` 15 → 9 (−7 lifted, +1 new docstring mention) |
| Vanishing: 5 `A : AddCommGrpCat.{0}` → `.{w}`, proofs unchanged | verified | 5 one-token hunks, `universe w` added, docstrings; `.{0}` 7 → 3 (−5, +1 docstring mention) |
| "12 not 3" | verified | 7 + 5 = 12 binders in the diff; the review (`r7-packet-02.md` finding 2) had elaborated 2 Vanishing + `pointCocycle_boundary` (its table says 3 Vanishing — the review's own inconsistency, immaterial); §5, MERGE.md, p02.md consistent (12) |
| SingularCochains `w = 0` instances are the old statements | verified | `A/Probe.lean`: four `example`s restating `pointCochain_exactAt_positive`, `pointCocycle_boundary`, `cohomology_subsingleton_iff_of_homeomorph`, `contractibleCohomology_subsingleton` at `AddCommGrpCat.{0}` accepted; `pp.universes` shows `A : AddCommGrpCat.{u_1}`, `complex.{u_1}`, spaces `Type`, `TopologicalSpace.{0}`, i.e. only the coefficient universe moved |
| Lift is real | verified | `pointCohomology_subsingleton (AddCommGrpCat.of (ULift.{1} ℤ))` and `nullhomotopic_pullback_closed_succ.{1}` elaborate |
| Interface is at `.{w}` (`complex`, `dualComplex`, `pullback`, `pullbackHomotopy`, `homotopyEquivCohomologyIso`), only `chains` pinned | verified | `SingularCochains.lean` at head l.86/126/130/164/179 take `A : AddCommGrpCat.{w}`; `chains (X : Type)` l.120 |
| Vanishing `ULift.{0} ℤ` pins forced by the local UCT | verified | `CoefficientNormalization.lean:199` `singularUliftIntCohomologyEvaluation_isIso_of_projective (X : Type) … IsIso (uliftIntCohomologyEvaluation (chains X) n)` at `AddCommGrpCat.of (ULift.{0} ℤ)` |
| PositivePrimitives chain-side pins forced by `chains` | partly | true for `pointFreeModule`/`single₀`/`pointChainHomotopyEquiv` (`chains Unit`, `ModuleCat.of ℤ ℤ`, `TopCat.of Unit`); **refuted** for `dualHomotopyEquiv`'s `K L` (finding 1) |
| `pointChainHomotopyEquiv` has no coefficient binder | verified | source l.64-70 |
| Vanishing/PositivePrimitives docstrings state the universes correctly | verified | read against head; "small" removed where `A` is now `.{w}`; module docstrings name binder and universe |
| AdaptedWindows: six `Type` → `Type*`, "exactly six lines", nothing else | verified | diff is 6 one-token hunks; `pp.universes` shows `{E : Type u_1} {M : Type u_2}` (+ `{X : Type u_3}`), all instance arguments follow (`AdaptedWindows.{u_1,u_2} E f`, `ContMDiff.{0,u_1,u_1,u_2,0,0,0}`); no `Type`-pinned dependency (a `Type*` binder cannot be silently forced to 0 — it is a universe parameter, so a pinned dependency would have failed the build) |
| "None of the six binders was forced"; `structure AdaptedWindows (E : Type*) … {M : Type*}` | verified | `SurgeryWindows.lean:1953`; `#check @AdaptedWindows : (E : Type u_1) → … {M : Type u_2} → … → Type (max u_1 u_2)` |
| No downstream declaration moved universe | verified | envdiff: exactly 6 changed types; consumers (`SurgeryCollapse.lean:601-831`, `Hopf/Recognition.lean:1195-1223`) unchanged and unlisted |
| PrimitivesH1: `section Homotopy` variable `.{0}` → `.{u}`, `universe u` added, nothing else; "14 → 13" | verified | diff is 2 lines; `.{0}` 14 → 13; no other `universe` in the file (would clash) |
| The two private lemmas: real `u`, old statement at `u = 0` | verified | `A/Probe3.lean` `run_cmd` prints `levelParams [u]`, `{K L : CochainComplex.{u,u+1,0} AddCommGrpCat.{u} ℕ}`, statements identical to base source l.168-190 modulo `u` |
| Both call sites still at `.{0}` | verified | `PrimitivesH1.lean:326,342` inside `(A : AddCommGrpCat.{0})` theorems |
| `envdiff.json`: 38 rows = 18 + 12 + 6 + 2, matching the receipts' lists exactly | verified | listed all 38 `changed_type_proof_naming` names; Coproduct 18 (8 lifted + 10 sigma*), `AlgebraicTopology.SingularCochains.*` 12, `AdaptedWindows.*` 6, `TopCat.SingularCochainSheaf.homotopy_apply_closed_{one,zero}` 2; the per-branch `envdiff.txt` files (30 / 6 / 2) sum to it; `changed_type_source` empty |
| `.{0}` pins 293 → 269 | verified | `git grep -o '\.{0}' <rev> -- 'Lib/*.lean' \| wc -l` at `62d45257` = 293, `9a6e125a` = 269, `8da46f0d` = 269 (definition: textual occurrences in Lean files under `Lib/`, recursively). Per-file: Coproduct −9, PositivePrimitives −6, Vanishing −4, PrimitivesH1 −1, `SingularSmallChains/Basic.lean` −4 (dup-dfa, slice B) = −24 |
| p02 envdiff "0 lost, 0 added, 30 changed source types (8 + 12 + 10)" | verified | fixer's `fix-p02/envdiff.txt`; names match the receipt's three lists |
| p0304 / p10 envdiff "6 / 2 changed, 0 lost, 0 added" | verified | fixer's `envdiff.txt` files; description of lost/added rows wrong (finding 2) |
| Commit hygiene: subject `Lib/<path>: …`, body names finding, both trailers, one fix item per commit | verified | all 20 commits on the three branches: `Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>` and `Claude-Session: …session_01VZt4JDgce67x5QTThwQ3E2` present, subjects start `Lib/`, bodies say "closes r7-packet-NN finding k" (`b69465c0` closes two findings sharing one docstring, `78314e50` closes 2 and 3 as one citation set — allowed by the rule's "one citation set") |
| No edits under `Lib/reports/` / `Lib/reviews/` beyond own receipt; no `TEXTBOOK.md`/`DECOMPOSITION.md`/`CORRESPONDENCE.md` | verified | `git diff --name-only` per branch |
| §9 hygiene | verified | over `+`/`-` lines of the three Lean diffs: no `sorry`/`axiom`/`admit`(the one hit is the English word in a `Relative.lean` docstring)/`maxHeartbeats`/`unsafe`/`native_decide`; no `@[simp]` added or removed (the p10 blank-line commit's `@[simp]` lines are context); no `noncomputable` added, no `private` removed (the `private`/`noncomputable` lines in the diff change only `.{0}` → `.{w}`); no `import Hopf` under `Lib/` |
| Docstring-only commits of p0304/p10 contain no code change | verified | filtered `+`/`-` lines for Lean keywords: only docstring text; `68a894aa` removes exactly four blank lines inside signatures |
| p0304 "Ten commits", p10 "5 + receipt", p02 "3 + receipt" | verified | `git log 62d45257..fix/<b>` |

## Not checked

* Builds (`lake build Lib`, `Solution S6Shortcuts S6 Challenge`, `Lib.AxiomAudit`, census) — not re-run,
  per the brief; the built copy at `8da46f0d` elaborated all my probes, which is consistent with them.
* The fixers' `dump_base.jsonl`/`dump_after.jsonl` were not re-diffed; I read their `envdiff.txt`
  (read-only) and the round-level `envdiff.json` and compared names.
* The docstring/citation commits of `fix/p0304` and `fix/p10` for *correctness of prose* (Slice C);
  I checked only that they change no code.
* Whether `Coproduct.sigma*`'s downstream users in `Hopf/` (`LibShims.lean:64,66` exports) see any
  difference — cannot, since the types are unchanged and Prop-irrelevant; build claimed green.
* MERGE.md's Weibel "Theorem 2.4.3 in the three Ext/AcyclicResolution* files" vs p0304's "plain
  Theorem 2.4.6 in AcyclicResolution{,H1}.lean": at head my grep finds neither in those files (another
  branch may have touched them); Slice C.

## Tool notes

* Three elaborations sufficed (`A/Probe.lean`, `A/Probe2.lean` (failed on private-name syntax),
  `A/Probe3.lean`). Private lemmas are unreachable by `#check`; a `run_cmd` scanning `env.constants`
  for the suffix works and should be the standard recipe in receipts that lift private declarations.
* `envdiff.txt` truncates the changed-type list at 20 names; the receipts had to be checked against
  `envdiff.json`. Printing the full list (38 names is short) would let a reader verify the "18 + 12 +
  6 + 2" line without Python.
* The tool's "lost/added" rows include every changed-type constant; all three fixers misread them
  (finding 2). A one-line legend in `envdiff.txt` ("lost/added include constants whose type hash
  changed") would prevent this.
* A receipt that says "left pinned, with the reason" should attach the elaboration that shows the pin
  is forced (or say "untested, out of scope"), exactly as required of "forced" claims in round 7. The
  one such claim here that was checkable in one `example` (finding 1) was wrong.
* "Universe lift" vs "changed type" should be separate counts everywhere (§5's "38 universe lifts").
