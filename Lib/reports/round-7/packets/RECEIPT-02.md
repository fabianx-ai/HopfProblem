# Round 7 packet 02 — receipt

Worktree `/home/goblin/hopf-r7-p02`, branch `r7/packet-02`, base `9552305f`,
Lean v4.33.0 / Mathlib v4.33.0.  All 11 files of `packet-02.md` are done; nothing
is left.

## Per file

### `Lib/AlgebraicTopology/SingularCochains/PositivePrimitives.lean` (B) — `fa51563a`
* citations: module docstring rewritten with `## Main results` and `## References`
  naming Hatcher §3.1 (cohomology of a point vanishes in positive degrees) and
  `Mathlib/Algebra/Homology/AlternatingConst.lean`; 0 manuscript citations were
  present.
* docstrings: 0 added (6 declarations already had one; the 5 missing ones are `private`
  and are out of scope).  **(corrected)** the public/private split as first written was
  wrong: the file has 4 public declarations (all documented) and 7 private ones (2
  documented, 5 not).  Six docstrings and five gaps is right; "all 6 public" is not.
* universe pins: 2 of 17 generalised — `homotopy_on_cocycle_succ` and the private
  `cochainMap_d_succ` from `AddCommGrpCat.{0}` to `AddCommGrpCat.{u}`.
  15 left.  **(corrected)** the reason given here was wrong: of the four interface
  declarations named, only `chains` is pinned.  At the branch head
  `Lib/AlgebraicTopology/SingularCochains.lean` has `dualComplex (A : AddCommGrpCat.{w})
  (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)` (l.82), `complex (X : Type) (A :
  AddCommGrpCat.{w}) : CochainComplex AddCommGrpCat.{w} ℕ` (l.122), `pullback (A :
  AddCommGrpCat.{w})` (l.126), `pullbackHomotopy` (l.160) and
  `homotopyEquivCohomologyIso` (l.175) all at `.{w}` — packet 01 lifted the coefficient
  universe in the same round.  Genuinely forced are the `ModuleCat.{0} ℤ` pins on
  `pointFreeModule`/`single₀` (through `chains`); the `A : AddCommGrpCat.{0}` binders at
  l.73/83/89/104/111/149/158 are **not** forced by the imported interface (the reviewer
  restated two of them and `pointCocycle_boundary` at `.{w}` with identical proof bodies
  and they elaborate).  See the corrections section at the end.
* `: Type` binders: 0 of 2 widened — forced by `complex (X : Type)` in the same
  imported interface.

### `Lib/AlgebraicTopology/SingularCochains/Vanishing.lean` (C) — `470f6058`
* citations: 2 replaced — "This FREE owner packages two standard transports" and
  "the repository's coefficient convention `ULift ℤ`" (module docstring, and again in
  the docstring of `uliftIntCohomology_subsingleton_of_projective_of_homology`), now
  Hatcher §3.1 and Theorem 3.2 (universal coefficient theorem), with `## Main results`
  and `## References` added.
* docstrings: 0 added (7/7 present).
* universe pins: 0 of 7.  **(corrected)** as for `PositivePrimitives`, only `chains` is
  pinned in that interface.  Genuinely forced here are the two `ULift.{0} ℤ` pins (via
  `DualEvaluation.LocalUCT.uliftIntCohomologyEvaluation`); the three
  `A : AddCommGrpCat.{0}` pins at l.61/72/82 lift with identical proof bodies.
* `: Type` binders: 0 of 3 — same cause.

### `Lib/AlgebraicTopology/SingularHomology/Chains.lean` (C) — `9a567385`
* citations: none present; one sentence added to `## Main definitions` recording that
  the `ChainHomology` API is now universe-generic.
* docstrings: 0 added (153/153 present).
* universe pins: **36 of 36 generalised**, `ModuleCat.{0} ℤ` → `ModuleCat.{u} ℤ`.
  All 36 sit in the abstract block `SingularChains.ChainHomology.*`
  (`ShortCycle`, `shortCycleModule`, `ShortBoundaries`, `shortCycleClass`,
  `shortCycleClass_surjective`, `shortCycleClass_eq_zero_iff`, `ShortOpchains`,
  `shortOpchainsModule`, `shortHomologyToChainClass`,
  `shortHomologyToChainClass_injective`, `shortHomologyToChainClass_cycleClass`,
  `Cycle1`, `Boundaries1`, `cycleClass`, `cycleClass_surjective`, `mkCycle1`,
  `cycleClass_eq_zero_iff`, `boundaryCycle1`, `Opchains`, `opchainsModule`,
  `chainClass`, `chainClass_boundary`, `chainClass_eq_iff`, `range_sc_one_f`,
  `opchainsEquiv`, `homologyToChainClass`, `homologyToChainClass_injective`,
  `homologyToChainClass_cycleClass`, `boundaries1_le_ker`, `homologyDesc`,
  `homologyDesc_cycleClass`, `shortMap`, `mapCycles`, `mapCycles_val`,
  `homologyMap_cycleClass`).
* `: Type` binders: none in the packet's count; the 17 `X : Type` of the singular part
  are forced — `singularComplex X = (TopCat.toSSet.obj (TopCat.of X)).chainComplex
  (ModuleCat.of ℤ ℤ)` and `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ` forces `TopCat.{0}`.

### `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean` (C) — `2fda9cbe`
* citations: none present.
* docstrings: **88 added (88/88)** — every public declaration now states what it says
  mathematically; the Hatcher references (§3.B Künneth splitting, §2.2 connecting map)
  are named where they apply.
* universe pins: **5 of 5 generalised** — `biprodElement`, `biprod_lift_f_apply`,
  `biprodElement_desc`, `biprodElement_boundary`, `biprod_lift_eq_boundary`.
* `: Type` binders: none in the packet's count.

### `Lib/AlgebraicTopology/SingularHomology/CircleProduct.lean` (C) — `3810bf32`
* citations: 1 corrected — the module docstring cited Hatcher Corollary 2.11 for the
  Künneth splitting; Corollary 2.11 is "a homotopy equivalence induces isomorphisms on
  homology".  Now §3.B (Künneth, one circle factor) for the statement, §2.2
  (Mayer–Vietoris, torus example) for the proof, Corollary 2.14 for `H_k(S¹)`.
* docstrings: 0 added (the packet records no docstring item).
* universe pins: **4 of 4 generalised** —
  `SingularMayerVietoris.ModuleHomology.cyclesMk_eq_moduleCatCyclesIso_inv`,
  `.cycleClass_eq_homologyClassOfCycle_of_next`, `.cycleClass_eq_homologyClassOfCycle`,
  `SingularHomology.connectingMap_cycleClass`.

### `Lib/AlgebraicTopology/SingularHomology/Coproduct.lean` (B) — `ffb80ad4`
* citations: 2 removed — "(attached to every declaration of the block, as in the
  source)" and "Consumed by the local-contributions and recognition files."; the
  finiteness of the index set is now stated against Hatcher Proposition 2.6.
* docstrings: 0 added (29/29 present).
* universe pins: **0 of 9 — item stopped, obstacle recorded.**  Replacing them by a
  universe variable makes the *type* of `Coproduct.singularChainsFiniteBiproducts` fail
  to elaborate:

  ```
  Lib/AlgebraicTopology/SingularHomology/Coproduct.lean:64:81:
  stuck at solving universe constraint
    u =?= max ?u.14 ?u.15
  while trying to unify
    CategoryTheory.Limits.HasLimitsOfSize.{?u.14, ?u.14, u, u + 1} (ModuleCat ℤ) : Prop
  with
    CategoryTheory.Limits.HasLimitsOfSize.{?u.14, ?u.14, max ?u.14 ?u.15,
      max (?u.14 + 1) (?u.15 + 1)} (ModuleCat.{max ?u.14 ?u.15, 0} ℤ) : Prop
  ```

  Mathlib's `ModuleCat.hasLimits` is stated for `ModuleCat.{max v w} R` and does not
  unify with a bare universe variable.  Supplying
  `HasFiniteProducts (ModuleCat.{u} ℤ) := ⟨fun _ => ModuleCat.hasLimitsOfShape⟩` was
  tried and fails the same way.  Every declaration of the file needs that instance to
  form `⨁ K`.  **(corrected)** the conclusion drawn from this — "so the pin is not a
  local fix" — is false.  The stuck constraint does reproduce, but the instance is
  obtainable at a bare `u` by a different proof term:

  ```lean
  example : HasFiniteBiproducts (ChainComplex (ModuleCat.{u} ℤ) ℕ) := Abelian.hasFiniteBiproducts
  ```

  which elaborates against this module (`Abelian (ChainComplex (ModuleCat.{u} ℤ) ℕ)` is
  found by `inferInstance`).  Both pinned instance theorems
  (`singularChainsFiniteBiproducts` l.62, `homologyFiniteBiproducts` l.317) use the
  failing term, so the fix is a one-token change in two places; the seven other pins
  (l.323–424) are abstract homological algebra over `⨁ K` and are not tied to
  `singularComplex`.  The real reason the item stopped is that only
  `HasFiniteBiproducts.of_hasFiniteProducts` and an explicit `HasFiniteProducts`
  instance were tried.  The item is re-opened in `Lib/reviews/REVIEW-7-8.md` §3.

### `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` (C) — `16738df2`
* citations: 4 pieces of process narrative deleted — the stale claim that the
  `PeriodTorusHigherHomology` names are only compatibility shims (**over half (corrected)**
  — 113 of the 218 declarations — of the file is in that namespace), "the homotopy-invariance arguments of the Hurewicz lane",
  the record of a disposable experiment with the local `Module ℤ` instances, and the
  "Consumers: the Hurewicz lane, the torus lane, the Pontryagin product" list.  The
  restriction to left degree 1 (and 2) is now stated against Hatcher's
  `H_p ⊗ H_q → H_{p+q}` (§3.B).
* docstrings: 0 added (218/218 present).
* universe pins: **5 of 5 generalised** — `SingularHomology.homologyBoundaries`,
  `.homologyLinearMap_ext`, `.homologyBoundaries_le_ker`, `.homologyDesc`,
  `.homologyDesc_cycleClass`.

### `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean` (B) — `95ca1371`
* citations: 1 replaced — the porting remark "the source used the `FirstHurewicz` alias
  of that namespace" is gone; `## Main definitions and results` and `## References`
  (Hatcher Theorem 2A.1) added.
* docstrings: **16 added (16/16)**.
* universe pins / `: Type` binders: none in the packet's count.

### `Lib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` (B) — `88db7b4d`
* citations: 3 docstrings now name their textbook result — `homotopic_homologyMap`
  (Hatcher Theorem 2.10), `homotopyEquivHomologyEquiv` (Corollary 2.11),
  `singularChainHomotopy` (repackages Mathlib's
  `TopCat.Homotopy.singularChainComplexFunctorObjMap`).
* docstrings: 0 added (26/26 present).
* `: Type` binders: **0 of 8 — item stopped, obstacle recorded.**  Widening them to
  `Type*` fails at the first use:

  ```
  Lib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean:73:46:
  Application type mismatch: The argument
    ContinuousMap.id X
  has type
    ContinuousMap.{u_1, u_1} X X
  of sort `Type u_1` but is expected to have type
    ContinuousMap.{0, 0} ?m.2 ?m.2
  of sort `Type` in the application
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X)
  ```

  forced by `SingularMayerVietoris.SingularHomology` / `singularHomologyMap`, which go
  through `SingularChains.singularComplex` and `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ`.

### `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` (C) — `a379b082`
* citations: none present (the module docstring already cites Hatcher §2.1/§2.2).
* docstrings: 0 added (249/249 present).
* universe pins: **29 of 29 generalised**, all in the homological-algebra block
  (l.600-930): `homologyLinearMap`, `homologyLinearMap_comp`, `homologyLinearMap_neg`,
  `connectingMap`, `exact_at_leftHomology`, `exact_at_middleHomology`,
  `exact_at_rightHomology`, `homologyLinearMap_second_zero_surjective`,
  `connectingMap_naturality`, `homologyClassOfCycle`, `connectingMap_lift_is_cycle`,
  `connectingMap_homologyClassOfCycle`, `homology_fst_inl`, `homology_snd_inl`,
  `homology_fst_inr`, `homology_snd_inr`, `homology_biprod_total`,
  `homologyBiprodEquiv`, `homologyBiprodEquiv_symm_apply`, `homologyBiprodEquiv_desc`,
  `biprodSequenceFirstMap`, `biprodSequenceSecondMap`, `biprodSequenceSecondMap_desc`,
  `biprodSequence_exact_at_leftHomology`, `biprodSequence_exact_at_middleHomology`,
  `biprodSequence_exact_at_rightHomology`, `biprodSequence_second_zero_surjective`.
* the 100 `X : Type` binders of the topological part are forced, same cause as
  `Chains.lean`.

### `Lib/AlgebraicTopology/SingularHomology/ModuleHomology.lean` (C) — `0e72dd19`
* citations: the whole module docstring was rewritten.  It advertised
  `FirstHurewicz.ChainHomology.shortCycleClass`, `ShortCycle`, `ShortOpchains`,
  `shortHomologyToChainClass`, `homologyDesc`, `homologyToChainClass_cycleClass`,
  `chainClass_eq_iff`, `boundaries1_le_ker` — 8 names none of which is declared here
  (**(corrected)** the namespace `FirstHurewicz.ChainHomology` does not exist *in `Lib`*;
  `Hopf/LibShims.lean:39-41` has `namespace FirstHurewicz export SingularChains
  (ChainHomology.shortCycleClass …)`, which creates exactly those aliases.  The rewrite is
  still right — `Lib` must not document `Hopf`-side aliases — but the stated reason was inexact) — and named the project
  files that consume the API.  Replaced by a description of the declarations the file
  has, with `## Main definitions and results` and `## References` (Hatcher §2.1,
  `ShortComplex/ModuleCat.lean`, `QuasiIso.lean`).
* docstrings: 0 added (20/20 present).
* universe pins: **22 of 22 generalised**, `ChainComplex (ModuleCat.{0} ℤ) ℕ` →
  `ChainComplex (ModuleCat.{u} ℤ) ℕ`, covering `Cycle`, `cycleModule`,
  `cycle_condition`, `mkCycle`, `cycleClass`, `cycleClass_surjective`,
  `cycleClass_eq_zero_iff`, `cycleClass_eq_iff`, `boundaryCycle`, `shortMap`,
  `mapCycles`, `mapCycles_val`, `homologyMap_cycleClass`,
  `homologyMap_surjective_of_cycle_lifting`,
  `homologyMap_injective_of_boundary_lifting`, `quasiIsoAt_of_cycle_boundary_lifting`,
  `quasiIso_of_cycle_boundary_lifting`, `cycle_of_boundary_relation`,
  `quasiIso_of_injective_chain_conditions`.
* the ring `ℤ` is **not** generalised: the `Module ℤ` structures on cycles and opchains
  come from `SingularChains.ChainHomology.shortCycleModule`, so an `R` would have to be
  threaded through `Chains.lean` first and would change every `→ₗ[ℤ]` in the statements.

## Totals

| item | done | left |
|---|---|---|
| manuscript citations / process narrative replaced | 13 | 0 |
| docstrings added | 104 (88 CirclePaths + 16 FirstHurewicz) | 0 (all remaining gaps are `private`) |
| universe pins generalised | **103 of 134 (corrected)** | **31 (corrected)** (9 Coproduct, 15 PositivePrimitives, 7 Vanishing — see the corrections section: the Coproduct obstacle and the "forced by the interface" reason were both wrong) |
| `: Type` binders widened | 0 of 13 | 13 (all forced by `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ`) |

## Builds

```
lake build Lib
  ✔ [9149/9150] Built Lib (3.4s)
  Build completed successfully (9150 jobs).            rc=0

lake build Solution S6Shortcuts S6 Challenge
  ℹ [9188/9189] Built Solution (6.1s)
  info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms:
    [propext, Classical.choice, Quot.sound]
  Build completed successfully (9189 jobs).            rc=0

lake build Lib.AxiomAudit
  Build completed successfully (9150 jobs).            rc=0
  3352 `depends on axioms` lines, 4 distinct axiom sets, all subsets of the allowed three:
    [propext, Classical.choice, Quot.sound]
    [propext, Classical.choice]
    [propext, Quot.sound]
    [propext]
```

## envdiff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl`

```
constants before 21719 after 21719 (keys 21713 21713)
lost 285 added 285   of which source declarations: 0  0
names with changed type 285   of which source: 233 (auxiliary: 52)
module moves (source declarations, 1-to-1): 0 ; ambiguous: 0 ; auxiliary moved: 0
VERDICT PASS
```

**0 source declarations lost, 0 added.**  All 233 changed source types are explained:

| count | what | why the type changed |
|---|---|---|
| 35 | `SingularChains.ChainHomology.*` | generalised in `Chains.lean` to `ModuleCat.{u} ℤ` |
| 27 | `SingularMayerVietoris.*` (l.600-930 block) | generalised in `MayerVietoris.lean` |
| 19 | `SingularMayerVietoris.ModuleHomology.*` | generalised in `ModuleHomology.lean` |
| 5 | `PeriodTorusHigherHomology.biprod*` | generalised in `CirclePaths.lean` |
| 5 | `SingularHomology.homology*` | generalised in `CrossProduct.lean` |
| 4 | `SingularMayerVietoris.ModuleHomology.*` / `SingularHomology.connectingMap_cycleClass` | generalised in `CircleProduct.lean` |
| 2 | `AlgebraicTopology.SingularCochains.homotopy_on_cocycle_succ`, `.cochainMap_d_succ` | generalised to `AddCommGrpCat.{u}` |
| **97** | **directly generalised (subtotal)** | |
| 53 | `Hurewicz.*` | statement mentions a generalised declaration (`Cycle`, `cycleClass`, `mkCycle1`, `homologyDesc`, …), whose universe is now an explicit level argument |
| 31 | `PeriodTorusHigherHomology.*` | idem |
| 19 | `MappingTorusHomology.Covering.*` | idem |
| 17 | `SingularHomology.*` | idem |
| 5 | `SingularMayerVietoris.*` | idem |
| 4 | `CoverNaturality.*` | idem |
| 4 | `SixthHurewicz.*` | idem |
| 2 | `SphereCube.*` | idem |
| 1 | `MorseCancellation.zeroChainCycle` | idem |
| **136** | **downstream (subtotal)** | |
| **0** | **unexplained** | |

Checked mechanically: every one of the 233 is either literally one of the declarations
whose source now carries `ModuleCat.{u}` / `AddCommGrpCat.{u}`, or has one of those in
its `uses` list in `dump_after.jsonl`.

## Commits

`9552305f..2fda9cbe` (11 file commits + this receipt):

```
fa51563a  SingularCochains/PositivePrimitives.lean
470f6058  SingularCochains/Vanishing.lean
95ca1371  SingularHomology/FirstHurewicz.lean
88db7b4d  SingularHomology/HomotopyInvariance.lean
9a567385  SingularHomology/Chains.lean
0e72dd19  SingularHomology/ModuleHomology.lean
ffb80ad4  SingularHomology/Coproduct.lean
a379b082  SingularHomology/MayerVietoris.lean
3810bf32  SingularHomology/CircleProduct.lean
16738df2  SingularHomology/CrossProduct.lean
2fda9cbe  SingularHomology/CirclePaths.lean
```

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-packet-02.md` (ACCEPT WITH FINDINGS; the code
changes are sound — pure `.{0}` → `.{u}` lifts with unchanged statements, 63 docstrings checked
against their statements, none wrong).  What follows corrects this receipt's text only; no Lean file
was changed by it.  The figures marked "(corrected)" above were fixed in place and are repeated here
because the originals were reported to the coordinator.

1. **Totals row (finding 3).**  "101 of 126, 25 left (9 Coproduct, 15 PositivePrimitives, 7
   Vanishing)" is wrong three times: 9 + 15 + 7 = 31, not 25; the per-file "done" numbers sum to
   2 + 36 + 5 + 4 + 5 + 29 + 22 = **103** (the row dropped `PositivePrimitives`' 2); and the per-file
   totals sum to 17 + 7 + 36 + 5 + 4 + 9 + 5 + 29 + 22 = **134**.  Correct row: **103 of 134, 31
   left**.  The per-file numbers themselves are right (re-counted `.{0}` before/after in each file).

2. **`Coproduct.lean`: "the pin is not a local fix" is false (finding 1).**  See the corrected
   passage in the `Coproduct.lean` section above.  The stuck universe constraint reproduces, but
   `Abelian.hasFiniteBiproducts` supplies the instance at a bare `u`; only
   `HasFiniteBiproducts.of_hasFiniteProducts` and an explicit `HasFiniteProducts` instance had been
   tried.  The item is re-opened (`Lib/reviews/REVIEW-7-8.md` §3, packet 02: lift the two biproduct
   instances, then the seven abstract pins).  Whether the seven downstream declarations then go
   through was not tested by the reviewer either.

3. **`PositivePrimitives` / `Vanishing`: "forced by the interface" is wrong (finding 2).**  Of
   `complex`, `chains`, `dualComplex`, `pullback`, only **`chains`** is pinned; packet 01
   (`c31bbc73`) lifted the coefficient universe of the other three in the same round.  Corrected in
   both file sections above.  The genuinely forced pins are the `ModuleCat.{0} ℤ` ones on
   `pointFreeModule`/`single₀` and the two `ULift.{0} ℤ` in `Vanishing` (via `LocalUCT`).  Whether
   the private helpers `pointChainHomotopyEquiv` / `dualPointSingle_exactAt` lift was not tested
   (private, unreachable from a scratch file), but nothing in their statements needs `A` at universe
   0.  Relatedly, both new module docstrings say "stated for an arbitrary coefficient group" while
   every statement takes a universe-0 group — a code fix, listed in `REVIEW-7-8.md` §3.

4. **Occurrence counts vs. declaration counts (finding 4).**  The per-file "36 of 36 / 29 of 29 /
   22 of 22 generalised" are `.{0}` **occurrence** counts, while the envdiff table's 35 / 27 / 19 are
   **declaration** counts (`shortMap` carries two pins, `homologyBiprodEquiv_desc` three,
   `ModuleHomology`'s old module docstring two).  The receipt lists 35 names under "all 36" without
   saying so.  Under the round-8 rule (`REVIEW-7-8.md` §4) the unit must be labelled.

5. **`FirstHurewicz.ChainHomology` (finding 5).**  The namespace does not exist in `Lib`, but
   `Hopf/LibShims.lean:39-41` creates exactly those aliases by `export`.  Corrected in place; the
   docstring rewrite itself stands.

6. **`PositivePrimitives` public/private split (finding 6)** and **`CrossProduct`'s
   `PeriodTorusHigherHomology` share (finding 7)**: corrected in place (4 public + 7 private, not
   "all 6 public"; 113 of 218 declarations, i.e. over half, not "about a third").  Neither affects
   the work done.

7. **The envdiff section cannot be checked against anything (finding 4).**  No `envdiff.json`/`.txt`
   sits beside this receipt, the worktree `/home/goblin/hopf-r7-p02` the dumps came from is gone, and
   the job directory holds only `*.bak` files and the axiom log.  The only round-7 artefact in the
   tree is the merged `Lib/reports/round-7/envdiff-merged-d950428a.json`, in which
   `changed_type_source` is empty and all 1,028 changed names sit under `changed_type_proof_naming`,
   so the 233 of this packet cannot be isolated.  The arithmetic here is internally consistent
   (97 direct + 136 downstream = 233) and the spot-checked direct names are in the merged
   `changed_type_all`, but **"0 lost, 0 added, 233 explained" is unverifiable from the tree**.  The
   round-8 rule — commit the `envdiff.json`/`.txt` beside the receipt — now applies to all rounds.

8. **`CircleProduct.lean`'s Hatcher "§2.2 (Mayer–Vietoris, and the torus example)" (finding 8)** is a
   citation the reviewer could not confirm from memory; it is a code fix if it is one at all and is
   not resolved here.
