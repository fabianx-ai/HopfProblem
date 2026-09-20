# Review of Lib/reports/round-8/pins/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — the work is sound (every change in the branch is, modulo
universe annotations, a `universe u` line, an explicit `(C := AbelianSheaf Y)`, or one docstring
word; nothing deleted, no hypothesis added, merge preserved the lifts), but the receipt gets the
mechanism of chokepoint 8 wrong and several counts in §3 are off.

Reviewer: r8-pins. Sources: `/home/goblin/hopf-lib-audit` (base `4e15a034`, tip `5ad9ec3c^2`,
merge `5ad9ec3c`, head `39f1d12b`); four scratch elaborations in `/home/goblin/hopf-lib-integration`
(files under `review-pass/r8-pins/Scratch{1,2,3,4}.lean`).

## Findings

1. `[wrong receipt]` **Chokepoint 8's "invisible pin" is real, but the stated mechanism is false.**
   Receipt §1: `germ_stalkIso_hom_nearbyRestrictionUnit` "was pinned invisibly — a bare `{X : TopCat}`
   binder and bare `AddCommGrpCat` arguments, which elaborate at universe 0 under this repo's
   `autoImplicit false`". Scratch 3 (head, `set_option autoImplicit false`, `pp.universes true`):
   ```
   theorem a0 {X : TopCat} (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat X) : True
     -- @a0.{u_1, u_2} : ∀ {X : TopCat.{u_1}} … (F : TopCat.Sheaf.{u_1,u_2,u_2+1} AddCommGrpCat.{u_2} X), True
   theorem a1 … stalkIso U F x = stalkIso U F x            -- a1.{u_1}   polymorphic
   theorem a2 … (nearbyRestrictionUnit U).app F = …         -- a2.{u_1}   polymorphic
   theorem a5 … (hx : inclusion U x ∈ V) : True             -- a5.{u_1}   polymorphic
   theorem a6 {X : TopCat} (F : TopCat.Sheaf AddCommGrpCat X) (V : Opens X) (x : X) (hx : x ∈ V) :
       F.presheaf.germ V x hx = F.presheaf.germ V x hx
     -- @a6 : ∀ {X : TopCat.{0}} (F : TopCat.Sheaf.{0, 0, 1} AddCommGrpCat.{0} X) …   PINNED
   ```
   Bare binders alone become universe *parameters* (`u_1`, `u_2`); `autoImplicit` is irrelevant.
   What pins is `TopCat.Presheaf.germ`, whose `[Limits.HasColimits AddCommGrpCat.{?v}]` instance
   argument is resolved while `?v` is still a metavariable and instance resolution assigns `?v := 0`
   (a3, a4, a6 — every statement containing `germ` — come out at `.{0}`; a1, a2, a5 do not). The base
   statement re-elaborated verbatim (`t3`, Scratch 2) has no universe parameters at all, so the
   observation "it was at universe 0" is correct and the lift to `.{u}` is a genuine lift whose
   `u = 0` instance is the old statement. The receipt's rule "bare `TopCat`/`AddCommGrpCat` ⇒
   pinned" is the wrong detector: the three remaining bare `TopCat.Presheaf AddCommGrpCat X`
   occurrences at head (`HigherDirectImageSheafification.lean:97,102`,
   `ResolutionCohomologyPresheaf.lean:140`) are fully `.{u_1}` (Scratch 4), while a `.{0}`-free
   statement can still be pinned through an instance argument. The receipt should say so; a future
   census that greps `.{0}` will miss this class.

2. `[wrong receipt]` **§3 counts.** With `git grep -o -F '.{0}' 5ad9ec3c^2 -- 'Lib/*.lean'`:
   `SingularCochainSheaf/*` has **32** files with pins (207 pins), not "26"; the set of files §3
   lists as staying pinned "for exactly this reason" carries **280** pins (287 with
   `SingularCochains.lean`'s own 7), not "271 of the 320"; `SingularHomology/Coproduct.lean` has 8
   *lines* but **9** occurrences, while the headline 1,024/320 are occurrence counts. None of this
   affects soundness; it affects the reader's ability to reconcile 320.

3. `[incomplete]` **§6 envdiff.** Of the 398 changed-type source names, 40 live in modules the branch
   did not edit. The receipt names two groups (`SingularCochainSheaf/*`: 29 names; `SphereTwo`: 2)
   and omits the third: `ConstantProductH1` (1), `ConstantProductH1Comparison` (1),
   `ConstantProductH1FibreIndependence` (1), `ConstantProductPositiveFibreIndependence` (5),
   `ConstantSheafH1` (1) — 9 names, all dependents of lifted declarations (the files are listed in §3
   as staying pinned, so the omission is only in the envdiff reconciliation).

4. `[nit]` **"They are the only proof-text edits in this packet."** Four of the `(C := AbelianSheaf Y)`
   insertions are inside theorem *statements*, not proofs: `ResolutionTransgression.lean` (tip)
   l.181–185 (`resolutionTransgressionMorphismOfResolution_eq`-style statement), l.217–221,
   l.231–235, l.267–271. `C` is determined by `pushedResolution f I : CochainComplex (AbelianSheaf Y) ℕ`,
   so the elaborated term is unchanged and the statement at `u = 0` is the same term; the sentence is
   nonetheless inaccurate.

5. `[nit]` **One commit per chokepoint** holds for chokepoints 1–6; chokepoint 7
   (`ConstantSheafCohomology.pullback`) shares `f59653c5` with five consumer files, chokepoint 8
   shares `6f4277d9` with `StalkCriterion.lean`. The receipt's own table makes this visible.

6. `[incomplete]` **Packet items silently already clean.** The packet lists `TopCat.LocalPredicate`
   over ℂ (`Analysis/Complex/SquareRoot.lean`, "1 pin") and "`HasExt` pinned to the hom universe in
   `cochainTransgression`". At base both files have zero `.{0}` (`Ext.{v}` in `cochainTransgression`
   is a universe parameter, not a pin). The receipt does not say these packet items were stale.

No `[unsound]` finding. Specifically checked and clean: no statement changed beyond universe
annotations (global check below), no hypothesis added, no deletion, no `sorry`/`axiom`/
`maxHeartbeats`/`unsafe`/`native_decide`, no `@[simp]`/`private`/`noncomputable` added or removed
(the attribute lines that appear in the diff are the same attribute on a re-universed line), no
`import Hopf` in `Lib/*.lean` at tip or head (the only hits are in `Lib/docs/*.md`), trailers on all
11 commits.

## The four questions in the assignment

**Pin counts.** `git grep -o -F '.{0}' <rev> -- 'Lib/*.lean' | wc -l` and `git grep -l … | wc -l`:
base `4e15a034` **1024 / 99 files**, tip `5ad9ec3c^2` **320 / 48**, merge `5ad9ec3c` 316 / 46,
head `39f1d12b` 293 / 45. The variant `'\.\{0[,}]'` gives one more at both base and tip
(`hasExt_of_enoughInjectives.{0,0,1}` in `Cohomology/SphereTwo.lean`). Receipt's 1024 → 320 confirmed.

**The 8 chokepoints, before/after.** Read from `git diff 4e15a034 5ad9ec3c^2 -- <file>` for all
eight files. In every case the after-statement is the before-statement with `.{0}` → `.{u}`
(`AddCommGrpCat.{0}`, `TopCat.{0}`, `Sheaf.H.{0}`, `Ext.{0}`, `HasExt.{0}`, `ULift.{0}`,
`Ext.addEquiv₀.{0}`, `Ext.mk₀.{0}`, `H.equiv₀.{0}`, `H.map.{0}`) and, for chokepoint 8, bare
`TopCat`/`AddCommGrpCat` → `TopCat.{u}`/`AddCommGrpCat.{u}` (which, per finding 1, is the lift of a
declaration that really was at 0). Global check: I took `git diff -U0` of the branch, normalised
removed lines by `.{0}`→`.{u}`, `.{1}`→`.{u + 1}`, bare `AddCommGrpCat`→`AddCommGrpCat.{u}`,
`TopCat}`→`TopCat.{u}}`, `: Type`→`: Type u`, and compared multisets with the added lines per file.
Residue over all 54 `.lean` files: the `universe u` line (+ blank) in 46 files, the 7
`(C := AbelianSheaf Y)` lines (finding 4), and the docstring word "small" dropped in
`AddCommGroup.lean`. Nothing else. So every `u = 0` instance is literally the old statement.

**`ULift.{u} ℤ` in `unitSheaf`: not a statement change.** The base already read
`AddCommGrpCat.of (ULift.{0} ℤ)` (diff of `AcyclicResolutionH1.lean`, l.54–56), so `u = 0` gives the
old term verbatim. It is also the only possible value: Mathlib's `CategoryTheory.Sheaf.H.{w',w,v,u} F n`
(`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`, printed in Scratch 3) is
`Ext ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) F n`, and
`AddCommGrpCat.of ℤ` lives only in `AddCommGrpCat.{0}`. The merge deleted `unitSheaf` (dup-sheaf item 9)
for `TopCat.ConstantSheaf.integralSheaf.{u} X := sheaf X (AddCommGrpCat.of (ULift.{u} ℤ))`
(`ConstantPushforward/GlobalSections.lean:37`, `.{u}` already at base) — same value, same universe.

**Explicit universe arguments in proofs.** `HasSmallLocalizedShiftedHom.{u + 1}` and
`homEquivCoyonedaHomologyOfIsKInjective.{u + 1}` are inside `letI`/`let` of the proof of
`resolutionDerivedHomCohomologyEquiv` (`ResolutionAbutment.lean:150–153`) — proof text, were `.{1}`.
`ULift.{u + 1} (E₂ f F p q)` is in the *type* of `resolutionPostnikovE₂Iso`
(`ResolutionPostnikov.lean:182`), was `ULift.{1}`; at `u = 0` the level `0+1` is `1`, same statement.
`AddCommGrpCat.{u}` on `stalkFunctor`/`forget` in `FiniteClosedPushforward/Exact.lean` is inside
`let K := …` and `have` lines of `pushforward_exact` — proof text. `(C := AbelianSheaf Y)`: see finding 4.

**§3 `SingularCochains.chains`/`complex`: the obstruction is real and is a protocol obstruction, not
just a consumer-proof one.** Mathlib (`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:30–38`):
```
universe w v u
variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
def singularChainComplexFunctor : C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ
```
The space universe `w` is tied to the coproduct-index universe. Scratch 3 at head:
`HasCoproducts.{u} (ModuleCat.{u} ℤ)` synthesises; `HasCoproducts.{u} (ModuleCat.{0} ℤ)` fails
(`ModuleCat.hasColimitsOfSize` needs `HasColimitsOfSize.{u,u} AddCommGrpCat.{0}`, i.e. `UnivLE.{u,0}`);
`(ModuleCat.of ℤ ℤ : ModuleCat.{1} ℤ)` is a type error (`ℤ : Type`, not `Type 1`); and
`ModuleCat.of ℤ (ULift.{0} ℤ) = ModuleCat.of ℤ ℤ` is not `rfl`. Hence for `X : Type u` the
coefficient object must be an object of `ModuleCat.{u} ℤ`, which the literal `ℤ` is not for `u > 0`;
every polymorphic form (`ULift.{u} ℤ`, `AddCommGrpCat.of (ULift ℤ)`, `ModuleCat.{max u v}`) changes
the `u = 0` object to `ULift.{0} ℤ`, which the protocol ("statement at `u = 0` unchanged") forbids
independently of the four consumer rewrites the receipt cites. Mathlib's own precedent for
polymorphic ℤ coefficients is exactly `ULift.{w} ℤ` (`Sheaf.H`); the protocol-clean route is a new
polymorphic `chains` beside the pinned one with a `u = 0` comparison isomorphism — an addition, not a
lift, correctly outside this packet. Same verdict for `SingularChains.singularComplex` and, by
consequence, `Coproduct.lean` (its `HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ)` follows the
chain complex, as the receipt says). `SphereTwo`: `HasCoveringDimensionLE.of_homeomorph {X Y : Type u}`
(`Dimension/Covering.lean:206`) and `hasCoveringDimensionLE_two_of_homeomorph {B : Type}`
(`Dimension/SphereTwo.lean:37`) confirm the one-universe obstacle; not re-elaborated.

**Merge preservation (16 conflicted files, MERGE.md §2).** At `5ad9ec3c` and `39f1d12b` all 16 have
0 `.{0}`, a `universe u` line, no bare `TopCat`/`AddCommGrpCat` binder; `.{u` counts tip vs head are
equal (e.g. `FiniteClosedPushforward/AcyclicResolutionH1` 57/57, `ResolutionAbutment` 10/10) except
`ResolutionTransgression` 10 → 9 where dup-sheaf's survivor replaced the deleted `Leray.integralSheaf`
line. Chokepoint statements at head: `Sheaf.instAddCommGroupH {X : TopCat.{u}} (F : Sheaf AddCommGrpCat.{u} X)`
(renamed by dfiles-c, universes kept); `subsingleton_h1_of_isFlasque … Subsingleton (Sheaf.H.{u} F 1)`
with `abelianSheaf_hasExt : HasExt.{u} …`; `h0GlobalIso`/`h1GlobalIso`/`globalComplex`/`extZeroGlobalIso`
at `.{u}` over the survivors `TopCat.Sheaf.globalSectionsFunctor X` and
`TopCat.ConstantSheaf.integralSheaf X`. The merge preserved every lift on what survived.

## Claims checked

| claim | status | how |
|---|---|---|
| 1024 pins / 99 files → 320 / 48; 704 lifted, 51 files cleared | verified | `git grep -o -F '.{0}' <rev> -- 'Lib/*.lean'` at base and tip |
| 10 work commits + receipt commit, messages match file sets (1/1/1/1/1/1/14/6/2/24 files) | verified | `git log 4e15a034..5ad9ec3c^2`, `git show --stat` per commit |
| one commit per chokepoint | partly | chokepoints 7, 8 bundled with consumers (finding 5) |
| `cohomologyAddCommGroup` lifted, not deleted; `Ext.instAddCommGroup` body unchanged | verified | diff of `AddCommGroup.lean`; head `instAddCommGroupH` |
| `unitSheaf` value `ULift.{u} ℤ`; `u = 0` unchanged | verified | base had `ULift.{0} ℤ`; Mathlib `Sheaf.H` printed |
| Flasque: whole file `.{u}`, `HasExt.{u}` from `IsGrothendieckAbelian.hasExt` | verified | diff; head l.41–43 |
| chokepoints 4–7 `.{u}` | verified | diffs of the four files; residue check |
| chokepoint 8 "bare binder elaborates at 0 under autoImplicit false" | refuted (mechanism) / verified (observation) | Scratch 1–3, finding 1 |
| `ConstantSheaf.sheaf`, `integralSheaf`, `integralHomGlobalEquiv`, `integralPushforwardHom_comp_bijective` already `.{u}` (packet 08) | verified | `git grep` at base: `TopCat.{u}` on all four |
| §2 files "every declaration now `.{u}`" | verified | none of the 45 files in tip's per-file `.{0}` list; no `: Type` binder left (grep) |
| two `: Type` → `Type u` widenings only (`GlobalSections`, `Fibre`) | verified | diff grep `: Type` |
| explicit universe args are the only proof-text edits | partly | finding 4 |
| `StalkCriterion` round-7 whnf timeout gone | not checked (needs build); round-7 record (`RECEIPT-09.md:36`) confirms the claim's premise |
| §3 `chains` obstruction real; `HasCoproducts.{u} (ModuleCat.{u} ℤ)` available | verified | Scratch 3; Mathlib signature |
| §3 "26 SingularCochainSheaf files", "271 of 320", "8 pins of Coproduct" | refuted (32 files; 280/287; 9 occurrences) | finding 2 |
| SphereTwo one-universe obstacle | verified (source) | `Covering.lean:206`, `Dimension/SphereTwo.lean:37` |
| `Degree1.lean` single pin is in the module docstring | verified | `Degree1.lean:27` |
| §4 lost 682 / added 681, 0 source lost, only `…SheafificationIso._proof_5` lost | verified | python over `envdiff.json`: lost−added = exactly that name |
| 398 changed source types = lifted decls and dependents | verified, list incomplete | grouped by module (finding 3) |
| no module moves | verified | `moves: []`, `ambiguous: []` |
| builds / AxiomAudit / census | not checked | see below |
| no `sorry`/`axiom`/heartbeats/`unsafe`/`native_decide`; attributes unchanged; trailers | verified | grep on branch diff; `git log --format=%(trailers)` |
| `Lib` never imports `Hopf` | verified | `git grep "import Hopf" -- Lib` at tip and head: only `Lib/docs/*.md` |
| MERGE.md: lifts kept on survivors in the 16 files | verified | counts and head statements above |

## Not checked

* The four build lines and the `AxiomAudit`/census results (would need `lake build`; MERGE.md
  records a successful `lake build Lib` at 9149 jobs right after this merge, which I take as the
  after-merge evidence).
* That the round-7 `whnf` timeout in `StalkCriterion.lean` was caused by universe defaulting (the
  file builds at head per MERGE.md; the causal claim itself is untestable without the base build).
* The `ULift`-lifted `chains` "elaborates" claim and the exact consumer error messages in §3 (kept
  out of tree by the author; I verified the underlying universe facts instead, Scratch 3).
* Docstrings/citations: the branch adds no docstrings and changes one word in one; nothing to
  sample.
* The 398 changed types individually; I checked them by module and by the whole-diff residue
  check, not one by one.

## Tool notes

* The receipt's headline counts are `.{0}` *occurrences* while some in-text counts are *lines*
  (`Coproduct.lean`); state the grep once and use it throughout.
* An "invisible pin" cannot be found by grep. The receipt should record the detector that does work:
  `#check` with `pp.universes true` (or `#print` and look for a missing `.{…}` on the constant). A
  census script that dumps universe parameters per declaration (the envdiff dumps already have the
  types) would have found chokepoint 8 without a round-7 build failure, and would prove "every
  declaration is now `.{u}`" instead of asserting it.
* The `envdiff.json` `changed_type_proof_naming` list is names only; adding the module (as `lost`/
  `added` entries have) would make the per-module reconciliation in §6 checkable directly.
* The whole-diff residue check (normalise universe annotations, compare removed vs added lines per
  file) took one script and settled "`u = 0` is the old statement" for all 54 files at once; a
  universe-lift receipt could ship that residue as its evidence.
