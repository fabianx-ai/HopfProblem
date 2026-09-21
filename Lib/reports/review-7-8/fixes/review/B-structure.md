# Review of fix round — slice B (structure: deletions, re-additions, moves, probes)

**Verdict: ACCEPT WITH FINDINGS** — every one of the five deletions has a twin I confirmed by
elaboration (the four `_one` lemmas close by the bare twin term at `n = 0` / `n = 1`, and
`Fin.tailHeadAddEquiv` is `rfl`-equal to the Mathlib composite as a structure and in both
directions as a function); the two re-added lemmas are literally the deleted statements; all
consumers are rerouted; the rename map is correct and complete; the AddCommGroup docstring's
mechanism reproduces; the receipts are accurate. What remains is small: the new
`Hopf/Proof/AxiomAudit.lean` (like `Lib/AxiomAudit.lean`) is reachable by no default target and
imported by nothing, so nothing enforces it; two commit-hygiene and counting nits.

Branches reviewed: `fix/names-dfiles` (`0ae6c1b1..97a28ff0`, 6 commits), `fix/moved`
(`9725a329..18514411`, 6), `fix/dup-dfa` (`6efd75bf..efbd141e`, 6). Head compared: `8da46f0d`.
Scratch: `/home/goblin/.claude/jobs/06995e68/tmp/review-fix/B/{B1,B2}.lean` with outputs
`B1.out`, `B2.out` (two elaborations in `/home/goblin/hopf-lib-integration`).

## Findings

1. `[nit]` **`Hopf/Proof/AxiomAudit.lean` is enforced by nothing.** `lakefile.toml` declares
   `[[lean_lib]] name = "Hopf"` with no `roots`/`globs`, so the lib's default root is the module
   `Hopf`, and there is no `Hopf.lean` at head (`git ls-tree 8da46f0d` shows only the directory).
   The file is imported by nothing (`git grep Hopf.Proof.AxiomAudit 8da46f0d -- '*.lean'` → 0).
   It is therefore built only when someone types `lake build Hopf.Proof.AxiomAudit` explicitly —
   which the fixer and the coordinator did (`names-dfiles.md` "Build lines", `MERGE.md` check row),
   and I re-ran the four probes myself (`B1.out`: each `[propext, Classical.choice, Quot.sound]`).
   The same is true of `Lib/AxiomAudit.lean` (`Lib.lean` does not import it), so this is
   consistent with the existing convention, but the receipt's "reachable" sentence should say
   "only by explicit module target; not in `defaultTargets`". The probes are exactly the four
   theorems of `Hopf/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean` (lines 66, 112, 141, 157 —
   the file has no other `theorem`/`def`/`instance`), and the docstring's claim that nothing
   reachable from `mathoverflow_1973` mentions them holds trivially: the four names occur in no
   `.lean` file other than `SphereTwo.lean` and `AxiomAudit.lean`.

2. `[nit]` **Commit subject format, `fix/moved` `9725a329`.** Subject is `Lib.lean,
   Hopf/Recognition.lean, SurgeryCollapse.lean: drop duplicate imports`, not the prescribed
   `Lib/<path>: <what>` (the fix item legitimately spans three files; the body names all three and
   the finding). Cosmetic.

3. `[nit]` **Probe count wording.** `names-dfiles.md` says `Lib/AxiomAudit.lean` "goes from 3312
   to 3314 `#print axioms` lines" — correct for the branch (I count 3312 → 3314; `dup-dfa` takes it
   to 3308; head has 3310). `MERGE.md` reports "3,302 probes" for `Lib.AxiomAudit` at the merged
   head; the head file has 3,310 `#print axioms` lines. Either 8 probes print nothing or the number
   was copied from a build log with a different definition; Slice C's item, flagged here because the
   discrepancy is created by this slice's branches (−4 +2).

4. `[nit]` **`moved.md` line reference.** "consumer … `SurgeryCollapse.lean:5204`" — the `let G :=`
   is at 5204 at base and 5204–5207 after the edit; fine. The receipt's `Lib.lean` claim
   ("`git grep -E 'IndexDisorder|Curve.CircleGluing' Lib.lean` now gives 2 lines (was 5)") is
   exact (5 → 2 at head).

Nothing `[unsound]`, `[wrong receipt]`, `[incomplete]` or `[rule]` found after the checks below.

## Deletions — statement vs twin (all five)

**(a) `TopCat.SingularSmallChains.homotopy_on_cocycle_one`** (base `Basic.lean:538`):
```
{K L : CochainComplex AddCommGrpCat.{0} ℕ} {f g : K ⟶ L} (h : Homotopy f g) (x : K.X 1)
(hx : K.d 1 2 x = 0) : f.f 1 x = L.d 0 1 (h.hom 1 0 x) + g.f 1 x
```
twin `CochainComplex.homotopy_on_cocycle_succ` (`CocycleEvaluation.lean:41`, universe `u`):
```
{K L : CochainComplex AddCommGrpCat.{u} ℕ} {f g : K ⟶ L} (h : Homotopy f g) (n : ℕ) (x : K.X (n + 1))
(hx : K.d (n + 1) (n + 2) x = 0) : f.f (n + 1) x = L.d n (n + 1) (h.hom (n + 1) n x) + g.f (n + 1) x
```
`pp.universes` (`B1.out`): `homotopy_on_cocycle_succ.{u_1}` with `AddCommGrpCat.{u_1}` — a real
universe parameter, no hidden pin. At `u = 0`, `n = 0` the index terms are `0 + 1`, `0 + 2`, `0`
against the literals `1`, `2`, `0`; these are `Nat` literals, defeq by `Nat.add` reduction, and my
`example` with the base statement verbatim closes by the bare term
`CochainComplex.homotopy_on_cocycle_succ h 0 x hx` (no `simp`, no `convert`). Stronger twin.

**(b) `smallCochain_cocycle_lift_exact_one`** (base l.552) vs `smallCochain_cocycle_lift_exact_succ`
(`CochainHomotopy.lean:38`): identical binders `{X : Type} [TopologicalSpace X] {I : Type}
(A : AddCommGrpCat.{0}) (U) (e) (he)`, then `(n : ℕ)` and `1`/`2` replaced by `n + 1`/`n + 2`,
`0` by `n`. Closes by `smallCochain_cocycle_lift_exact_succ A U e he 0 phi hphi`. Stronger twin.

**(c) `smallCochain_boundary_of_restriction_boundary_one`** (base l.585) vs `…_succ`
(`CochainHomotopy.lean:78`): same pattern (`chi` in degree `0` ↔ `n`, `phi` in `1` ↔ `n + 1`).
Closes by `… A U e he 0 phi hphi chi hchi`. Stronger twin.

**(d) `cochainRestriction_homologyMap_isIso_one`** (base l.607) vs
`cochainRestriction_homologyMap_isIso` (`CochainHomotopy.lean:103`, `(n : ℕ)`,
`IsIso (homologyMap (cochainRestriction A U) n)`). Closes by `… A U e he 1`. `pp.universes`: all
universe arguments concrete (`Type`, `.{0}`), same as the deleted statement. Stronger twin.

The branch diff of `Basic.lean` removes exactly the four docstring+theorem blocks and adds nothing
(`grep -c '^+'` → 1, the `+++` header); `cochainMap_d` survives and is used by `CochainHomotopy.lean`.
The fixer's `Check.lean` (`/home/goblin/.claude/jobs/06995e68/tmp/fix-dup-dfa/Check.lean`) contains
the same four examples; I re-elaborated them independently in `B1.lean`.

**(e) `Fin.tailHeadAddEquiv`** (base `IntegerPresentation.lean`):
```
def Fin.tailHeadAddEquiv (n : ℕ) : (Fin (n + 1) → ℤ) ≃+ ((Fin n → ℤ) × ℤ) where
  toFun v := (fun i => v i.succ, v 0);  invFun v := Fin.cons v.2 v.1; …
```
twin (Mathlib `LinearAlgebra/Pi.lean:663` `Fin.consLinearEquiv` = `Fin.consEquiv` + linearity;
`LinearAlgebra/Prod.lean:658` `LinearEquiv.prodComm` = `Prod.swap`):
```
((Fin.consLinearEquiv ℤ fun _ : Fin (n + 1) => ℤ).symm.trans (LinearEquiv.prodComm ℤ ℤ (Fin n → ℤ))).toAddEquiv
```
I restated the deleted definition verbatim as `Fin.tailHeadAddEquiv'` and checked, all by `rfl`
(`B1.out`, exit 0): `⇑(tailHeadAddEquiv' n) = ⇑(twin n)`, `⇑(tailHeadAddEquiv' n).symm =
⇑(twin n).symm`, the pointwise forms on `v` and on `p`, and the structure equality
`tailHeadAddEquiv' n = twin n`. So the twin is definitionally equal as a function in both
directions and as a bundled `≃+`; the composite is moreover a `≃ₗ[ℤ]` (stronger). The single
consumer `exists_indexTwoBasis_extension` (`SurgeryCollapse.lean:5204–5207`) builds `G` from the
composite and its two proof obligations are unchanged in the diff.

## Re-added lemmas — original vs new

`git log -S freeGroup_invariant_iff --all`: deleted at `86377b36` (`refactor: delete
Lib/LinearAlgebra/Dual/Contragredient.lean`). Original (`86377b36^`, last declaration):
```
theorem LinearRepresentation.freeGroup_invariant_iff {A R N : Type*} [CommSemiring R]
    [AddCommMonoid N] [Module R N] (ρ : FreeGroup A →* (N ≃ₗ[R] N)) (x : N) :
    (∀ g, ρ g x = x) ↔ ∀ a, ρ (FreeGroup.of a) x = x
```
Re-added `FreeGroup.forall_apply_eq_self_iff` (`Lib/GroupTheory/FreeGroup/Invariant.lean:37`):
identical binders, hypotheses, conclusion; proof identical except `_root_.map_inv` /
`_root_.map_mul` (needed: `FreeGroup.map_inv` is Mathlib `FreeGroup/Basic.lean:1028`, in the
namespace). Placement: a `FreeGroup` file, as `AUDIT.md` asked. Module docstring present, `Lib.lean`
imports it, `Lib/AxiomAudit.lean` probes it. The four `ofMultiplicative*` helpers and
`contragredient*` stay deleted — the fix list (`REVIEW-7-8.md` §3 "names") asked only for
`freeGroup_invariant_iff`; the receipt says so and defers the receipt-text part to `fix/receipts`.

`git log -S fibre_constant_of_ker_le --all`: deleted at `fff26c16` with `SurjectiveDescent.lean`.
Original (`4e15a034:Lib/Algebra/Group/SurjectiveDescent.lean:35`):
```
theorem fibre_constant_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hker : f.ker ≤ g.ker) : ∀ a b, f a = f b → g a = g b
```
Re-added `MonoidHom.apply_eq_apply_of_ker_le` (`Lib/Algebra/Group/Ker.lean:37`): `(a b : A)
(hab : f a = f b) : g a = g b` — the same Pi type with the two quantifiers and the implication
moved before the colon; proof identical modulo `_root_.`. Placement sensible (only kernel file in
`Lib/Algebra/Group/`); module docstring cites `Mathlib/Algebra/Group/Subgroup/Basic.lean` for
`liftOfSurjective`, which is right (`Basic.lean:932`). `Lib.lean` and `Lib/AxiomAudit.lean` updated.
`descendHomOfSurjective`/`_comp` stay deleted for their round-8 Mathlib twins (not this round's item).

## Consumers, rename map, imports, duplicates

* Old names at head in `Lib Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean` (excluding
  `Lib/reports`, `Lib/reviews`): 0 hits for each of the four `_one` names, `tailHeadAddEquiv`,
  `exists_split_of_ker_eq_range`, `exists_addEquiv_split_of_ker_eq_range`,
  `LinearEquiv.natAbs_apply_one`, `freeGroup_invariant_iff`, `fibre_constant_of_ker_le`,
  `SurjectiveDescent`, `Dual.Contragredient`, `Lib.Topology.Sheaves.Cohomology.SphereTwo`.
  New names present: renamed lemmas at `IntegerPresentation.lean:245/287/295`, consumers
  `SurgeryCollapse.lean:5183` (`exists_prodAddEquiv_…`) and `Hopf/Recognition.lean:3025`
  (`Int.natAbs_linearEquiv_apply_one`); `#check` of all three in `B1.out` shows the statements
  unchanged from base (same binders `{R} [CommRing R] {A B} … (i) (p) hi hp hk`, same conclusion).
* `rename.txt`: 3 lines, direction `<new> <old>` (matches the rule "after→base"). Complete: the
  round envdiff lists exactly 5 lost / 3 added source names, none of them a renamed name, 0 moves,
  0 ambiguous — so the map fired for all three renames; there are no other renames on the three
  branches (branch diffs read in full). The three per-branch `envdiff.txt` files still exist under
  `/home/goblin/.claude/jobs/06995e68/tmp/fix-{names-dfiles,moved,dup-dfa}/` and their first lines
  match the receipts (38254 → 38256 / 38250 / 38250).
* `import Hopf` under `Lib/`: none in any `.lean` (only in `Lib/docs/*.md` and `.lean.txt` logs).
  `Lib.lean`: 440 → 442 (`names-dfiles`) → 439 at head (−3 duplicate lines from `moved`; no other
  branch touched it). Both new modules have module docstrings and `## Main results`.
* Duplicate imports at head (sweep over every `.lean`, `sort | uniq -d` on `import` lines): exactly
  `Lib.Algebra.Module.IntegerPresentation` twice in `Hopf/Proof/SphereTopology.lean`,
  `Hopf/SphereTopology.lean`, `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` — the three
  `MERGE.md`/`moved.md` admit. Removed by `9725a329`: `CircleGluing` ×2 and `IndexDisorder` ×1 in
  `Lib.lean`, `IndexDisorder` ×1 each in `Hopf/Recognition.lean` and `SurgeryCollapse.lean`, as
  the receipt's table says.

## `AddCommGroup.lean` docstring cause — tested

`B2.lean` (Mathlib-only imports, the file's three; `Lib` not imported):
(a) `F : TopCat.Sheaf AddCommGrpCat.{u} X`, `AddCommGroup (Sheaf.H.{u} F n) := inferInstance` →
`failed to synthesize AddCommGroup (Sheaf.H F n)`; (b) `F : CategoryTheory.Sheaf
(Opens.grothendieckTopology X) AddCommGrpCat.{u}` → synthesized (the only diagnostic is
"depends on 'Ext.instAddCommGroup', which is noncomputable", i.e. the instance was found);
(c) explicit `Ext.instAddCommGroup` for the `TopCat.Sheaf`-typed `F` → elaborates; (d) with
`attribute [local reducible] TopCat.Sheaf` → synthesized. Mathlib source: `TopCat.Sheaf` is
`nonrec def Sheaf : Type max u v w := Sheaf (Opens.grothendieckTopology X) C deriving Category`
(`Topology/Sheaves/Sheaf.lean:108`); `Sheaf.H` is `abbrev H (n : ℕ) : Type w' := Ext (…) F n`
(`Sites/SheafCohomology/Basic.lean:59`); `Ext.instAddCommGroup` is at
`Algebra/Homology/DerivedCategory/Ext/Basic.lean:239` and `GrothendieckCategory/HasExt.lean`
contains no `AddCommGroup`. The head docstring states exactly this and keeps the load-bearing
conclusion; the declaration itself is untouched by the branch (diff is docstring-only).
`SheafificationLocal.lean` paths: `stalkFunctor_map_unit_toSheafify_isIso` at `Sheafify.lean:137`,
`germ_eq` at `Stalks.lean:456` — both as the fix says.

## Docstrings on these branches (all read against the statements)

`LocalContributionsNaturality.lean` (7): each lists hypotheses then conclusion; directions checked
against the statements (`homologyEquiv_symm_single`: `symm (Pi.single i a) = map (inclusion) a`;
`homologyEquiv_inclusion`: the reverse; `homologyEquiv_map`: coordinates of the pushforward =
componentwise pushforward of coordinates; `componentConnecting_enlarge`: pushing the `i`-th
component along `U ∩ V i ⊆ U' ∩ V i` gives the two-set connecting map of `U', V i`) — correct.
`RadialFilling.lean` (12): correct, including `radialTime` = `projIcc 0 1 (1 − ‖v‖)` "1 at the
centre, 0 on and outside the sphere" and the `3/4`, `1/4` plateaus. `GlobalUnitPredicates.lean`:
the four dischargers exist at the cited places (`GlobalSections.lean:82`,
`GlobalKernelSmall.lean:137/142`, `BarycentricSmallChains.lean:34`). `Hopf/Proof/…/CutTransport.lean`:
`passageNormalProduct_det` exists (l.825) and is now in the inventory. `coordMatrix_eq_toMatrix`
docstring matches its statement. Milnor "§3, Thm. 3.4" (a triad with Morse number 0 is a product
cobordism) is the right item to my knowledge (Slice C's domain; flagging that I am ~90 % sure).

## Hygiene (§9) over the three branch diffs

No `sorry`, `axiom`, `admit`, `maxHeartbeats`, `unsafe`, `native_decide`; no `@[simp]` added or
removed; no `noncomputable` added; no `private` removed. Files touched under `Lib/reports/`: only
each branch's own receipt (`fixes/names-dfiles.md`, `fixes/moved.md`, `fixes/dup-dfa.md`); nothing
under `Lib/reviews/`, `TEXTBOOK.md`, `DECOMPOSITION.md`, `CORRESPONDENCE.md`. All 18 commits carry
both trailers (`Co-Authored-By: Claude Opus 5`, `Claude-Session: …session_01VZt4JDgce67x5QTThwQ3E2`),
one commit per fix item, bodies name the finding closed. No later branch touched any file these
three edited (`git log 62d45257..9a6e125a -- <file>` lists only these branches' commits), so the
branch tips equal the head for every file above.

## Claims checked

| claim | result | how |
|---|---|---|
| four `_one` lemmas are literally `_succ`/`isIso` at `n = 0`/`1`, closed by the bare twin term | verified | `B1.lean` examples with the base statements verbatim, `exact`-style terms, exit 0 |
| `homotopy_on_cocycle_succ` is universe-polymorphic, `u = 0` recovers the old statement | verified | `pp.universes` in `B1.out`: `.{u_1}` on `AddCommGrpCat`, everything else fixed |
| `Fin.tailHeadAddEquiv` is `rfl`-equal to the Mathlib composite, both directions | verified | five `rfl` examples incl. structure equality, `B1.out` |
| twin of `tailHeadAddEquiv` "strictly stronger" | verified | composite is a `≃ₗ[ℤ]`; `.toAddEquiv` is the old object |
| `forall_apply_eq_self_iff` = deleted `freeGroup_invariant_iff` (binders, hyps, conclusion) | verified | `git show 86377b36^:…Contragredient.lean` vs head file, textual diff = name + `_root_.` |
| `apply_eq_apply_of_ker_le` = deleted `fibre_constant_of_ker_le` | verified | `git show 4e15a034:…SurjectiveDescent.lean:35` vs head; same Pi type |
| `Hopf/Proof/AxiomAudit.lean` probes exactly the four moved theorems, axioms = {propext, choice, Quot.sound} | verified | `SphereTwo.lean` has exactly 4 declarations; `#print axioms` re-run in `B1.out` |
| "no declaration reachable from `mathoverflow_1973` mentions them" | verified | the four names occur only in `SphereTwo.lean` and `AxiomAudit.lean` |
| `lake build Hopf.Proof.AxiomAudit` reachable without an import in `Final.lean` | verified / qualified | file imported by nothing; `Hopf` lib has no root module; explicit target only (finding 1) |
| AddCommGroup docstring cause (`TopCat.Sheaf` non-reducible `def`; site-typed and reducible variants synthesize) | verified | `B2.out` (a) fails, (b)(c)(d) synthesize; Mathlib `Sheaf.lean:108`, `SheafCohomology/Basic.lean:59` |
| Mathlib paths: `Ext.instAddCommGroup` `DerivedCategory/Ext/Basic.lean:239`; `HasExt.lean` no `AddCommGroup`; `Sheafify.lean:137`; `Stalks.lean:456`; `liftOfSurjective` `Subgroup/Basic.lean`; `FreeGroup.map_inv` `:1028`; `LinearEquiv.mul_apply` `Equiv/Basic.lean:109` | verified | grep in `.lake/packages/mathlib` |
| rename map direction `<new> <old>`, 3 entries, complete | verified | `rename.txt`; round envdiff 0 moves and renamed names absent from lost/added |
| renamed statements unchanged | verified | branch diff (name-only hunks) and `#check` in `B1.out` |
| all consumers of deleted/renamed names rerouted | verified | `git grep` at head over the consumer set, 0 hits for 13 old names |
| `Lib` imports no `Hopf` | verified | `git grep '^import Hopf\|^public import Hopf' 8da46f0d -- Lib Lib.lean` → only docs/logs |
| new modules in `Lib.lean` with module docstrings | verified | `Lib.lean` diff; both files' `/-! # … -/` |
| duplicate imports removed as tabled; exactly three remain (`IntegerPresentation` ×3 files) | verified | full-tree sweep at head |
| `Lib.lean` 440 → 442; `AxiomAudit` 3312 → 3314 `#print axioms` | verified | counts at base / branch tip |
| `MERGE.md` "3,302 probes" | partly | head has 3,310 `#print axioms` lines (finding 3) |
| `MERGE.md`: lost 5 = 4 `_one` + `tailHeadAddEquiv`, added 3 = 2 re-adds + `coordMatrix_eq_toMatrix` | verified | `envdiff.txt` LOST/ADDED lines |
| per-branch envdiff summaries in the three receipts | verified | scratch `envdiff.txt` files still present, first lines match |
| `coordMatrix` deletion declined for the ~10-site threshold; documented-twin fallback allowed | verified | `REVIEW-7-8.md` §3 "moved" says "(or document the twins)"; `coordMatrix_eq_toMatrix` added, proof is the reviewer's |
| `GlobalUnitH1Criterion.lean` gone so the `_one` blocker is gone | verified | no file by that name at head; `r8-dup-hom.md` row "Item 10 blocker" note |
| dischargers named in `GlobalUnitPredicates.lean` exist at the cited lines | verified | grep at head |
| hygiene §9, trailers on 18 commits, receipts-only edits under `Lib/reports` | verified | branch diffs, `git show -s --format=%B` |
| `w4-w1-solution` reroute note (finding 4) recorded, no code change | verified | commit body `f544da65` and receipt §5 |

## Not checked

* The actual `lake build` runs (forbidden); I relied on the receipts' build lines plus my own two
  elaborations against the built head. The `lib_stock_census.py --check` result was not re-run.
* The Milnor Theorem 3.4 item number beyond memory (no copy of the book here); Slice C's remit.
* Whether the `_proof_n` auxiliaries in the round envdiff (51 lost / 47 added, "not judged")
  contain anything beyond the fixers' explanations — Slice A's universe lifts dominate that list.
* `r8-dfiles-c` finding 5 (dead import of `SphereTwo` in `Hopf/Proof/Final.lean`) — a design note,
  not a fix item.

## Tool notes

* A twin claim should ship as a checked-in `example` (base statement verbatim, proved by the bare
  twin term), not a sentence; `dup-dfa` did this in scratch and I had to redo it. A
  `Lib/reports/…/fixes/twins/*.lean` folder built by `lake build` would make "twin is an instance"
  mechanically true.
* `envdiff.py` cannot see a Mathlib twin, so every Mathlib-twin deletion is a `FAIL` needing prose;
  an `--accept-lost <name>=<twin expression>` option that elaborates `example : <old type> := <twin>`
  would close that gap.
* `Hopf/Proof/AxiomAudit.lean` and `Lib/AxiomAudit.lean` are outside every default target; a
  `[[lean_lib]] name = "Audit"` with `roots = ["Lib.AxiomAudit", "Hopf.Proof.AxiomAudit"]` in
  `defaultTargets` would make the probes part of the build instead of a manual step.
* Receipts should quote line numbers at the branch tip and say so; several drifted by the +11/−8
  of sibling branches, which costs the reviewer time to reconcile even though all were right.
