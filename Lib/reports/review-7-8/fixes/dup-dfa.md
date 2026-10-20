# Fix receipt: dup-dfa

Branch `fix/dup-dfa`, base `62d45257` (`lib/integration`), worktree `/home/goblin/hopf-fix-dup-dfa`,
Lean/Mathlib v4.33.0.  Closes the code-side findings of `Lib/reports/review-7-8/r8-dup-hom.md`,
`r8-dup-sheaf.md` and `r8-dfiles-a.md` assigned to this seat.  Five commits plus this receipt.

## Findings

### 1. r8-dup-hom, claims table "Item 10 blocker" — CLOSED (deletion)

The dup-hom receipt (`Lib/reports/round-8/dup-hom/RECEIPT.md` §7 item 3, "`SingularSmallChains/
Basic.lean` degree-one lemmas: blocked") recorded four lemmas in
`Lib/AlgebraicTopology/SingularSmallChains/Basic.lean` as instances of general lemmas that it could
not retire, because the two live consumers of the middle two were at
`Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitH1Criterion.lean:92,135`, owned by another
seat.  The review's note confirms that `GlobalUnitH1Criterion.lean` was deleted later in round 8
(commit `0d8e2b19`, branch `r8/dup-sheaf`), so the blocker no longer exists at `39f1d12b`/
`62d45257` — verified: `git grep` for the four names over `Lib Hopf Solution.lean S6.lean
S6Shortcuts.lean Challenge.lean` at base found only their own definitions and eight
`#check`/`#print axioms` lines in `Lib/AxiomAudit.lean`.

All four are literally the `n = 0` (resp. `n = 1`) instance of a surviving twin.  Checked by an
`example` per lemma, stating the deleted statement verbatim (binder names, implicitness and all)
and proving it by the twin applied at the stated argument — no `simp`, no conversion:
`/home/goblin/.claude/jobs/06995e68/tmp/fix-dup-dfa/Check.lean`, one `lake env lean` run, exit 0.

| deleted (Basic.lean, base) | surviving twin | instance |
|---|---|---|
| `TopCat.SingularSmallChains.homotopy_on_cocycle_one` (l.538) | `CochainComplex.homotopy_on_cocycle_succ` (`Lib/Algebra/Homology/Homotopy/CocycleEvaluation.lean:41`, universe-polymorphic `{u}`) | `h 0 x hx` at `u = 0` |
| `smallCochain_cocycle_lift_exact_one` (l.552) | `TopCat.SingularSmallChains.smallCochain_cocycle_lift_exact_succ` (`SingularSmallChains/CochainHomotopy.lean:38`) | `A U e he 0 phi hphi` |
| `smallCochain_boundary_of_restriction_boundary_one` (l.585) | `smallCochain_boundary_of_restriction_boundary_succ` (`CochainHomotopy.lean:78`) | `A U e he 0 phi hphi chi hchi` |
| `cochainRestriction_homologyMap_isIso_one` (l.607) | `cochainRestriction_homologyMap_isIso` (`CochainHomotopy.lean:103`) | `A U e he 1` |

The twins are strictly more general (every `n`, and universe-polymorphic in the first case), so
nothing is lost.  `TopCat.SingularSmallChains.cochainMap_d`, which sits immediately above the
deleted block and is used by `CochainHomotopy.lean`, stays.  The module docstring of `Basic.lean`
does not mention any of the four, so it needed no edit.

Consumers rerouted: the eight `#check`/`#print axioms` lines in `Lib/AxiomAudit.lean`
(l.4144–4151 at base) were dropped rather than retargeted, because all four twins are already
probed there (`Lib/AxiomAudit.lean:5757–5767`).  No other consumer existed.

Commit `6efd75bf`.

### 2. r8-dup-sheaf finding 3 — CLOSED (docstring)

`Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitPredicates.lean` module docstring said the
four predicates "are discharged in `GlobalKernelSmall.lean` and `BarycentricSmallChains.lean`".
`GlobalUnitSurjective` is not among them: it is discharged by
`TopCat.SingularCochainSheaf.globalCochainUnit_surjective` in
`Lib/Topology/Sheaves/SingularCochainSheaf/GlobalSections.lean:82`.  The sentence now names the
discharging declaration and file for each predicate, checked against the sources:

* `GlobalUnitSurjective` — `globalCochainUnit_surjective`, `GlobalSections.lean:82`
* `GlobalKernelLocallySmall` — `globalKernelLocallySmall`, `GlobalKernelSmall.lean:137`
* `SmallKernelGlobal` — `smallKernelGlobal`, `GlobalKernelSmall.lean:142`
* `HasSmallChainEquivalences` — `hasSmallChainEquivalences_barycentric`,
  `BarycentricSmallChains.lean:34`

The "consumed in `GlobalUnitPositive.lean`" clause is kept (all four appear there).
Commit `b24b4d32`.

### 3. r8-dfiles-a finding 5, first half — CLOSED (docstring)

`Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean` module docstring inventoried 41 of the
file's 42 declarations; `MorseCancellation.passageNormalProduct_det` (l.824) was missing.  Added
to the sheet-passage group directly after `passageNormalProduct` (l.820), the definition it is
about.  Three docstring lines re-wrapped to stay under 100 columns; no other inventory entry
changed.  Commit `1b69a172`.

### 4. r8-dfiles-a finding 5, second half — CLOSED (docstrings)

`Lib/Geometry/Manifold/Morse/RadialFilling.lean` had a module docstring but no declaration
docstring.  All twelve declarations now have one; each lists the declaration's hypotheses first
and then states its conclusion, read off the statement:
`RadialFilling.direction`, `direction_coe`, `direction_of_mem_sphere`, `radialTime`,
`coe_radialTime`, `radialTime_le_quarter`, `three_quarters_le_radialTime`,
`contMDiffAt_radialTime`, `filling`, `filling_eq_center`, `filling_eq_boundary`,
`filling_on_sphere`.  No statement, proof, name or attribute was touched.  Commit `4e322a56`.

### 5. r8-dfiles-a finding 7 — CLOSED (citation)

`Lib/Geometry/Manifold/Morse/CutTransport.lean` references block cited Milnor, *Lectures on the
h-cobordism theorem*, "§3 (sublevel sets across a regular interval)".  §3 is "Elementary
cobordisms"; the statement in question (a cobordism with no critical points is a product) is
Theorem 3.4 there, as the review states.  The parenthesis is replaced by the item number:
"§3, Thm. 3.4".  Commit `64fdefb2`.

## Builds

Per edited module, foreground, from the worktree root:

```
lake build Lib.AlgebraicTopology.SingularSmallChains.Basic                 done 0
lake build Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnitPredicates  done 0
lake build Lib.Geometry.Manifold.Morse.RadialFilling                       done 0
lake build Lib.Geometry.Manifold.Morse.CutTransport                        done 0
lake build Hopf.Proof.Geometry.Manifold.Morse.CutTransport                 done 0
```

After the deletion, the full set:

```
lake build Lib                                 lib 0     (9144 jobs, Build completed successfully)
lake build Solution S6Shortcuts S6 Challenge   chain 0   (9196 jobs, Build completed successfully)
lake build Lib.AxiomAudit                      audit 0
python3 scripts/lib_stock_census.py --check    census 0
  stock declarations under Hopf/: 123  (prefixes: 222, prefixes now absent from Hopf/: 194)
  ratchet PASS: 123 <= baseline 1648
```

`Lib.AxiomAudit` axiom lines are exactly `[propext, Classical.choice, Quot.sound]`,
`[propext, Quot.sound]` and `[propext]`; no `sorryAx`, no error.  The only `sorry` warning in the
chain is the pre-existing `Challenge.lean:42` challenge statement, unchanged from the base.

## Environment diff

Base dump taken before the first edit, after dump after the last; no renames, so no
`--rename`.  `python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl
dump_after.jsonl`:

```
constants before 38254 after 38250 (keys 38152 38148)
lost 4 added 0 of which source declarations: 4 0 ; names with changed type 0 of which source: 0
  LOST TopCat.SingularSmallChains.cochainRestriction_homologyMap_isIso_one
  LOST TopCat.SingularSmallChains.homotopy_on_cocycle_one
  LOST TopCat.SingularSmallChains.smallCochain_boundary_of_restriction_boundary_one
  LOST TopCat.SingularSmallChains.smallCochain_cocycle_lift_exact_one
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1): (none)
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
```

The `FAIL` verdict is the tool's standing verdict for any lost name.  Every lost name is one of
the four deleted `_one` lemmas of finding 1, each with its surviving twin named in the table
above and in the commit body of `6efd75bf`; no auxiliary was lost, nothing was added, and no type
changed — the four docstring commits are invisible to the environment, as expected.

## Commits

`62d45257..64fdefb2` (5 commits, this receipt to follow):

```
6efd75bf Lib/AlgebraicTopology/SingularSmallChains/Basic.lean: retire the four degree-one cochain lemmas
b24b4d32 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitPredicates.lean: name the right discharger per predicate
1b69a172 Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean: complete the module docstring inventory
4e322a56 Lib/Geometry/Manifold/Morse/RadialFilling.lean: docstring every declaration
64fdefb2 Lib/Geometry/Manifold/Morse/CutTransport.lean: sharpen the Milnor h-cobordism citation
```
