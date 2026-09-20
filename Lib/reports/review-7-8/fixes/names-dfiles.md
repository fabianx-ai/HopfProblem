# Fix round: `r7-names`, `r8-dfiles-b`, `r8-dfiles-c` (code-side findings)

Agent `names-dfiles`.  Worktree `/home/goblin/hopf-fix-names-dfiles`, branch `fix/names-dfiles`,
base `62d45257` (`lib/integration`), Lean v4.33.0 / Mathlib v4.33.0.
Scratch `/home/goblin/.claude/jobs/06995e68/tmp/fix-names-dfiles/`.

Scope: the code-side findings named in the assignment and in `Lib/reviews/REVIEW-7-8.md` §3
under `names`, `dfiles-b` and `dfiles-c`.  Receipt corrections in `Lib/reports/round-7/…` and
`Lib/reports/round-8/…` are owned by another agent and were not touched.

## Findings

### 1. `r7-names` finding 1 — `freeGroup_invariant_iff` had no surviving twin  — **closed**

`LinearRepresentation.freeGroup_invariant_iff` was deleted with
`Lib/LinearAlgebra/Dual/Contragredient.lean` at commit `86377b36`; `AUDIT.md` l.520 had asked
for a *move* to a `FreeGroup` file.  It is restated in the new module
`Lib/GroupTheory/FreeGroup/Invariant.lean` (module docstring, `## Main results` bullet,
declaration docstring):

```
FreeGroup.forall_apply_eq_self_iff {A R N : Type*} [CommSemiring R]
    [AddCommMonoid N] [Module R N] (ρ : FreeGroup A →* (N ≃ₗ[R] N)) (x : N) :
    (∀ g, ρ g x = x) ↔ ∀ a, ρ (FreeGroup.of a) x = x
```

Binders, hypotheses and conclusion are literally those of the deleted theorem
(`git show 86377b36^:Lib/LinearAlgebra/Dual/Contragredient.lean`, last declaration); only the
name and namespace changed (`LinearRepresentation` → `FreeGroup`, Mathlib-style
`forall_…_iff`).  The proof is the deleted one — `FreeGroup.induction_on`, `LinearEquiv.mul_apply`
(`Mathlib/Algebra/Module/Equiv/Basic.lean:109`) — with two adjustments forced by the new
namespace: `map_inv` and `map_mul` are written `_root_.map_inv` / `_root_.map_mul`, because
`FreeGroup.map_inv` (`Mathlib/GroupTheory/FreeGroup/Basic.lean:1028`) and `FreeGroup.map_mul`
shadow the `MonoidHom` versions inside `namespace FreeGroup`.  Nothing but Mathlib is used.

The four `ofMultiplicative*` helpers of the deleted file were **not** restated: the proof does
not need them (the assignment made them conditional on that) and they had no consumer.  The
remaining two deleted declarations, `contragredient` / `contragredient_apply`, keep their
round-7 twin `Representation.dual` up to `LinearEquiv.toLinearMap`; saying so in the round-7
receipt and in `Lib/reviews/INTEGRATION-7.md` is the receipt-owner's item, not this one.

`Lib.lean` imports the new module (440 → 442 imports, together with finding 2's module);
`Lib/AxiomAudit.lean` gains the section header `Lib.GroupTheory.FreeGroup.Invariant` with a
`#check` / `#print axioms` pair.

### 2. `r8-dfiles-b` finding 1 — `fibre_constant_of_ker_le` had no named twin  — **closed**

Re-added in the new module `Lib/Algebra/Group/Ker.lean` (none of the three existing
`Lib/Algebra/Group/` files is about kernels; the new file carries a module docstring and a
`## Main results` bullet):

```
MonoidHom.apply_eq_apply_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hker : f.ker ≤ g.ker) (a b : A) (hab : f a = f b) :
    g a = g b
```

This is the deleted statement (`git show 4e15a034:Lib/Algebra/Group/SurjectiveDescent.lean`,
l.35), not a weakening: the deleted theorem's conclusion was `∀ a b, f a = f b → g a = g b`,
so moving those two variables and the implication in front of the colon yields literally the
same Pi type.  The proof is the deleted one, via `MonoidHom.mem_ker` and
`eq_of_mul_inv_eq_one` (again `_root_.map_mul` / `_root_.map_inv`, shadowed inside
`namespace MonoidHom`).

The other two declarations of the deleted file keep their round-8 twins
(`MonoidHom.liftOfSurjective`, `MonoidHom.liftOfRightInverse_comp`); the module docstring
cites their correct Mathlib file `Mathlib/Algebra/Group/Subgroup/Basic.lean`, which is
`r8-dfiles-b` finding 2 — the receipt text itself is the receipt-owner's item.

`Lib.lean` imports the new module; `Lib/AxiomAudit.lean` gains the section header
`Lib.Algebra.Group.Ker` with a `#check` / `#print axioms` pair.

### 3. `r8-dfiles-c` findings 1 and 3 — wrong mechanism and wrong Mathlib paths  — **closed**

`Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` (module docstring; declaration untouched):

* The sentence "Typeclass resolution does not see through `Sheaf.H` to `Ext` in this
  development" and the sentence "Closing the gap is an upstream change to `Sheaf.H`" are gone.
  In their place the docstring states the mechanism the reviewer reproduced (probes under
  `/home/goblin/.claude/jobs/06995e68/tmp/review-pass/r8-dfiles-c/`): `Sheaf.H` is stated for
  the site-level `CategoryTheory.Sheaf J C`, while Mathlib's `TopCat.Sheaf C X` is a
  non-reducible `def` for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`
  (`Mathlib/Topology/Sheaves/Sheaf.lean:108`), so at instance transparency the unifier cannot
  identify the two and `AddCommGroup (Sheaf.H F n) =?= AddCommGroup (Ext _ _ _)` fails for a
  `TopCat.Sheaf`-typed `F`.  The docstring now also records that Mathlib's instance *does*
  fire for a site-typed sheaf and for a locally reducible `TopCat.Sheaf`, i.e. that nothing
  upstream is broken, and that the file stays load-bearing only until `Lib` switches its
  sheaves to the site-level spelling.  The observed failure (`failed to synthesize
  Add (Sheaf.H Q 0)` in `ShortExactDegreeOne.lean` and `FiniteClosedPushforward/Cohomology.lean`)
  and the "must not be deleted" conclusion are kept — they were right.
  This also closes `r7-names` finding 2, which is the same sentence.
* `CategoryTheory.Abelian.Ext.instAddCommGroup` is attributed to
  `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean` (l.239, grepped), not to
  `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean`.  The `Sheaf.H` = `Ext`
  citation `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` was already right and is
  kept, with the addition that `H` is an `abbrev` there.
* The declaration docstring of `CategoryTheory.Sheaf.instAddCommGroupH` said the instance is
  "registered under the `Sheaf.H` head symbol"; it now says it is registered for a sheaf whose
  type is spelled `TopCat.Sheaf`, which is what the declaration's binders say.

`Lib/Topology/Sheaves/SheafificationLocal.lean` (module docstring `## References`):
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` is attributed to
`Mathlib/Topology/Sheaves/Sheafify.lean` (l.137, grepped) instead of `Stalks.lean`; because the
two cited facts are then no longer in one file, `TopCat.Presheaf.germ_eq` gets its own path
`Mathlib/Topology/Sheaves/Stalks.lean` (l.456) in place of "from the same file".

### 4. `r8-dfiles-c` finding 2 — the four `SphereTwo` theorems were probed by nothing  — **closed**

New file `Hopf/Proof/AxiomAudit.lean` (module docstring: axiom probes for declarations that
live under `Hopf/Proof` and are not in the dependency closure of the final theorem), with
`#check` / `#print axioms` for the four theorems of
`Hopf/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean`:

```
TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo
TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo
TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo
```

Each reports exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

On the lakefile: the `Hopf` lean_lib has no `roots`/root module, but `lake build
Hopf.Proof.AxiomAudit` resolves and builds the file directly (3094 jobs, green), so **no**
import had to be added to `Hopf/Proof/Final.lean`.  Like `Lib/AxiomAudit.lean`, the file is
deliberately imported by nothing, and it uses plain `import` (not `module` / `public import`),
as `Lib/AxiomAudit.lean` does.

### 5. `r8-dfiles-c` finding 4 — `w4-w1-solution` reroute  — **noted, no code change**

Branch `w4-w1-solution` still carries `import Lib.Topology.Sheaves.Cohomology.SphereTwo` in
`W4W1/CenterBaseCohomologicalDimension.lean:1` (the two theorems are used at l.43 and l.62),
plus the old module line in its `Lib.lean` (l.416) and the four old probes in its
`Lib/AxiomAudit.lean` (l.7419–7430).  When that branch meets this one, the import must be
rerouted to `Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo` and those four probes dropped
in favour of `Hopf/Proof/AxiomAudit.lean` (finding 4 above).  The note is in the body of
commit `f544da65` and here; nothing on this branch touches `w4-w1-solution`.

## Build lines

All from the worktree root, Lake `v4.33.0`:

```
lake build Lib.GroupTheory.FreeGroup.Invariant         ✔ [755/755]   Built (1.1s)
lake build Lib.Algebra.Group.Ker                       ✔ [626/626]   Built (2.3s)
lake build Lib.Topology.Sheaves.Cohomology.AddCommGroup ✔ [2113/2113] Built (2.6s)
lake build Lib.Topology.Sheaves.SheafificationLocal    ✔ [1810/1810] Built (2.6s)
lake build Hopf.Proof.AxiomAudit                       Build completed successfully (3094 jobs)

lake build Lib                                 ✔ [9145/9146] Built Lib (6.1s); 9146 jobs, exit 0
lake build Solution S6Shortcuts S6 Challenge   Build completed successfully (9198 jobs)
                                               'Mathoverflow1973.mathoverflow_1973' depends on
                                               axioms: [propext, Classical.choice, Quot.sound]
lake build Lib.AxiomAudit                      Build completed successfully (9146 jobs)
                                               3302 axiom reports, axiom set over all of them
                                               = {propext, Classical.choice, Quot.sound}; no sorryAx
lake build Hopf.Proof.AxiomAudit               4 axiom reports, same set, no sorryAx
python3 scripts/lib_stock_census.py --check    ratchet PASS: 123 <= baseline 1648
```

`Lib/AxiomAudit.lean` goes from 3312 to 3314 `#print axioms` lines (the two new pairs);
`Lib.lean` from 440 to 442 imports.

## Environment diff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` before the first edit
(`dump_base.jsonl`, 38254 constants) and after the last (`dump_after.jsonl`, 38256), then
`envdiff.py` (`envdiff.json`, `envdiff.txt`).  No rename map: nothing was renamed on this
branch, and the two names re-introduced from history are absent from the base environment, so
they diff as additions.

```
constants before 38254 after 38256 (keys 38152 38154)
lost 0 added 2 of which source declarations: 0 2 ; names with changed type 0 of which source: 0
  ADDED FreeGroup.forall_apply_eq_self_iff   {'Lib.GroupTheory.FreeGroup.Invariant': 1}
  ADDED MonoidHom.apply_eq_apply_of_ker_le   {'Lib.Algebra.Group.Ker': 1}
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
```

`VERDICT FAIL` is the tool's verdict for "a source key was added"; it is `PASS` only for an
environment-preserving change.  Nothing was lost and no type changed.  Both additions are
intended and are the two findings above:

| added source name | module | why |
| --- | --- | --- |
| `FreeGroup.forall_apply_eq_self_iff` | `Lib.GroupTheory.FreeGroup.Invariant` | r7-names finding 1: restatement of the deleted `LinearRepresentation.freeGroup_invariant_iff`, same type |
| `MonoidHom.apply_eq_apply_of_ker_le` | `Lib.Algebra.Group.Ker` | r8-dfiles-b finding 1: re-add of the deleted `fibre_constant_of_ker_le`, same type |

Neither proof produced an auxiliary constant (auxiliary added = 0).  `Hopf/Proof/AxiomAudit.lean`
adds no constant: it is imported by nothing and contains only `#check` / `#print axioms`.

## Commits

`62d45257..` on `fix/names-dfiles` (this receipt is the last commit):

| sha | subject |
| --- | --- |
| `0ae6c1b1` | `Lib/GroupTheory/FreeGroup/Invariant.lean: restate freeGroup_invariant_iff` |
| `eb83e08e` | `Lib/Algebra/Group/Ker.lean: re-add fibre_constant_of_ker_le` |
| `4b3a3379` | `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean: correct the docstring` |
| `a805f92f` | `Lib/Topology/Sheaves/SheafificationLocal.lean: correct a reference path` |
| `f544da65` | `Hopf/Proof/AxiomAudit.lean: probe the four SphereTwo theorems` |

No `sorry`, `axiom`, `admit`, `maxHeartbeats`, `native_decide`, `unsafe`; no statement weakened,
no hypothesis added, no declaration deleted or renamed; `Lib` imports no `Hopf` module.
