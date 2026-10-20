# Fix receipt — `r8-moved` (branch `fix/moved`, base `62d45257`)

Review fixed: `Lib/reports/review-7-8/r8-moved.md` (review of
`Lib/reports/round-8/moved/RECEIPT.md`, which is **not** edited here).
Fix list: `Lib/reviews/REVIEW-7-8.md` §3, bullet `moved`.

## Findings

### Finding 2 — duplicate `import` lines — **closed**

Commit `9725a329`.  Removed, keeping one copy of each:

| file | import | copies before → after |
| --- | --- | --- |
| `Lib.lean` | `Lib.Geometry.Manifold.Curve.CircleGluing` | 3 → 1 |
| `Lib.lean` | `Lib.Combinatorics.IndexDisorder` | 2 → 1 |
| `Hopf/Recognition.lean` | `Lib.Combinatorics.IndexDisorder` | 2 → 1 |
| `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` | `Lib.Combinatorics.IndexDisorder` | 2 → 1 |

No declaration touched.  `git grep -E 'IndexDisorder|Curve.CircleGluing' Lib.lean` now
gives 2 lines (was 5).

Observed but **not** touched (outside this assignment, introduced by another round-8
branch): `Lib.Algebra.Module.IntegerPresentation` is imported twice in each of
`Hopf/SphereTopology.lean`, `Hopf/Proof/SphereTopology.lean` and
`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`.  A full duplicate-import sweep of the
tree (`for f in $(git ls-files '*.lean'); do grep '^import ' $f | sort | uniq -d; done`)
reports only those three lines now.

### Finding 1 — seven missing docstrings — **closed**

Commit `976ef717`, `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean`.
The review is right that the round-8 receipt's claim ("added on this branch's base") was
false: the file had `grep -c '/--'` = 0 at `4e15a034` and at `39f1d12b`, and 0 at the base
of this branch.  All seven declarations now carry a docstring that lists the hypotheses
first and then states the conclusion:

* `CoverOverlapHomology.homologyEquiv_symm_single`
* `CoverOverlapHomology.homologyEquiv_inclusion`
* `CoverOverlapHomology.componentMap`
* `CoverOverlapHomology.overlapMap`
* `CoverOverlapHomology.overlapMap_component`
* `CoverOverlapHomology.homologyEquiv_map`
* `CoverLocalContributions.componentConnecting_enlarge`

No statement, binder or proof changed; the file now has `grep -c '^/--'` = 7.

### Finding 3 — Mathlib twins and two over-promising names — **closed**

**(a) `LinearEquiv.coordMatrix` — documented twin, not deleted.**  Commit `687ea169`,
`Lib/LinearAlgebra/Matrix/TransvectionReduction.lean`.  Added

```
LinearEquiv.coordMatrix_eq_toMatrix (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) :
    coordMatrix B v = (Module.Basis.ofEquivFun B.symm).toMatrix v
```

proved by the reviewer's script `ext i j; simp [coordMatrix, Module.Basis.toMatrix,
Module.Basis.ofEquivFun_repr_apply]`, and named the twin `Module.Basis.toMatrix` in the
docstring of `coordMatrix` and in the module docstring.

The assignment's preferred route (delete `coordMatrix`, restate `coordMatrix_mulVec` and
`surjective_coordMatrix_mulVec` on `Module.Basis.toMatrix`) was **not** taken, because the
reroute is far past the ~10-site threshold: `coordMatrix` occurs on 27 lines and appears in
the statements of six `Lib` declarations (`coordMatrix`, `coordMatrix_mulVec`,
`surjective_coordMatrix_mulVec`, `surjective_functional_row_mulVec`,
`symm_apply_eq_sum_of_coordMatrix_eq_mul`, `functional_row_eq_mul_of_coordMatrix_eq_mul`)
and of four `Hopf` declarations (`Hopf/Recognition.lean` ×5 lines,
`Hopf/Proof/Recognition.lean` ×1, `Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean`
×3), three of which unfold it with `simp only [LinearEquiv.coordMatrix]`.  This is the
fallback the assignment prescribes for that case.

**(b) `Fin.tailHeadAddEquiv` — deleted for its Mathlib twin.**  Commit `d160c940`.  The
surviving twin is

```
(Fin.consLinearEquiv ℤ fun _ : Fin (n + 1) => ℤ).symm.trans (LinearEquiv.prodComm ℤ ℤ (Fin n → ℤ))
```

which is `rfl`-equal to the deleted definition and strictly stronger (a `≃ₗ[ℤ]`, generic in
the module, where the deleted one was a `ℤ`-only `≃+` in the `Fin` namespace).  Its single
consumer, `ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension` in
`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean:5204`, now builds `G` from that composite
(`.toAddEquiv`); the two proof obligations after it are unchanged and close by definitional
equality.  Reroute cost: 1 consumer line + 1 module-docstring sentence, so the deletion
route applied here.

**(c) two renames.**  Commit `5d3d5d62`, `Lib/Algebra/Module/IntegerPresentation.lean`.
Statements, binders and proofs unchanged:

| new | old | why |
| --- | --- | --- |
| `LinearMap.exists_prodEquiv_of_functional_ker_eq_range` | `LinearMap.exists_split_of_ker_eq_range` | not a general splitting lemma: the surjection is a functional `p : B →ₗ[R] R` onto the ring itself and the conclusion is `(A × R) ≃ₗ[R] B` |
| `LinearMap.exists_prodAddEquiv_of_functional_ker_eq_range` | `LinearMap.exists_addEquiv_split_of_ker_eq_range` | its additive form, renamed with it so the pair stays consistent (the review's objection applies verbatim to it) |
| `Int.natAbs_linearEquiv_apply_one` | `LinearEquiv.natAbs_apply_one` | about `ℤ ≃ₗ[ℤ] ℤ` only; had no `Int` in the name |

Consumers updated: `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean:5183`,
`Hopf/Recognition.lean:3025`, the module docstring.  `git grep` for the three old names
over the tree (excluding `Lib/reports`, `Lib/reviews`) returns nothing.

Rename map (`<new> <old>`), used for the after-dump:

```
LinearMap.exists_prodEquiv_of_functional_ker_eq_range LinearMap.exists_split_of_ker_eq_range
LinearMap.exists_prodAddEquiv_of_functional_ker_eq_range LinearMap.exists_addEquiv_split_of_ker_eq_range
Int.natAbs_linearEquiv_apply_one LinearEquiv.natAbs_apply_one
```

### Findings 4 and 5 — not this agent's

Both are corrections to the round-8 receipt's prose (the envdiff paragraph and the two
counts).  `Lib/reports/round-8/moved/RECEIPT.md` is explicitly out of scope here; the
receipt-correction agent owns them.

## Builds

```
lake build Lib.LinearAlgebra.Matrix.TransvectionReduction \
  Lib.Algebra.Module.IntegerPresentation \
  Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality
  → Build completed successfully (8723 jobs).
lake build Lib.Geometry.Manifold.Morse.SurgeryCollapse Hopf.Recognition
  → Build completed successfully (8858 jobs).
lake build Lib                            → Build completed successfully (9144 jobs).
lake build Solution S6Shortcuts S6 Challenge → Build completed successfully (9196 jobs).
lake build Lib.AxiomAudit                 → Build completed successfully (9144 jobs);
    union of all reported axioms = {propext, Classical.choice, Quot.sound}; 0 occurrences
    of sorryAx.
python3 scripts/lib_stock_census.py --check → ratchet PASS: 123 <= baseline 1648
```

No new warning is reported for any file edited here.

## Environment diff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` before the first edit and
after the last (with `--rename`), then `envdiff.py`:

```
constants before 38254 after 38250 (keys 38152 38148 )
lost 5 added 1 of which source declarations: 1 1 ; names with changed type 0 of which source: 0
  LOST Fin.tailHeadAddEquiv {'Lib.Algebra.Module.IntegerPresentation': 1}
  ADDED LinearEquiv.coordMatrix_eq_toMatrix {'Lib.LinearAlgebra.Matrix.TransvectionReduction': 1}
auxiliary lost/added/changed (not judged): 4 0 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT FAIL
```

Every entry accounted for:

* `Fin.tailHeadAddEquiv` (and its four auxiliaries `._proof_1` … `._proof_4`) — the
  deletion of finding 3(b); twin
  `(Fin.consLinearEquiv ℤ _).symm.trans (LinearEquiv.prodComm ℤ ℤ _)` in Mathlib, `rfl`-equal
  and stronger.  This single lost source name is the whole reason for `VERDICT FAIL`; the
  tool fails on any lost source declaration and cannot see a Mathlib twin.
* `LinearEquiv.coordMatrix_eq_toMatrix` — the new equation lemma of finding 3(a).
* 0 changed types, 0 module moves, 0 ambiguous.  The three renames do not appear on either
  side: the rename map matched them and their types are unchanged, which is the mechanical
  check that they are pure renames.

## Commits

`62d45257..` (branch `fix/moved`), oldest first:

| commit | fix item |
| --- | --- |
| `9725a329` | finding 2 — duplicate imports in `Lib.lean`, `Hopf/Recognition.lean`, `SurgeryCollapse.lean` |
| `976ef717` | finding 1 — seven docstrings in `LocalContributionsNaturality.lean` |
| `687ea169` | finding 3(a) — `coordMatrix_eq_toMatrix` and the twin named in the docstrings |
| `d160c940` | finding 3(b) — `Fin.tailHeadAddEquiv` deleted for the Mathlib composite |
| `5d3d5d62` | finding 3(c) — the two (three) renames |

plus this receipt.
