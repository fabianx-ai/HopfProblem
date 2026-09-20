# Round 8 — seat `moved` (packet `round-7/judgement/moved-verbatim.md`)

Worktree `/home/goblin/hopf-r8-moved`, branch `r8/moved`, base `4e15a034`.
Seven files whose docstrings said "moved verbatim" from `Hopf/`, graded C (not D).

## Per item

### 1. `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` — done (commit `93781a7c`)

Ten general integer-matrix / coordinate-matrix statements carried the project namespace
`MorseCancellation` and, in four names, the project word "class" (homology class).
All ten renamed to the namespace of their object (`Matrix`, `LinearEquiv`); statements
unchanged. The round-7 items the auditors list (`{A : Type}` → `Type*`, docstrings,
the provenance paragraph) were already done on this branch's base.

Consumers updated: `Lib/Geometry/Manifold/Morse/CutTransport.lean`, `Hopf/Recognition.lean`,
`Hopf/Proof/Recognition.lean`.

Not done: re-deriving the row reduction from Mathlib's `Matrix.Pivot` / Smith-form API.
That is a reproof, not a rename or a move.

### 2. `Lib/Algebra/Module/IntegerPresentation.lean` — done (commit `f2439031`)

The six declarations the auditors call "unrelated split-extension/rank lemmas under a project
namespace" are general `R`-module, `Matrix` and `Fin` statements; they were under
`HomologyTransport`. All six renamed to the namespace of their object. Statements unchanged;
the module docstring now names them, so the file no longer hides a second topic.

They were *not* moved to `Hopf/Proof`: they carry no project hypothesis (they are stated for a
general commutative ring and general modules), so rule (1) of the packet applies, not rule (2).

Consumers updated: `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`, `Hopf/Recognition.lean`,
`Hopf/Proof/Recognition.lean`.

Not done: rebuilding the `IntegerPresentation` API on Mathlib's `Module.Presentation` over a
general ring. That is a rewrite of the file's main construction.

### 3. `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean` — done (commit `6efb0582`)

Verdict B, "docs only". No declaration name in the file is project vocabulary
(`CoverOverlapHomology`, `CoverLocalContributions` are descriptive).  **(corrected)** this item
originally also claimed that "the docstrings the auditors ask for were added on this branch's base".
That is **false**: at base `4e15a034` the file has 7 declarations and **0** `/--` docstrings
(`git show 4e15a034:… | grep -c '/--'` → 0; the lines preceding each `theorem`/`def` are blank,
`noncomputable section`, or proof lines), and at head `39f1d12b` it is still 0 — the only later
touch, `a3c8ce9c` on `r8/dup-hom`, retargets four qualifiers.  The packet's finding "7 of 7
declarations lack docstrings" was therefore **still open** when this receipt recorded it as closed,
and verdict B was not actually executed.  **The seven docstrings are being added now**
(`Lib/reviews/REVIEW-7-8.md` §3, moved).  What this item did do is right: the remaining "moved
verbatim" paragraph (a qualifier-retarget receipt) is deleted and replaced by the reference for the
result (Hatcher §2.2, naturality of Mayer-Vietoris for maps of covers).  No declaration changed.
A sentence of the form "X was already done on the base" must carry the command that shows it.

Not done: merging the file into `LocalContributions.lean`. The packet restricts file surgery
to *splits* the entry asks for; this is a merge.

### 4. `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean` — done (commit `527575bf`)

The entry's one rename: the file's only statement that is not about a surgery-window system
`S : AdaptedWindows E f` is the realization of a compactly supported relative isotopy of a
regular level by the flow of a modified gradient-like field, and it sat in `FlowSuspension`,
the namespace of the construction its *proof* uses. Renamed to the namespace of its subject.
Statement unchanged. Two references inside its own proof had been resolving through the old
namespace and are now written out (`FlowSuspension.exists_native_whole_level_holonomy`,
`FlowSuspension.native_whole_level_exterior_tails`, both from `Morse/Connection.lean`).

Consumer updated: `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean`.

`nativeMorseIndex` is used here but defined outside the packet
(`MorseCancellation.nativeMorseIndex`, **226 matching lines at head (corrected; the receipt said ~100 uses)** across `Morse/*`); renaming it is another
seat's file, so it is untouched.

**`AdaptedWindows.exists_ordered_index_cut` left in place — reason.** The auditors ask for it
"stated for `IsMorse` + `Finite criticalPoints` without `S : AdaptedWindows`". It is not a local
change and, as stated, not a true generalisation: the last conjunct
(`∀ z, f z ≤ a → index z ≤ k`) needs that no *other* critical point shares the value `f r`,
which `S` supplies (`S.distinct`, `S.toSurgeryWindows.isolated`). `IsMorse` + `Finite` does not
give it; supplying it would be adding a hypothesis, which the rules forbid. Moving it to
`Hopf/Proof/` instead is impossible: its only consumer is `Hopf/SphereTopology.lean:899` **(corrected; the receipt said l.898)**, and
`Hopf/Proof/SphereTopology.lean` *imports* `Hopf/SphereTopology.lean`, so `Hopf/Proof` is
downstream of the consumer.

Not done: the import list (49 Lib files for a 622-line file), `set_option maxSynthPendingDepth`,
the kitchen-sink `open scoped`, the unused `universe u v`. Round-7 checklist items, not renames.

### 5. `Lib/Geometry/Manifold/Morse/CircleGluing.lean` — done (commit `ade17473`)

Split, as the entry asks: the self-contained gluing construction
(`periodicExtension`, `joinedArc`, `joinedLoop`, `circleExp_localDiffeomorph`, `periodicCircle`
and their lemmas — 36 declarations) is now the documented module
`Lib/Geometry/Manifold/Curve/CircleGluing.lean`, listed in `Lib.lean` and imported by the file
it left. It needed one lemma from earlier in the old file
(`MorseCancellation.injective_mfderiv_curve_translate`, a general statement about translating
the parameter of a curve); that moved with it and lost the project namespace.

Renamed in place, the two general lemmas the entry flags plus the two `native` names:
`MorseCancellation.exists_native_open_curve_with_germ`,
`MorseCancellation.exists_embedded_native_open_arc_with_local_germs`,
`NativeOpenSubmanifold.injective_mfderiv_subtype_val` (all three are statements about an
open subset `S : TopologicalSpace.Opens N`, now in that namespace) and
`MorseCancellation.unitSphere_eq_two_points_of_finrank_one` (a fact about
`Metric.sphere (0 : V) 1`, now in `Metric`).

Consumers updated: `Lib/Geometry/Manifold/Whitney/EmbeddedArcs.lean`,
`Lib/Geometry/Manifold/Morse/BeltCancellation.lean`,
`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`.

Not done: merging the remaining surgery rows (`MorseCancellation.exists_*_return_arc*`,
`ManifoldImmersion.exists_relative_embedded_avoidance_*`, `AdaptedWindows.*`,
`FlowSuspension.*`, `ManifoldMorse.MorseSurgeryData.*`) into their subject files. That is a
set of merges across four other files, not a split of this one.

### 6. `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean` — done (commit `7236c088`)

Split, as the entry asks: the twelve declarations of the inversion count (Milnor Thm 4.8) are
pure finite combinatorics, used nowhere else in the file, and are now
`Lib/Combinatorics/IndexDisorder.lean` (listed in `Lib.lean`), out of the project namespace
`MorseRearrangement` and under `IndexDisorder`. The two module docstrings were rewritten so
each names one subject and cites its reference (Hirsch Ch. 3 / Milnor §4).

Consumers updated and given the new import: `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean`,
`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`, `Hopf/Recognition.lean`.

Not done: replacing `sheetSum X n` by `Fin n × X` and dropping its six hand-rolled instances,
and splitting `exists_*_ambient_*` into `Transversality/AmbientIsotopy.lean`. The first is a
redefinition (the six instances would have to be re-derived, and every use of `sheetSumMap`
reproved); the second would leave `RearrangementAmbient.lean` empty of its own subject and was
not needed to remove project vocabulary.

### 7. `Lib/Geometry/Manifold/Whitney/AnnularExtension.lean` — done (commit `6b1c40f1`)

The entry's project residue that is a fixed index: `structure TubularBigon` declared its
normal-fibre dimension `(n : ℕ := 4)`, the project's 6-manifold Whitney disc (2 + 4 = 6). The
default is removed, so the codimension is an explicit parameter. Two declarations relied on it
(`TubularBigon.TangentAdaptedChart`, `TubularBigon.SheetParametrizedChart` in
`Whitney/RankThreeModel.lean`) and now pass `4`; every other use already passed `n` or `3`. No
statement changes (see the envdiff note below).

Not done, with reasons:

* `*_of_circle_nullhomotopies` → `[SimplyConnectedSpace M]`: `SimplyConnectedSpace` is strictly
  stronger than "every map `S¹ → M` is nullhomotopic" as the hypothesis is used here
  (it also asks for path-connectedness), so the swap would weaken the three theorems. Forbidden.
* moving `SphereCone.*` and `AnnularExtension.*` to `Topology/`, and
  `sphereMap_nullhomotopic_of_omitted_point`, `sphereMap_nullhomotopic_of_dim_lt`,
  `sphere_sphere_nullhomotopic` to `AlgebraicTopology/`: two further file splits the packet did
  not ask this seat for (the entry asks for the split, the packet's rule (3) admits a split
  only when the pieces are clean — these three theorems are stated through the file's own
  root-namespace `Sphere n` abbreviation, which would have to be replaced first).
* the root-namespace `UnitSphere` / `Sphere` abbreviations: generic, but not project
  vocabulary; renaming them touches `Morse/SurgeryWindows.lean`'s `Hemisphere.Sphere` and every
  sphere-map statement in `Whitney/`, outside this packet.

## Rename map

The map used for the envdiff is `rename-new-to-old.txt` in this directory (new → old, the
direction `dump --rename` wants). Read as old → new:

| old | new |
| --- | --- |
| `MorseCancellation.classCoordinateMatrix` | `LinearEquiv.coordMatrix` |
| `MorseCancellation.classCoordinateMatrix_mulVec` | `LinearEquiv.coordMatrix_mulVec` |
| `MorseCancellation.classCoordinateMatrix_surjective` | `LinearEquiv.surjective_coordMatrix_mulVec` |
| `MorseCancellation.functional_class_row_surjective` | `LinearEquiv.surjective_functional_row_mulVec` |
| `MorseCancellation.transported_classes_of_matrix_product` | `LinearEquiv.symm_apply_eq_sum_of_coordMatrix_eq_mul` |
| `MorseCancellation.functional_rows_of_matrix_product` | `LinearEquiv.functional_row_eq_mul_of_coordMatrix_eq_mul` |
| `MorseCancellation.mul_transvection_surjective` | `Matrix.surjective_mulVec_mul_transvection` |
| `MorseCancellation.mul_transvection_list_surjective` | `Matrix.surjective_mulVec_mul_transvection_list` |
| `MorseCancellation.eq_mul_transvection_of_columns` | `Matrix.eq_mul_transvection_of_columns` |
| `MorseCancellation.primitive_row_has_unit_after_column_additions` | `Matrix.primitive_row_has_unit_after_column_additions` |
| `HomologyTransport.ker_comp_span_singleton` | `LinearMap.ker_comp_eq_ker_sup_span_singleton` |
| `HomologyTransport.exists_split_rank_one_extension` | `LinearMap.exists_split_of_ker_eq_range` |
| `HomologyTransport.exists_add_split_rank_one_extension` | `LinearMap.exists_addEquiv_split_of_ker_eq_range` |
| `HomologyTransport.integerCoordinateSplit` | `Fin.tailHeadAddEquiv` |
| `HomologyTransport.integerEquiv_one_natAbs` | `LinearEquiv.natAbs_apply_one` |
| `HomologyTransport.matrix_sizes_eq_of_bijective` | `Matrix.cols_eq_rows_of_bijective_mulVec` |
| `FlowSuspension.exists_relative_regular_level_isotopy_realization` | `RegularLevel.exists_flow_realization_of_relative_isotopy` |
| `MorseCancellation.exists_native_open_curve_with_germ` | `TopologicalSpace.Opens.exists_contMDiff_curve_with_germ` |
| `MorseCancellation.exists_embedded_native_open_arc_with_local_germs` | `TopologicalSpace.Opens.exists_embedded_arc_with_local_germs` |
| `NativeOpenSubmanifold.injective_mfderiv_subtype_val` | `TopologicalSpace.Opens.injective_mfderiv_subtype_val` |
| `MorseCancellation.unitSphere_eq_two_points_of_finrank_one` | `Metric.unitSphere_eq_two_points_of_finrank_eq_one` |
| `MorseCancellation.injective_mfderiv_curve_translate` | `CircleGluing.injective_mfderiv_curve_translate` |
| `MorseRearrangement.upperValueRank` | `IndexDisorder.upperValueRank` |
| `MorseRearrangement.finiteIndexDisorder` | `IndexDisorder.finiteIndexDisorder` |
| `MorseRearrangement.upperValueRank_comp_equiv` | `IndexDisorder.upperValueRank_comp_equiv` |
| `MorseRearrangement.finiteIndexDisorder_comp_equiv` | `IndexDisorder.finiteIndexDisorder_comp_equiv` |
| `MorseRearrangement.upperValueRank_consecutive` | `IndexDisorder.upperValueRank_consecutive` |
| `MorseRearrangement.sum_erase_two_nat` | `IndexDisorder.sum_erase_two_nat` |
| `MorseRearrangement.weighted_sum_swap_identity` | `IndexDisorder.weighted_sum_swap_identity` |
| `MorseRearrangement.finiteIndexDisorder_swap_lt` | `IndexDisorder.finiteIndexDisorder_swap_lt` |
| `MorseRearrangement.exists_adjacent_index_inversion` | `IndexDisorder.exists_adjacent_index_inversion` |
| `MorseRearrangement.exists_consecutive_below_of_intermediate` | `IndexDisorder.exists_consecutive_below_of_intermediate` |
| `MorseRearrangement.beforeValueRank` | `IndexDisorder.beforeValueRank` |
| `MorseRearrangement.beforeValueRank_exchange_lt` | `IndexDisorder.beforeValueRank_exchange_lt` |

## Lost names

None. Under the rename map the envdiff reports **0 lost source declarations and 0 added**, so
there is no lost-name table and no surviving-twin argument to make: nothing was deleted in this
packet.

## Envdiff

`envdiff.json` in this directory; `dump_base.jsonl` from base `4e15a034` before any edit,
`dump_after.jsonl` from the final tree with `--rename rename-new-to-old.txt`.

```
constants before 38593 after 38593 (keys 38491 38491 )
lost 39 added 39 of which source declarations: 0 0 ; names with changed type 22 of which source: 17
  PROOF-NAMING TubularBigon, TubularBigon.mk, and its 15 projections
auxiliary lost/added/changed (not judged): 39 39 5
module moves (source declarations, 1-to-1):
      36  Lib.Geometry.Manifold.Morse.CircleGluing -> Lib.Geometry.Manifold.Curve.CircleGluing
      12  Lib.Geometry.Manifold.Morse.RearrangementAmbient -> Lib.Combinatorics.IndexDisorder
ambiguous module changes: 0
auxiliary constants that changed module: 12
VERDICT PASS
```

* **lost/added 0 source, 39 auxiliary**: **(corrected)** this explanation — "equation lemmas and
  `_proof_n` abstractions realized in a different module after the two file splits" — does not fit
  the data.  In `envdiff.json`, **22 of the 39 on each side are the `TubularBigon` family**
  (`TubularBigon`, `.mk`, 15 projections, `_sizeOf_inst`, `ctorIdx`, `mk._flat_ctor`,
  `mk.noConfusion`, `mk.sizeOf_spec`): the same names with new hashes, listed again under
  `changed_type_all` (22) / `changed_type_proof_naming` (17).  Of the remaining 17, **8 come from the
  rename commits** (`Fin.tailHeadAddEquiv._proof_3/_4` have different hashes from
  `integerCoordinateSplit._proof_3/_4`; `LinearEquiv.coordMatrix.eq_1`; the `_simp_1_n` of the
  transvection lemmas) and **9 from the `IndexDisorder` split**; **nothing from the `CircleGluing`
  split appears in lost/added at all** (its 12 auxiliaries are `auxiliary_moved`).  The conclusion —
  0 source declarations lost, and all 17 source type changes are `TubularBigon`'s
  `optParam ℕ 4 → ℕ` — is right; only the sentence explaining the 39 was not.
* **17 changed types, all `TubularBigon`**: the only type change in the packet, and it is the
  binder change of item 7 — the parameter `n` of the structure went from `optParam ℕ 4` to a
  plain `ℕ` binder, which changes the recorded type of `TubularBigon`, of `TubularBigon.mk` and
  of each of its 15 projections. `envdiff` classes them PROOF-NAMING (the `uses` sets are
  identical), and every consumer passes the same `n` it passed before, so no statement moved.
* **module moves**: exactly the two splits, 36 + 12 declarations, 1-to-1, no ambiguity.

## Builds

```
lake build Lib.LinearAlgebra.Matrix.TransvectionReduction Lib.Algebra.Module.IntegerPresentation \
           Lib.Combinatorics.IndexDisorder \
           Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality \
           Lib.Geometry.Manifold.Curve.CircleGluing
  -> Build completed successfully (8741 jobs).

lake build Lib
  -> Build completed successfully (9152 jobs).

lake build Solution S6Shortcuts S6 Challenge
  -> Build completed successfully (9191 jobs).
  -> 'Mathoverflow1973.mathoverflow_1973' depends on axioms:
       [propext, Classical.choice, Quot.sound]

lake build Lib.AxiomAudit
  -> Build completed successfully (9152 jobs);
     the only axioms over all probes are propext, Classical.choice, Quot.sound.

python3 scripts/lib_stock_census.py --check
  -> ratchet PASS: 123 <= baseline 1648
```

## Commits

`93781a7c..6b1c40f1` on `r8/moved` (plus this receipt), one per packet file:

| commit | file |
| --- | --- |
| `93781a7c` | `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` |
| `f2439031` | `Lib/Algebra/Module/IntegerPresentation.lean` |
| `6efb0582` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean` |
| `527575bf` | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean` |
| `ade17473` | `Lib/Geometry/Manifold/Morse/CircleGluing.lean` (+ new `Lib/Geometry/Manifold/Curve/CircleGluing.lean`) |
| `7236c088` | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean` (+ new `Lib/Combinatorics/IndexDisorder.lean`) |
| `6b1c40f1` | `Lib/Geometry/Manifold/Whitney/AnnularExtension.lean` |

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r8-moved.md` (ACCEPT WITH FINDINGS; all 34 renames and
both splits are exact — statements byte-identical up to the name, old names absent, new names
present exactly once, and the split files partition the source declarations — and both "not done"
reasons hold up, including the `SimplyConnectedSpace` refusal, where the swap really would add
path-connectedness as a hypothesis).  These corrections are to this receipt's text only; no Lean
file was changed by them.

1. **Item 3's docstring claim is false (finding 1)**, corrected in item 3.
   `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean` has **0** declaration
   docstrings at base `4e15a034` and **0** at head `39f1d12b`, for 7 declarations; the packet's
   finding was recorded as closed while it was still open.  The seven docstrings are being added by
   a fix agent (`Lib/reviews/REVIEW-7-8.md` §3, moved).

2. **The branch left duplicate `import` lines, and one commit touches files its message does not name
   (finding 2), recorded here.**  Each of `ade17473`, `7236c088` and `6b1c40f1` re-adds an import
   that is already present.  At the branch tip and still at head `39f1d12b`: `Lib.lean` imports
   `Lib.Geometry.Manifold.Curve.CircleGluing` **three** times and `Lib.Combinatorics.IndexDisorder`
   twice; `Hopf/Recognition.lean` and `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` each import
   `Lib.Combinatorics.IndexDisorder` twice.  The commit that adds the second and third copies is
   `6b1c40f1`, "AnnularExtension: make the Whitney bigon codimension explicit" — none of the three
   files it touches has anything to do with the bigon, so both this receipt's "one commit per packet
   file" and that commit message are inaccurate for it.  Lean accepts duplicate imports, so nothing
   breaks; removing the five lines is on the fix list.  Commits that touch `Lib.lean` or consumer
   imports must say so in the message.

3. **Two new names duplicate Mathlib declarations and the receipt does not say so (finding 3).**  All
   29 distinct new short names were checked against Mathlib: **zero collisions** (good), but two have
   twins.  `LinearEquiv.coordMatrix B v = (Module.Basis.ofEquivFun B.symm).toMatrix v` (closes by
   `ext i j; simp [LinearEquiv.coordMatrix, Module.Basis.toMatrix,
   Module.Basis.ofEquivFun_repr_apply]`), so `coordMatrix_mulVec` /
   `surjective_coordMatrix_mulVec` are restatements of `Basis.toMatrix` lemmas; and
   `Fin.tailHeadAddEquiv n v = LinearEquiv.prodComm ℤ ℤ _ ((Fin.consLinearEquiv ℤ _).symm v)` holds
   by `rfl`, while the new name sits in `Fin` but is ℤ-specific with no type argument where
   Mathlib's is generic.  The packet had already flagged the first
   ("`LinearMap.toMatrix`-style coordinate matrix under a nonstandard name"), so the rename gave it a
   Mathlib-shaped name without pointing at the Mathlib twin.  Two further names over-promise:
   `LinearMap.exists_split_of_ker_eq_range` reads as a general splitting lemma but is only for
   `p : B →ₗ[R] R` (the old name said `rank_one_extension`), and `LinearEquiv.natAbs_apply_one` is
   about `ℤ ≃ₗ[ℤ] ℤ` only, with no `Int` in the name.  Replacing the two by their Mathlib twins, or
   documenting the twins, and renaming the two over-promising ones are on the
   `Lib/reviews/REVIEW-7-8.md` §3 list.  The other names were judged reasonable.

4. **The envdiff paragraph is corrected in place (finding 4)**: 22 of the 39 lost/added on each side
   are the `TubularBigon` family reappearing with new hashes, 8 come from the rename commits and 9
   from the `IndexDisorder` split, and nothing from the `CircleGluing` split is in lost/added.  The
   conclusion was right; the explanation was not.  (The tool invites the mistake: names that are both
   lost/added by a hash change *and* changed-type should be printed in one bucket.)

5. **Two small figures (finding 5), corrected in place.**  `nativeMorseIndex` has **226** matching
   lines at head, not "~100 uses"; the consumer of `exists_ordered_index_cut` is
   `Hopf/SphereTopology.lean:**899**`, not 898.
