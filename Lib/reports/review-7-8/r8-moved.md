# Review of Lib/reports/round-8/moved/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — all 34 renames and both splits are exact (statements
byte-identical up to the name, old names absent, new names present once, split files partition
the source declarations), the two "not done" reasons hold up, but the receipt makes one false
claim (item 3's docstrings), the branch leaves duplicated `import` lines in three files with a
commit that misdescribes what it touches, and two new names shadow Mathlib twins the receipt
does not mention.

## Findings

1. **[wrong receipt]** Item 3 (`LocalContributionsNaturality.lean`, commit `6efb0582`) says
   "the docstrings the auditors ask for were added on this branch's base". False. At base
   `4e15a034` the file has 7 declarations and 0 `/--` docstrings
   (`git show 4e15a034:Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean | grep -c '/--'` → 0;
   the lines preceding each `theorem`/`def` are blank, `noncomputable section`, or proof lines).
   At head `39f1d12b` it is still 0 (the only later touch, `a3c8ce9c` on `r8/dup-hom`, retargets
   four qualifiers). The packet's finding "7 of 7 declarations lack docstrings" is therefore
   still open and the receipt records it as closed. Either add the seven docstrings or correct
   the receipt; the packet verdict B ("docs only") was not actually executed.

2. **[nit] Duplicate `import` lines introduced by the branch, still at head, and a commit that
   touches files its message does not name.** Each of `ade17473`, `7236c088`, `6b1c40f1` re-adds
   imports already present. Branch tip `9ffac3fc^2`: `Lib.lean` imports
   `Lib.Geometry.Manifold.Curve.CircleGluing` three times and `Lib.Combinatorics.IndexDisorder`
   twice; `Hopf/Recognition.lean` and `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` each
   import `Lib.Combinatorics.IndexDisorder` twice. All still present at `39f1d12b`
   (`git show 39f1d12b:Lib.lean | grep -E 'IndexDisorder|Curve.CircleGluing'` → 5 lines).
   Commit `6b1c40f1` ("AnnularExtension: make the Whitney bigon codimension explicit") is the one
   that adds the second/third copies to `Lib.lean`, `Hopf/Recognition.lean` and
   `SurgeryCollapse.lean` — none of which has anything to do with the bigon — so the receipt's
   "one per packet file" and the commit message are both inaccurate for that commit. Lean
   accepts duplicate imports, so nothing breaks; it is residue that the next seat will have to
   clean.

3. **[nit] Two new names duplicate Mathlib declarations; the receipt does not say so.** Checked
   all 29 distinct new short names against Mathlib (zero collisions), then the twins:
   * `LinearEquiv.coordMatrix B v = (Module.Basis.ofEquivFun B.symm).toMatrix v` — closes by
     `ext i j; simp [LinearEquiv.coordMatrix, Module.Basis.toMatrix, Module.Basis.ofEquivFun_repr_apply]`
     (scratch elaborated, `r8-moved/Scratch.lean`). The packet already flagged this
     ("`LinearMap.toMatrix`-style coordinate matrix under a nonstandard name"); the rename gives it
     a Mathlib-shaped name without pointing at `Module.Basis.toMatrix`, and
     `coordMatrix_mulVec`/`surjective_coordMatrix_mulVec` are then restatements of
     `Basis.toMatrix` lemmas (`Basis.sum_toMatrix_smul_self`, `Basis.toMatrix_mulVec`-shaped).
   * `Fin.tailHeadAddEquiv n v = LinearEquiv.prodComm ℤ ℤ _ ((Fin.consLinearEquiv ℤ _).symm v)`
     holds by `rfl` (same scratch). The new name sits in `Fin` but is `ℤ`-specific with no type
     argument; Mathlib's is generic. A rename map entry pointing at the Mathlib twin, or a
     docstring line "this is `Fin.consLinearEquiv` specialised to `ℤ`", would have been honest.
   * Naming quality: `LinearMap.exists_split_of_ker_eq_range` reads as a general splitting lemma
     but is only for `p : B →ₗ[R] R` (extension by the ring itself; the old name said
     `rank_one_extension`), and `LinearEquiv.natAbs_apply_one` is about `ℤ ≃ₗ[ℤ] ℤ` only, with no
     `Int` in the name. Neither collides with anything; both over-promise.
   The other names are reasonable: `Matrix.eq_mul_transvection_of_columns`,
   `Matrix.surjective_mulVec_mul_transvection(_list)`, `Matrix.cols_eq_rows_of_bijective_mulVec`,
   `TopologicalSpace.Opens.*` (first explicit argument is the `Opens`, so dot-notation works),
   `Metric.unitSphere_eq_two_points_of_finrank_eq_one`, `IndexDisorder.*`, `CircleGluing.*`.

4. **[nit] Envdiff paragraph is loose.** The receipt explains the 39 lost / 39 added as
   "equation lemmas and `_proof_n` abstractions realized in a different module after the two file
   splits". In `envdiff.json`, 22 of the 39 on each side are the `TubularBigon` family
   (`TubularBigon`, `.mk`, 15 projections, `_sizeOf_inst`, `ctorIdx`, `mk._flat_ctor`,
   `mk.noConfusion`, `mk.sizeOf_spec`) — same names, new hashes, listed again under
   `changed_type_all` (22) / `changed_type_proof_naming` (17); of the remaining 17, 8 come from
   the rename commits (`Fin.tailHeadAddEquiv._proof_3/_4` have different hashes from
   `integerCoordinateSplit._proof_3/_4`; `LinearEquiv.coordMatrix.eq_1`; the `_simp_1_n` of the
   transvection lemmas) and 9 from the `IndexDisorder` split; nothing from the `CircleGluing`
   split is in lost/added (its 12 auxiliaries are `auxiliary_moved`). The conclusion (0 source
   declarations lost, all 17 source type changes are `TubularBigon`'s `optParam ℕ 4 → ℕ`) is
   right; the sentence explaining the 39 is not.

5. **[nit]** "`nativeMorseIndex` … ~100 uses across `Morse/*`": 226 matching lines at head.
   "`Hopf/SphereTopology.lean:898`": line 899 at head. Trivial.

Nothing `[unsound]`: no statement changed, no hypothesis added, no deletion, no `sorry`/`axiom`/
`maxHeartbeats`/`unsafe`/`native_decide`/`@[simp]`/`private` change in the branch diff (the only
`noncomputable section` additions are in the two new files, copied from the sources which already
had one).

## Claims checked

| claim | status | how |
| --- | --- | --- |
| 8 commits, one per packet file plus receipt; commit messages describe the commit | partly | `git log 4e15a034..9ffac3fc^2`: 7 file commits + receipt; `6b1c40f1` also edits `Lib.lean`, `Hopf/Recognition.lean`, `SurgeryCollapse.lean` (duplicate imports) without saying so (finding 2) |
| Trailers present on every commit | verified | `git log --format='%(trailers…)'`: `Co-Authored-By: Claude Opus 5`, `Claude-Session` on all 8 |
| Item 1: ten `MorseCancellation.*` → `Matrix.*`/`LinearEquiv.*`, statements unchanged | verified | `git show 93781a7c`: every hunk is a name substitution; binders, hypotheses, conclusions identical |
| Item 1: `{A : Type}` → `Type*`, docstrings, provenance paragraph already done on base | verified | base file: 6 × `Type*`, 0 × `{A : Type}`, docstrings present as context lines, no "Provenance"/"Moved verbatim" |
| Item 2: six `HomologyTransport.*` renamed, statements unchanged | verified | `git show f2439031`: name substitutions only; module docstring paragraph added |
| Item 2: consumers `SurgeryCollapse`, `Hopf/Recognition`, `Hopf/Proof/Recognition` updated | verified | same diff |
| Item 3: porting paragraph replaced by Hatcher §2.2 reference, no declaration changed | verified | `git show 6efb0582`: 3 lines deleted, 4 added, all in the module docstring |
| Item 3: "docstrings … were added on this branch's base" | **refuted** | 0 docstrings at base and at head (finding 1) |
| Item 4: one rename `FlowSuspension.exists_relative_regular_level_isotopy_realization` → `RegularLevel.exists_flow_realization_of_relative_isotopy`, statement unchanged; two in-proof references written out; `MiddleBlocks` updated | verified | `git show 527575bf` |
| Item 4: `exists_ordered_index_cut` cannot be stated for `IsMorse` + `Finite` without a new hypothesis | verified | head proof (AdaptedWindows.lean:632–) uses `S.distinct` (equal-value case) and `S.toSurgeryWindows.isolated` (above-`r` case) for the last conjunct; with two critical points of index `k`, `k+1` at one value the conjunct `f z ≤ a → index z ≤ k` fails, so the general form is false, not merely unproved |
| Item 4: only consumer `Hopf/SphereTopology.lean`, and `Hopf/Proof/SphereTopology.lean` imports it | verified | `git grep exists_ordered_index_cut 39f1d12b` → `Hopf/SphereTopology.lean:899` only; `Hopf/Proof/SphereTopology.lean:65 import Hopf.SphereTopology` |
| Item 5: split of `Morse/CircleGluing.lean` into `Curve/CircleGluing.lean`, 36 declarations, every source declaration in exactly one result | verified | declaration lists: base 56 = head 20 (Morse) + 36 (Curve), no duplicates, set difference is exactly the five renames; deleted lines of `ade17473` vs the new file differ only in header, `noncomputable section`/`end` and the one rename |
| Item 5: four in-place renames, statements unchanged | verified | `git show ade17473` added lines; statement heads at head read |
| Item 5: consumers `EmbeddedArcs`, `BeltCancellation`, `SurgeryCollapse` updated | verified | same diff |
| Item 6: twelve inversion-count declarations to `Lib/Combinatorics/IndexDisorder.lean`, 1-to-1 | verified | base 35 = head 23 + 12, no duplicates; deleted lines of `7236c088` under `MorseRearrangement.→IndexDisorder.` equal the new file body; consumers `OrderedCancellation`, `SurgeryCollapse`, `Hopf/Recognition` updated |
| Item 7: `TubularBigon` `(n : ℕ := 4)` → `(n : ℕ)`; exactly two uses relied on the default, now pass `4`; every other use passes `n` or `3` | verified | `git grep TubularBigon 4e15a034`: 85 use sites; only `RankThreeModel.lean:890, 2319` lacked the argument (both `structure … Chart` decls); the four multi-line uses (`EmbeddedArcs` 327/3172/3239, `FrameField` 2560) all pass `3`; head has `(n : ℕ)` at AnnularExtension.lean:917 |
| Item 7: no statement changes | verified | `#check @TubularBigon` at head: `… → ℝ → ℕ → Type u_2`; no theorem for general codimension is stated or claimed — the packet's "any `n ≥ 5`" remark is untouched, and the receipt does not claim otherwise |
| Item 7: `SimplyConnectedSpace` is strictly stronger than the `hnull` hypothesis (adds path-connectedness) | verified | the three theorems (AnnularExtension.lean:697, 831, 881) assume only `[TopologicalSpace M]` (+ manifold structure for the third), no connectedness; `hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (const c)`; Mathlib `SimplyConnected.lean:73` gives `instance : PathConnectedSpace X`, confirmed by `inferInstance` in the scratch. A discrete two-point space satisfies `hnull` and is not simply connected, so the swap adds a hypothesis |
| Rename map: 34 entries, direction new→old, every new name defined exactly once at head, every old name absent | verified | loop over `rename-new-to-old.txt`: 34 × (0 hits for old in `*.lean`, 1 defining hit for new) |
| New names collide with Mathlib | refuted (good) | grep of all 29 distinct short names over `.lake/packages/mathlib/Mathlib`: 0 hits; twins exist for two of them (finding 3) |
| Envdiff: 0 source lost/added, 17 changed types all `TubularBigon`, two module moves 36 + 12, 0 ambiguous, PASS | verified (explanation of the 39 loose) | `envdiff.json` fields dumped (finding 4) |
| No `Hopf` import in `Lib` | verified | `git grep "import Hopf" 39f1d12b -- Lib/`: only `Lib/docs/*.md` prose |
| Hygiene | verified | branch diff: no `sorry`, `axiom`, `maxHeartbeats`, `unsafe`, `native_decide`, `@[simp]`, `private` changes; `noncomputable section` only in the two new files (sources had it at base) |
| Builds (`lake build Lib`, `Solution …`, `AxiomAudit`, census ratchet) | not checked | see below |

## Not checked

* The build lines in the receipt (`lake build Lib` etc.). Not re-run (forbidden); the head is
  built and the scratch file importing `TransvectionReduction`, `IntegerPresentation`,
  `AnnularExtension` elaborated, which is weak evidence the renamed files are consistent.
* Proof bodies of the 34 renamed declarations beyond the diff hunks: the diffs are pure name
  substitutions, so proofs were not reread.
* The receipt's item-5/6 "Not done" reasons (merging surgery rows into subject files; replacing
  `sheetSum` by `Fin n × X`) — these are scope refusals, not factual claims; not tested.
* Whether `Lib/Geometry/Manifold/Curve/CircleGluing.lean` needs its
  `import Lib.Geometry.Manifold.WhitneyEmbedding` (it is the only non-Mathlib import; the moved
  lemmas use `mfderiv` machinery that may come from it). Not checked.
* Later branches: `dfiles-a`/`dup-hom` touched `CutTransport.lean` and
  `LocalContributionsNaturality.lean` after this merge; only the latter mattered for a claim
  here and was read.

## Tool notes

* The envdiff summary line "lost 39 added 39 of which source declarations: 0 0" invites exactly
  the receipt's mistake: names that are both lost/added (hash change) and changed-type
  (`TubularBigon`) should be printed in one bucket, or the lost/added lists should exclude
  names present on both sides.
* A receipt sentence of the form "X was already done on the base" should carry the command that
  shows it (here `grep -c '/--'` would have exposed finding 1 in one line).
* The rename-map loop (old absent / new defined once) and the split partition check (declaration
  list of the source = disjoint union of the two results) are mechanical; a tool that emits both
  tables into the receipt would make this packet reviewable in minutes.
* Commits that touch `Lib.lean` or consumer imports should say so in the message; `git show
  --stat` was needed to discover finding 2.
