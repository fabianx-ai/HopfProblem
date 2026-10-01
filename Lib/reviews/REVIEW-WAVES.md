# Review of the monolith waves (two Fable reviewers, 2026-10-02)

Wave 1 (`Lib/reports/wave-1/MERGE.md`) and wave 2 (`Lib/reports/wave-2/MERGE.md`) were each checked by one
fresh Fable reviewer, read-only, brief `Lib/reports/wave-reviews/BRIEF.md`, reviews `wave-reviews/W1.md` and
`W2.md`. Head reviewed: `8ff8d81e`.

## 1. Verdicts

| slice | verdict | unsound | findings |
|---|---|---|---|
| W1 (wave 1, ten branches) | ACCEPT WITH FINDINGS | 0 | 13: 3 wrong receipt, 3 docstring, 4 citation, 1 api, 2 nit |
| W2 (wave 2, twelve branches) | ACCEPT WITH FINDINGS | 0 | 10: 4 wrong receipt, 3 docstring, 1 api, 2 nit |

Verified positively, independently of the split tool: **every declaration block of all 24 monoliths is
textually identical at base and head** modulo the recorded renames, lifts and docstring edits (W1: 2,423
ranged units by dump range plus a line-multiset pass; W2: 2,114 blocks with comments stripped). Nothing
deleted. The 82 moves out of `Lib` are safe (no `Lib` constant uses a moved name or its auxiliaries; no
probe lost) and verbatim. All 156 renames: old names gone, new names present, no clash with Mathlib today.
The 11 lifts are literally the old statements at `u = 0`. All 24 facades hold imports only. The
docstring-rewrite commits are comment-only (15 commits compared with comments stripped). Hygiene clean; all
139 commits carry both trailers.

## 2. Findings that matter

1. **Two context lines were lost in "verbatim" splits, and the tool's receipts could not see it.**
   (a) W1-1: `wave1/prism` dropped 16 `attribute [local instance] SingularHomology.integerLinearMapModule
   SingularHomology.integerTensorModule in` prefixes (14 were in force) because `split_module.py` stops a
   unit's upward extension at a blank line. Statements unchanged (they are theorems; hashes equal).
   (b) W2-1: `wave2/collar` dropped `set_option maxSynthPendingDepth 3`; two `DiskFraming` statements now
   elaborate with different instance paths (hash changed; the reviewer proved old and new definitionally
   equal by `exact`). `envdiff` classed it `PROOF-NAMING`, and the receipt explained it as proof numbering,
   which is false. Neither is unsound; both contradict "moved verbatim" / "no statement changed".
2. **Coordinator counts wrong in both merge receipts** (W1-2, W1-3, W1-13, W2-3): wave 1's "2,345
   declarations" mixes three units (2,299 top-level units = 2,423 ranged constants); wave 2 has 141 new
   modules not 151, 289 rewritten docstrings not 322, 2,072 moved declarations not 2,035. Corrected in both
   `MERGE.md` files at this commit, originals quoted.
3. **Visibility in `CubeBoundaryThreeCells`** (W2-2): 30 of the 34 new `public` have a live user in another
   piece; four (`mesh_two_of_one`, `coordinateNonconstant`, `square_nonconstant_coordinates`,
   `square_zero_mem`) are public only for two dead lemmas (`square_intrinsic_face`,
   `square_unit_mesh_endpoint_case`). The "36 dead private lemmas" claim is confirmed.
4. **Citations invented while replacing manuscript pointers** (W1-6, W1-7, W1-8, W1-9): about twenty module
   docstrings in the prism and hurewicz2 pieces attribute simplex straightening, the Kuhn triangulation and
   based-triangle classes to "the proof of Hatcher, Theorem 4.32", which argues by CW approximation; "Hatcher,
   Example 0.2" for `ℝⁿ ∖ 0 ≃ Sⁿ⁻¹`; "Milnor Theorem 8.1:" as the name of a closed-manifold corollary;
   Godement II.5.10 for the singular comparison. The rule was "cite only if sure".
5. **Docstring defects** (W1-4, W1-5, W1-10, W2-5, W2-6, W2-7): ten of morse-d's 281 docstrings state their
   sentence twice; one has a `?` placeholder; five drop a hypothesis or cite the wrong lemma; the two
   `Hopf/Proof/…/RiemannMapping` modules kept old vague docstrings, one of them wrong ("affine
   identification"). Of 179 docstrings read across both slices, the content of 168 is right.
6. **Naming** (W1-11, W2-9): `SingularHomology.formalMap_*` are lemmas about `SingularMayerVietoris.formalMap`;
   `Hurewicz.Prism.straightenedTwoCycle*` is straightening, not the prism operator; the nine names declared
   into Mathlib's `Real`/`expNegInvGlue` namespaces do not exist in Mathlib today and will clash when it adds
   them (accepted: such a clash is the signal to delete ours).

## 3. Fix list (one Opus 5.5 seat, branch `fix/waves`)

Code context (must leave every type hash equal to the BASE of its wave):
- Restore the 14 effective `attribute [local instance] … in` prefixes in `PrismOperator/{HurewiczMap,Basic,
  TwoTriangles}.lean` (W1-1 lists the declarations); the two vacuous ones stay out, noted.
- Restore `set_option maxSynthPendingDepth 3` in `Collar/RangeTransport.lean` so that
  `DiskFraming.exists_smooth_frame_near_starConvex` and `…_on_neighborhood_closedBall` get their base type
  hashes back (W2-1 gives both hashes).
Docstrings and citations (comment-only):
- W1-4 (ten doubled), W1-5 (placeholder), W1-10 (two omissions), W2-5 (two wrong lemma citations in
  `Cells.lean`), W2-6 (`exists_patch_step` and the two lighter ones), W2-7 (`discCoordinate`).
- W1-6: "Hatcher, Theorem 4.32" for the statement only, the argument described as the file's own; W1-7:
  "Hatcher, Chapter 0"; W1-8: "cf. Milnor, Theorem 8.1 (index 0)"; W1-9: drop the Godement pointer in
  `ComparisonPositive.lean:20`.
Receipts (in place, original quoted): `prism.md` (verbatim claim), `collar.md` (the false explanation),
`morselemma.md` (the imprecise one), `cube3.md` (four not three), `residue.md` (W1-12).
Not in this fix round, owner's call: deleting the 36 dead lemmas of `cube3/notneed.txt` (which would let the
four declarations of finding 3 go private again); moving the misnamed groups of finding 6.

## 4. Protocol and tool changes

- "Verbatim" is checked on the COMPLEMENT as well: every base line not covered by a moved unit must reappear
  in the pieces or be listed (prefix commands, `set_option`, `open`, `variable`, `universe`). The seats that
  did this by hand (cross, mayer) had no loss.
- A split may not drop a `set_option` unless the type hashes of the piece are unchanged; a changed hash with
  identical text is a finding, not a "proof naming".
- Tool requests for `~/lean-agent-ide`: `split_module.py` unit extension across one blank line before a
  docstring, and import insertion after `public import`; `envdiff` classes for "hash changed, `uses`
  identical including auxiliaries" (instance path) and for universe lifts, the move list to include
  hash-changed names, the full changed-type list in `envdiff.txt`.
- Counts in a merge receipt come from one stated unit and one command, quoted beside the number.
- A textbook is cited for a proof step only when the textbook's proof has that step.
