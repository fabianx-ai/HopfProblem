# Lane G — independent re-review at bd9c393

Reviewer: astra (Devin).
HEAD: `bd9c3936cc75251a9685449e6dbf7c8e9295e2af`.
Observed branch: `lib/textbook-extraction-devin`.
Scope: findings 1–10 in `G-stage2-astra-review.md`, the revised ledger, and the actual proof mechanisms in §§3–5. Repository kept read-only.

## Verdict

**NO-GO as written. Substantial repairs accepted, including the specific G2a/G2b repair for finding 8.**

The remaining principal blockers are narrowly identifiable: the Whitney complement explanation still omits the essential relative disk-avoidance step and cites the wrong transport mechanism; the base handle-trade signature was dropped rather than expanded; and the trade narrative claims preservation of the cut after cancellation without a corresponding source guarantee. These are documentation/interface defects, not findings that the existing recognition theorem is false.

## Findings 1–10: disposition

| Original finding | Re-review |
|---|---|
| 1. Wrong trade level | **Partly fixed.** Correct original cut and birth/placement chain; new overclaim about final cancellation preserving the cut must be removed. |
| 2. Whitney complement hypothesis | **Still open.** The condition is now acknowledged and the lower-level hypothesis is correctly identified, but its conversion to a complement contraction is not correctly recovered. Exact missing source mechanism below. |
| 3. Premature index-3 elimination | **Fixed in §§3–5.** Order is 2, then 4 by negation, then 3 using H₃=0. Remove the unrelated false `3 < k` gloss at G.md:1109. |
| 4. Unique-minimum proof | **Substantially fixed.** Named component-joining, branch-realization, higher-minimum cancellation and excellence-preservation chain matches source. Small comparison-class and consecutive-pair clarifications remain. |
| 5. Compressed load-bearing signatures | **Partly fixed, not complete.** Initial minimization and index-two-zero signatures are repaired; `exists_one_to_three_handle_trade` is missing from the typed ledger. |
| 6. Wrong extreme-count signature | **Fixed.** G.md:371–383 agrees with ST:7014–7026: no hdim/e, top count at finrank E. |
| 7. Coordinates | **Partly fixed.** Main typed coordinates and Reeb structure coordinates repaired; thematic table stays at old coordinates; an accidentally included theorem has a wrong new coordinate. |
| 8. Backward G2/G3 dependency | **Fixed for the identified grouping/placement defect.** G2a → G3 → G2b and corresponding file assignment are consistent. This is not a complete helper-closure or green-module certificate. |
| 9. Universe normalization | **Fixed.** Preserve source universes, as recorded at G.md:1168–1172. |
| 10. Blanket legacy-provider claim | **Fixed as an inventory correction.** Receipt:29–45 distinguishes the geometric legacy cone from public homology modules. Production extraction remains gated. |

## 1. Section 3: what the proof bodies actually do

ST:6290–6319 constructs the first minimum by `Nat.find` over **all excellent Morse functions**, then supplies adapted windows. The revised explicit signature at G.md:341–353 correctly removes the invented path-connected/nonempty instances and exposes the windows and complete minimality quantifier.

ST:6103–6122 finds an index-one handle with two attaching points **not Joined in the lower sublevel**. It does not yet assert that the given field's two ends flow directly to two distinct minima. ST:6192–6223 calls `realize_one_handle_minimum_branches`, constructs compatible chart models, orders the two minimum values using distinctness, and invokes `cancel_realized_higher_minimum` with the higher minimum first. ST:6124–6190 proves uniqueness of the connecting orbit, applies `exists_flow_preserving_consecutive_pair` (6168–6170), performs isolated (0,1) cancellation, then obtains distinct critical values from surviving germs (6185–6189). ST:6996–7036 invokes this reduction, contradicts minimum count, and transfers to -f.

Thus the revised mechanism is materially better and identifies the right reduction. Suggested final precision at G.md:103–118: distinguish disconnected attaching components from the branches after field realization, explicitly mention the consecutive-value rearrangement, and obtain at least one minimum from compactness/nonemptiness before assuming that a count other than one means at least two. Replace the informal generic-flow assertion by the actual component argument.

At G.md:99–101 the secondary minimum is described only among ordered competitors. The actual source ST:10005–10063 first minimizes the 1+5 cost among **all equal-total-count excellent competitors**, then orders the chosen function and transports counts. The trade output need not be ordered. Either say this stronger comparison class, matching the now-correct signature at G.md:403–410, or explicitly reorder the trade output before applying minimality. This is a short logical repair, not a new mathematical construction.

G2a's label “no surgical content” (G.md:337–338) is not a proof-dependency claim that can be maintained: the extreme-count theorem just traced uses (0,1) cancellation. Its provider must include or import the reviewed cancellation seam.

## 2. Section 4: correct cut, but no final cut-preservation promise

The original cut is correctly described by `hlow ≤2` and `hhigh ≥3`; in fact all original index-two critical points are below it. ST:9796–9818 gives the base trade's exact signature. Its proof:

1. Chooses support U=f⁻¹(Ioo l u), with a<l (9819–9826).
2. Births the pair, retains old critical germs and controls new values.
3. Obtains equality of the old/new level at a, new regularity, the first-new-value gap, and the lower-index bound (9831–9837).
4. Preserves the unique index-zero point and calls the unchanged-cut cancellation wrapper (9847–9861).
5. Computes the total and individual index counts (9862–9882).

The geometric placement really uses `exists_transverse_middle_belt_loop` and `exists_new_attaching_circle_placement` at ST:9040–9047, then realization of the transverse level isotopy and exclusion of other connections at 9405–9439. Two points on the negative-coordinate unit sphere alone are not the transverse single-intersection construction.

**G.md:143's “without disturbing the cut” overstates the result.** ST:9365–9398's preserved-middle-cut theorem assumes the equality of f/g levels as input, but returns excellence, pair removal and surviving indices, not equality of the final h-level to the old cut. Its terminal call at 9437 is `cancel_transverse_pair_after_flow_preserving_descent`. The latter first rearranges critical values (9324–9326), then cancels in an isolating band (9347–9352), and returns no final cut identity. The same limitation is visible in the exact ledger output at G.md:476–486.

Fix: say “using the cut preserved by the birth and geometric placement,” not that the final cancellation preserves it. The final count contradiction needs no such additional assertion. This also avoids silently confusing this trade with the distinct preserved-data machinery for the middle campaign.

## 3. Section 5: the exact missing complement argument

The lower-level induction is real. ST:5716–5775 starts from the first sublevel disk, transfers between consecutive regular levels, and applies `upper_circle_nullhomotopies` at index 2 or 3. ST:5821–5861 specializes it to the lower level of the chosen index-two point. In this specialization earlier noninitial points have index **2** (5859–5860); index 3 belongs to the more general helper, not a predecessor in this particular ordered index-two prefix.

However the dimension argument at G.md:196–200 only moves a **circle** off the upper belt. A contraction in the lower level must also avoid the **lower attaching sphere** if it is to return through the complement. That missing requirement is exactly what the actual code proves:

- `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean:667–689`, `ImageComplement.nullhomotopic_of_ambient_nullhomotopic`: relative homotopy/disk avoidance with the dimension inequality.
- Lines 691–703, `ImageComplement.circle_nullhomotopies`: requires **2 + dim(obstacle) < dim(level)**, not only circle avoidance.
- Lines 705–733, `SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_sphere_dimension`: first contracts in **OldComplement**, using that inequality, then transports the entire nullhomotopy through `complementHomeomorph` to **NewComplement**.
- For the chosen index-two handle, the lower obstacle is the attaching **S¹**, so **2+1<5**. For the general index-three induction step, it is S² and **2+2<5**. These are the missing disk-avoidance inequalities.
- Lines 798–827 specialize this to the signed chart.
- `Hopf/SingularHomology.lean:19932–19961`, `MorseSurgeryData.nonempty_belt_tubularBigon`, calls that chart lemma at 19956–19957 and then `nonempty_tubularBigon_of_complement_contractions` at 19959. This is the direct Whitney-disk bridge from `hnull`.
- SurgeryWindows:1339–1372 separately recovers contractions in the whole upper boundary by moving circles off the belt and using the already-proved complement contractions. Lines 1548–1560 are the upper-level wrapper used by ST's induction.

**G.md:201–209 incorrectly attributes the complement contraction to `exists_native_belt_cut_family`.** Rec:8331–8408 collects hnull from `last_index_two_collapse_is_primitive` and transports the attaching family and matrix between two **regular cuts above the chosen critical value**. Its `hba` and `hband` at 8379–8391 make this explicit. This is not the old/new surgery-complement transport across the handle.

Also replace “belt S³ ... boundary of its descending disk” (G.md:201–202) by **boundary of the four-dimensional cocore**. The descending/core disk of an index-two handle is two-dimensional and has S¹ boundary. The source belt is parameterized by PositiveCoordinates, with rank 4 (e.g. SingularHomology:19974–19975).

`hnull` is a **sufficient lower-level input**, not literally the same proposition as complement π₁-injectivity (G.md:215–216). The chart/complement/avoidance lemmas above convert it to the stronger assertion that every circle in the belt complement contracts. This is why the source works; the revised narrative still needs to state this conversion.

The remainder of the middle campaign is correct: Rec:8874–8885 performs primitive-functional slides, then moves the chosen index-three point first; 8921–8955 proves consecutiveness, transports the unit and flow data, cancels, and recovers excellence. Rec:8957–9015 eliminates index 2; 9017 onward applies -f for index 4; 9243–9262 uses complete blocks and equal matrix sizes to eliminate index 3. G.md:223–227 now has the correct mathematical order. **Delete G.md:1109's alleged `3 < k` hypothesis:** `ordered_no_middle_indices_count_two` has no binder k and no such hypothesis.

## 4. Signature inventory and coordinates

The claim “all signatures are now verbatim” cannot be accepted as a complete ledger claim:

- **Missing node:** `MorseCancel.exists_one_to_three_handle_trade` has no `theorem` entry in the revised ledger. It is still named in the narrative and thematic table. G3 now passes directly from `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` to `exists_one_to_three_handle_trade_at_cut` at G.md:456–488. Restore ST:9796–9818 before `_at_cut`; its body calls the base trade. This was one of the three explicitly load-bearing signatures in finding 5.
- **Accidental extra node:** G.md:736–748 includes `AdaptedWindows.no_connection_above_canonical_cut`, absent from the original 35-theorem inventory. Its signature matches Rec:3397–3409, but the ledger attaches **3365**, the coordinate of the preceding matrix-surjectivity theorem. Assign it an intentional role/consumer, or remove it from the promised output set. The matrix theorem at G.md:704–734 includes its proof body and lacks its own correctly placed source annotation.
- The main inspected expanded signatures (initial minimization, extreme counts, outer minimization, G2b, canonical matrix surjectivity, belt-cut family, full cancellation, index-two-zero and count-two) retain the actual source binders/results. The two expanded signatures from finding 5 that are present are repaired. This is a source comparison, **not** a new aggregate elaboration receipt or a claim of a byte-for-byte automated comparison of all 35 blocks.
- G.md:751–755 falsely describes `exists_canonical_middle_family` as a universal unit-column property. Its displayed/source conclusion is a family with the same ranges and a pointwise flow-orbit parametrization; it does not assert a unit. Units arise later from `exists_primitive_functional_unit`.
- The thematic table at G.md:260–267 still carries old coordinates and G2 as a single row. The header explicitly says 1cc1784, so treat it as historical, not as the live source map advertised elsewhere. Relabel the table unmistakably historical or update it to agree with the current ledger. The new typed Reeb structure locations at 1158–1161 are correct.

## 5. Finding 8: the split resolves the identified cycle

**Yes:** the explicit row/file split now resolves the particular issue I raised.

- G2a supplies initial/ordered/outer-minimal systems.
- G3 derives vanishing of outer counts.
- G2b assembles `without_outer_indices`. Its source proof at ST:10215–10220 calls G2a's outer minimization, rewrites finrank=6, then calls G3's outer-count theorem.
- G.md:282–288 and receipt:55–58 consistently place G1+G2a in MinimalSystem, G3+G2b in HandleTrade, G4+G5 in MiddleBlocks, G6/headline in Smale. G5 counts no longer live in the preliminary MinimalSystem file.

This accepts the requested ordering repair; it does not certify all supporting helper ownership or module imports. In particular the G2a extreme-count proof still needs its cancellation dependencies, and the source remains legacy-gated. No additional cycle was established by this review.

## Checks and scope limits

- Read the collaboration protocol, revised G.md in full, updated receipt and prior findings; traced named proof bodies, following helpers outside the suggested ranges when necessary.
- `git rev-parse HEAD`: exact requested bd9c393; branch as above.
- `git diff 699d1a4 bd9c393 --stat -- Hopf Lib/Geometry Lib/AlgebraicTopology`: **empty**, establishing that the relevant Lean sources are unchanged from the previous probe head. This allows carrying forward the previous name-resolution/design-mutation/module-negative evidence, but does not certify the newly edited ledger.
- Source grep located the missing base-trade entry, extra no-connection declaration, and precise complement-provider call sites. Source reads compared the revised load-bearing declarations and mechanisms against their implementations.
- `git diff --check`: exit 0; initial and final status contains only the pre-existing untracked AGENTS.md.
- No Lean compiler or build was run in this re-review, no new Lean probes created, no package operations, no repository edits, no commits or pushes. No new provider/consumer certification is claimed.

## Minimal repair list

1. Restore the base trade signature; fix the accidental extra declaration's coordinate/ownership.
2. Limit “unchanged cut” to birth/placement inputs, not the final cancellation output.
3. Replace §5's contraction paragraph by old-complement disk avoidance (2+1<5), complement homeomorphism, then the tubular-bigon consumer; separate this from regular-cut family transport and correct core/cocore language.
4. Align secondary minimality with all excellent equal-count competitors, or explicitly reorder the trade output.
5. Remove the false unit-column and `3 < k` glosses; reconcile the historical table with the new split.

After those changes, the surviving issues are much smaller than in the initial review. The corrected G2a/G2b ordering need not be redesigned again.
