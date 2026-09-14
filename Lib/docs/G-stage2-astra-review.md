# Lane G — independent Stage-2 review

Reviewer: **astra (Devin)**, independent of Muse and the scout.
Reviewed HEAD: `699d1a4abbeaefa61dddf5890bd72317ce0b6acb`.
Repository: `/home/ox-alpha/HopfProblem`.
Observed branch: `lib/textbook-extraction-devin`, not the requested `lib/textbook-extraction`; HEAD matches. No branch change was made.

## Verdict

**NO-GO for freezing the submitted Stage-2 textbook; NO-GO for Axis-6 handoff.** The recognition theorem and the two requested design mutations are sound at the checked interface. The recovered proof is not yet a complete, hypothesis-preserving textbook argument. Legacy name resolution is not certification of the compressed statements or production visibility.

| Requested check | Verdict | Result |
|---|---|---|
| 1. FQN resolution | GO for names; NOT GO for the claim of matching signatures | All 35 distinct theorem names in G1–G6 resolve, plus five supporting definitions/structures: 40/40 checks. The self-review's 33 count is inaccurate. See signature findings below. |
| 2. Coordinates | NO-GO as current coordinates | Full census below distinguishes expected `699d1a4` drift from older wrong coordinates. |
| 3a. Drop `SecondCountableTopology M` | GO | Inner G6 signatures do not require it; an actual consolidated-headline wrapper compiled without it. |
| 3b. Sphere consolidation | GO within the stated scope | Five `rfl` equalities passed. `Hemisphere.Sphere 2` remains S², not S⁶; attaching-map types remain unchanged. |
| 4. Three load-bearing compressed signatures | NO-GO | Elisions hide structured output, unique-minimum and homotopy/dimension inputs, manifold/window data, and the exact minimality quantifier. One row also invents instances. |
| 5. Legacy module gate | GO: blocking fact independently reproduced | Production-style import fails specifically because `Hopf.Recognition` is non-`module`. Receipt's blanket location claim needs qualification. |
| 6. Textbook fidelity | NO-GO | Wrong level in §4, premature index-3 elimination, missing codimension-two Whitney hypothesis, and incomplete minimum/placement arguments. |

These are verdicts on the submitted document. The proposed uncommitted edits remove several false claims but do **not** make the remaining proof or ledger GO.

## Numbered findings

Document line references in this section refer to the **submitted `699d1a4` blob**, before my edits; Lean source coordinates refer to live HEAD. This avoids ambiguity from the review's own inserted text.

1. **Wrong regular level in the handle trade — G.md:96–104.** The level below the 2-handles need not be simply connected: the 1-handles create fundamental-group generators and the 2-handles can kill them. Milnor §8 explicitly warns that multiple index-1 points spoil the simple-connectivity assumption at the early level. The source trade at SphereTopology:9796–9818 requires a cut with original indices ≤2 below and ≥3 above, a unique minimum, and a critical-free band containing a point above the cut. Its disk/level-basin construction is at 7574–7658, not an assertion that all early levels inherit π₁(M). **Fix:** work after the original 2-handles, transport the selected belt loop to that cut, use the relative disk/isotopy placement, and transport back to cancel. I replaced the incorrect paragraph with this outline, explicitly leaving the preservation proof open.

2. **Whitney's codimension-two hypothesis is missing — G.md:124–130.** The dimensions are correctly S³ belt, S² attaching sphere, in N⁵. But ambient simple connectivity alone is insufficient for the cited Whitney theorem. Milnor Thm. 6.6 uses moving dimension r=2 and fixed dimension s=3 here and requires injectivity π₁(N minus fixed sheet) → π₁(N), as well as orientation and Whitney-loop conditions. Merely writing `(p,q)=(3,2)` does not avoid this requirement. Milnor's proof of Thm. 6.4 supplies the extra complement argument in the index-2 case. The local source has meaningful additional data: Recognition:8331–8368 returns lower-level circle nullhomotopies, obtained from `last_index_two_collapse_is_primitive` at 8295 (call at 8375–8376); `cancel_from_complete_middle_family` at 8834 takes `hnull` at 8844; SphereTopology:6599–6628 consumes lower-level `hnull` for the single-belt-intersection theorem. **Fix:** recover the lower-level-to-belt-complement transport and the relative preservation hypotheses as mathematics, and match the exact lane-F input. Do not replace it with a generic simply-connected-level claim. I marked this as an explicit open Stage-2 obligation. This is a narrative defect, not a claim that the existing Lean theorem is false.

3. **Index 3 is eliminated too early — G.md:121–137.** Surjectivity of ∂₃: Z^c → Z^r, followed by minimality, eliminates index 2 when r>0; it does not imply c=0. A map Z^c → 0 is surjective for any c. In the actual proof, Recognition:8957 concludes only index-two count zero; 9017 eliminates index 4 by negation; 9243 requires both counts zero before concluding index-three count zero and total count two. **Fix:** justify that later ≥4 handles preserve H₂, first eliminate 2, then 4, then use H₃(M)=0 (or the source's complete-block bijectivity/count argument) to eliminate 3. The revised narrative now follows this order and includes the r>0 qualification for finding a unit.

4. **The purported complete proof of unique extrema is not complete — G.md:75–88.** “Basins are open and disjoint... cancelable or connectable” does not prove a reduction of critical count while retaining excellence and the comparison class. The source explicitly uses `exists_excellent_morse_reduction_of_multiple_minima` through SphereTopology:6996–7012; the duality is at 7014–7036. The narrative must explain the connected 0/1-handle graph and the corresponding cancellation, with preservation of the requisite data, or invoke a precisely stated reviewed lemma. Also state that minimum counts are attained by well-ordering of the nonempty set of finite critical counts, not just finiteness of each critical set. **Still open.** As written, §§1–7 also mix Lean names and lane references into what is advertised as ordinary-mathematical canonical text.

5. **Load-bearing signature compression changes or conceals the boundary — G.md:245–250, 326–332, 464–468.**
   - `exists_minimal_excellent_morse_system`, SphereTopology:6290–6302, has **neither** `[PathConnectedSpace M]` **nor** `[Nonempty M]`, both added in the ledger. Its output includes `∃ _ : AdaptedWindows E f`, not merely an “excellent” proposition. Its minimality compares against every smooth Morse g with `Set.InjOn g (criticalPoints E g)`; g need not be ordered or supplied with windows.
   - `exists_one_to_three_handle_trade`, SphereTopology:9796–9818, hides S, hf, hm, e, hdim, the points m/q and **hminimum**. These are not repeated cosmetic binders. Its output is an excellent Morse function of the same total count, count1 decreased by one, count3 increased by one, all other index counts unchanged. It does not promise an ordered output directly.
   - `minimal_ordered_index_two_count_zero`, Recognition:8957–8973, hides `[Nonempty M]`, `[PathConnectedSpace M]`, `{f}`, S, hf and the exact smooth/Morse/distinct-value comparison class in hminimal. No mysterious extra hypothesis is present beyond those, but those are structurally material inputs and must be recorded.
   **Fix:** copy complete source signatures, preserving actual universes and comparison classes. These remain unexpanded in the historical ledger, explicitly downgraded by the new banner; this review does not manufacture an Axis-5 packet.

6. **A second G2 row is substantively incorrect, not just compressed — G.md:256–259; self-review:37–41.** `minimal_excellent_morse_extreme_counts_one` at SphereTopology:7014–7026 takes no hdim and no homotopy equivalence. Its conclusion is count0=1 and count(finrank E)=1, not literally count6=1. It takes path-connectedness, windows, smoothness, Morse data, and minimality. Muse's assertion that this theorem uses literal six is false. **Fix:** retain the general theorem; identify specialization at finrank=6 separately. Also, a 1+5 cost function in the outer-minimization theorem is definable at general dimension; it is the downstream negation/trade interpretation that needs dimension six.

7. **Coordinates: expected drift plus pre-existing stale structure locations — G.md:154, 170–177, 202, 222–533.** The full census below supplies actual decl-start lines. The git diff explains Recognition −9 and subsequently a further −6 (total −15), and SphereTopology +1 import followed by −49 and −12 (net −60). The early SphereTopology rows therefore move +1. These are expected post-verification drift, **not evidence that the earlier census was dishonest or mistaken**. Separately, `TwoDiskDecomposition` and `SublevelDisk` were already at 5199/5283, not 8073/8157, before the small F0b shift; this is an older stale-source error. G.md:154's 9444 points to neither the old declaration start nor the current instance line (9429). **Fix:** refresh live source references with a new head stamp; keep historical receipts explicitly historical. I retained the historical table for traceability and added a prominent pointer to this census rather than silently claiming a regenerated packet.

8. **G1<G2<G3 is not a topological order — G.md:173–180; self-review:50–54.** G2 includes `exists_minimal_ordered_morse_system_without_outer_indices`, whose proof consumes G3's `outer_index_minimal_outer_counts_zero` (SphereTopology:10195 onward). Split G2 into preliminary minimization and post-trade assembly. The placement in G.md:190/receipt:48 also combines preliminary G2 and downstream G5 counts in one file; the import graph must be settled rather than treating the thematic rows as green boundaries. I replaced the false row-order claim with this warning. File splitting/ownership remains open.

9. **Do not silently normalize universes — G.md:540–543.** The checked homology interface is universe-zero: `SingularMayerVietoris.SingularHomology (Y : Type)` at Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean:853. The compiler prints G1 homology and Recognition-side statements in Type, while Reeb and initial minimization are universe-polymorphic. Blanket conversion to Type* is not a verbatim move. **Fix applied in prose:** preserve elaborated universes; require a separate design/probe for generalization. No Lean statement was changed.

10. **Seam gate is real, but receipt overstates the legacy inventory — G-INTERFACE_RECEIPT.md:29–38,59.** `module; public import Hopf.Recognition` fails at import for exactly the stated non-module reason. `SurgeryWindows.lean` is also legacy (its imports start at line 6 without a module header); it owns `AdaptedWindows` at 1804 and native index at 6741. Recognition and SphereTopology still contain the geometric and Reeb cone. However `SingularMayerVietoris.SingularHomology` already lives in a real public module (MayerVietoris:6–11,853), and `SphereHomology.UnitSphere` is in Lib/SingularHomology/Sphere. The negative import test proves the current path is blocked, not that every cited type is legacy or that all four lane labels are individually necessary. C is also a consumer-routing dependency. **Fix:** use a per-provider seam inventory, then actual production provider/consumer probes. Existing self-review and receipt remain untouched as historical artifacts.

11. **Theorem statement/reference hygiene — G.md:30–44,572.** Smale Theorem A is correctly the closed smooth homotopy-sphere recognition theorem in dimensions ≥5; this lane's n=6 result is a legitimate specialization and its content is FREE. Make “without boundary” explicit (now done). “Strictly stronger per unit of generality dropped” is not a mathematical relation: Mathlib's `proof_wanted` at Geometry/Manifold/PoincareConjecture.lean:43–44 has the same conclusion in all dimensions without an explicit smoothness or compactness assumption. Our arbitrary six-dimensional real normed model is equivalent to Euclidean space. I replaced the strength claim with the correct specialization statement. Finally the in-tree Stage-2 review labels itself self-review; it cannot satisfy the independent-review condition by being listed as independent in G.md's open item 5.

## Live coordinate census

Every row below was matched at its declaration start with the search tool in the actual three Hopf sources, not inferred solely by applying a delta. `ST` = Hopf/SphereTopology.lean, `Rec` = Hopf/Recognition.lean, `SH` = Hopf/SingularHomology.lean. Prefix every dotted name by `Mathoverflow1973.`. All 40 also passed compiler name checks.

| Declaration | File | Submitted line → live line |
|---|---|---|
| Smale.simplyConnectedSpace_of_homotopySixSphere | SH | 14047 → 14047 |
| Smale.pathConnectedSpace_of_homotopySixSphere | SH | 14052 → 14052 |
| Smale.homotopySixSphere_homology_subsingleton | ST | 14226 → 14166 |
| MorseCancel.exists_minimal_excellent_morse_system | ST | 6289 → 6290 |
| MorseCancel.exists_index_ordered_morse_system_preserving_critical_points | ST | 6942 → 6943 |
| MorseCancel.minimal_excellent_morse_extreme_counts_one | ST | 7013 → 7014 |
| MorseCancel.exists_outer_index_minimal_ordered_morse_system | ST | 10004 → 10005 |
| MorseCancel.exists_minimal_ordered_morse_system_without_outer_indices | ST | 10194 → 10195 |
| MorseCancel.exists_excellent_indexed_morse_birth | ST | 8636 → 8637 |
| MorseCancel.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum | ST | 9600 → 9601 |
| MorseCancel.exists_one_to_three_handle_trade | ST | 9795 → 9796 |
| MorseCancel.exists_one_to_three_handle_trade_at_cut | ST | 9883 → 9884 |
| MorseCancel.exists_one_to_three_handle_trade_of_ordered_indices | ST | 9976 → 9977 |
| MorseCancel.outer_index_minimal_index_one_count_zero | ST | 10064 → 10065 |
| MorseCancel.outer_index_minimality_neg | ST | 10112 → 10113 |
| MorseCancel.outer_index_minimal_outer_counts_zero | ST | 10145 → 10146 |
| Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere | ST | 14338 → 14278 |
| Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks | ST | 14360 → 14300 |
| MorseCancel.exists_middle_index_blocks | ST | 14386 → 14326 |
| AdaptedWindows.exists_ordered_middle_family | ST | 14468 → 14408 |
| AdaptedWindows.exists_canonical_middle_family | Rec | 2688 → 2688 |
| MorseCancel.canonical_middle_matrix_surjective | Rec | 3365 → 3365 |
| AdaptedWindows.exists_primitive_functional_unit | Rec | 7365 → 7365 |
| AdaptedWindows.exists_first_middle_pivot | Rec | 3847 → 3847 |
| MorseCancel.exists_native_belt_cut_family | Rec | 8340 → 8331 |
| MorseCancel.cancel_from_preserved_unit_belt_cut | Rec | 8689 → 8680 |
| MorseCancel.cancel_from_complete_middle_family | Rec | 8843 → 8834 |
| MorseCancel.minimal_ordered_index_two_count_zero | Rec | 8966 → 8957 |
| MorseCancel.minimal_ordered_index_four_count_zero | Rec | 9026 → 9017 |
| MorseCancel.ordered_no_middle_indices_count_two | Rec | 9258 → 9243 |
| MorseCancel.critical_pair_of_surgery_count_two | Rec | 9385 → 9370 |
| Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points | Rec | 9344 → 9329 |
| MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere | Rec | 9413 → 9398 |
| MorseCancel.nonempty_homeomorph_of_homotopySixSphere | Rec | 9431 → 9416 |
| Smale.homeomorphic_sixSphere_of_homotopySixSphere | Rec | 9442 → 9427 |
| MorseCancel.canonicalMiddleMatrix | Rec | 3359 → 3359 |
| Smale.twoDiskDecompositionOfSublevels | Rec | 9289 → 9274 |
| Smale.homeomorphSphereOfSublevelDisks | Rec | 9339 → 9324 |
| Smale.TwoDiskDecomposition | ST | 8073 → 5199 |
| Smale.SublevelDisk | ST | 8157 → 5283 |

## Design-mutation checks and their limits

The checked G6 section (Rec:9274–9432) has no SecondCountableTopology M binder until the headline at 9429. The actual inner wrapper calls two-critical-point existence, then Reeb and the finrank rewrite. Source search throughout Recognition found SecondCountableTopology on auxiliary X/Y/Z sheet types at 4856–4858,5585–5586,5771,5889, but not an additional assumption on M. These auxiliary sheet hypotheses must not be erased during extraction; they do not invalidate dropping the headline's unused M instance. The wrapper probe is the decisive test: it applies the existing inner theorem with only the recorded manifold, compactness and dimension assumptions. Compactness implies second countability here because the finite-dimensional manifold has a finite chart subcover, not because arbitrary compact spaces are second countable.

Six equality examples compiled by `rfl`: the five advertised S⁶ spellings against the Euclidean R⁷ unit sphere, and Hemisphere.Sphere 2 against the R³ unit sphere. The same successful probe constructed the consolidated headline without SecondCountableTopology M. The G4 canonical matrix (Rec:3359) and G5 cancellation family (8834) retain γ with domain Hemisphere.Sphere 2; no substitution of S⁶ into these binders is warranted. Generic Reeb retains Sphere(finrank E) until hdim is rewritten; it is not uniformly a six-sphere theorem.

## Commands and observed results

Read in order: collaboration protocol, lean-protocol (especially Stage 2 and Axis-5 GO), all G.md, Muse self-review, receipt, scout §1(1)–(15). Then searched and read live declarations/proofs, the actual Mathlib Poincaré statement, and the relevant Lib headers.

Environment for Lean commands:

```sh
source /home/ox-alpha/muse-env.sh
```

This selects Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, and the supplied process-local safe-directory environment. No git configuration was written.

- `git status --short`, `git rev-parse HEAD`, `git branch --show-current`: matching requested commit, alternate branch as recorded; initially only pre-existing untracked AGENTS.md.
- Declaration-start searches using the provided grep tool across Hopf/{SingularHomology,SphereTopology,Recognition}.lean: 35 theorem rows plus five support names located; census above.
- `git diff 1cc1784 699d1a4 --unified=0 -- Hopf/SphereTopology.lean Hopf/Recognition.lean`: verified exact movement causes. Recognition removes 9 then 6 lines. SphereTopology adds one import and removes 49 then 12 lines.
- `ps -eo pid,comm,etime,args`: inspected shared-machine activity; no build launched.
- `lake env lean /tmp/G_Astra_Probe.lean`, first run: **exit 1**, after all 40 names and six rfl equalities succeeded; final wrapper failed to parse ≃ₕ because the probe omitted `open ContinuousMap` (`Mathlib.Tactic.subscriptTerm` error). This was a probe-context error, not an API failure.
- Same command after adding `open ContinuousMap`: **exit 0**. All 40 name checks, six rfl equalities, and the consolidated wrapper without SecondCountableTopology M passed. Probe imports only Hopf.Recognition and opens scoped Manifold/ContDiff plus Mathoverflow1973/ContinuousMap.
- `lake env lean /tmp/G_Astra_Module.lean`: **exit 1**, expected negative control. File contents: `module`, `public import Hopf.Recognition`, `public section`, and a fully qualified check of the inner recognition theorem. Exact diagnostic: `cannot import non-\`module\` Hopf.Recognition from \`module\`` at line 1:0. No downstream name-resolution or universe error substituted for this result.
- `lean --version`: confirmed pinned version above.
- `git diff --check`: **exit 0** after proposed documentation edits.

No aggregate public-provider/consumer certification was attempted or claimed. `#check` verifies the imported constants, not the literal compressed snippets, and successful import trusts existing compiled dependencies; no comprehensive rebuild or axiom audit was performed.

## Textbook reference verification

Smale, Annals 74 (1961), Theorem A: the indexed primary text states that a closed smooth n-manifold of the homotopy type of Sⁿ, n≥5, is homeomorphic to Sⁿ. This agrees with the intended n=6 headline. The source was located by web search under the title *Generalized Poincare's Conjecture in Dimensions Greater Than Four* (University of Chicago copy). Direct webfetch returned raw PDF, so I do not claim a full page-by-page review of Smale's paper.

Milnor, *Lectures on the h-Cobordism Theorem*, Princeton 1965: fetched the Edinburgh copy located by web search and extracted its existing text in memory with:

```sh
curl -fsSL "https://webhomes.maths.ed.ac.uk/~v1ranick/papers/hcobord.pdf" | pdftotext -layout - -
```

Exit 0; read the actual extracted passages for Thms. 6.6, 8.1 and 9.1 and the index-2 discussion in the proof of 6.4. OCR has spacing errors, but these statements are legible:

- 8.1 assumes a smooth triad; the index-1 part uses simple connectivity of W and the incoming V and absence of index-0 points, and trades 1 for 3 by an auxiliary (2,3) pair. The closed-manifold adaptation must account for its retained minimum rather than pretending the triad statement applies literally.
- 9.1 assumes simply connected W,V,V′, vanishing relative homology H*(W,V), and dim W≥6, and gives a product cobordism. Its proof invokes 8.1, duality and 7.8. G uses the same elimination pattern plus Reeb; it is not literally a one-line specialization of the triad theorem without explaining the boundary reduction.
- 6.6 has the additional complement π₁-injectivity condition in moving dimension 1 or 2. The S²/S³/N⁵ dimensions in G do not bypass it.

## Changes left uncommitted and open work

Only `Lib/docs/G.md` was modified in the repository. Changes: explicit NO-GO/draft banner; boundaryless hypothesis; correct relation to Mathlib; corrected trade cut; corrected middle-index order and r>0 algebra step; explicit Whitney complement obligation; dependency-order warning; preservation of source universes. No Lean implementation or signature was changed. Historical coordinates, compressed rows and the original self-review/receipt were deliberately not relabeled as freshly certified.

Open before Stage-2 GO: expand the unique-minimum reduction, relative handle trade and codimension-two Whitney complement argument; state exact reviewed seam hypotheses; remove implementation prose from the canonical mathematics; have the author accept the corrections. Open before implementation: repair full signatures and coordinates, split dependency boundaries, finish the legacy provider cone, then perform the required production-context interface/consumer checks for designed statements (or the protocol's extraction-mode docstring/public-consumer obligations for truly verbatim moves).

Temporary probe files were removed after recording their outcomes. No explicit olean/ilean artifacts were produced by these commands. Final repository status: modified G.md and the pre-existing untracked AGENTS.md only. No commits, pushes, builds, package updates, cache downloads, cleans, or package writes were performed.
