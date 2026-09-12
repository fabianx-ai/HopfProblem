# Review of the integration of lanes C, E2, F, G, J (head 856e4762)

*Independent review, 2026-09-12, by the coordinating reviewer (Claude Fable). Full build performed; `lib/textbook-extraction` fast-forwarded to 856e4762 after both builds were green.*

# Integration of lanes C, E2, F, G, J onto `lib/textbook-extraction`

Reviewer's summary. The five branches (`lib/C-hurewicz` accd1ed1, `lib/E2-transversality` 8becf61c, `lib/F-whitney` e47b908a, `lib/G-smale-recognition` 8e8ea406, `lib/J-tori` 43554f62) were merged with `--no-ff` onto lane A (527ac353) in that order; no conflicts; `git diff --check` clean. Integration head **856e4762**; `lib/textbook-extraction` was fast-forwarded to it after both builds came back green.

**Build (toolchain v4.33.0, seeded from lane A's oleans):** `lake build Lib` 57 s, 0 errors, 78 warnings (all lane A's `dupNamespace`); `lake build Solution S6Shortcuts S6 Challenge` 639 s, 8,824 jobs, 0 errors, 79 warnings (same 78 + the pre-existing `sorry` in `Challenge.lean`). `mathoverflow_1973` depends on `[propext, Classical.choice, Quot.sound]`.

---

## Lane C (code) — what is verified

- **Axioms:** 32 of 32 landed declarations print exactly `[propext, Classical.choice, Quot.sound]` (`cubeChain_eq_sum_simplices`, `normalizationHomotopy`, `classOperator`, `crossProductHomology`, `factorMap_unique`, `exists_filling`, … full list in the review).
- **Statements under `Hopf/`:** 15,089 declarations compared against 527ac353 — 0 new, 0 changed statements; 11 proofs changed with identical statements (the ten `SixSphereCube.*` re-derivations in `Hopf/Recognition.lean` and `FourthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop`). Exactly what C11 claims.
- **Provenance:** every move commit carries range, byte count and SHA-256 — good. Two of four sampled hashes reproduce byte-for-byte (`4b9b9d7` CrossProduct, `63b933a` HomotopyExtension); the content of all four matches modulo the announced renames.
- **Placeholders:** none. **Stock ratchet:** 5,170 → 3,893 with the prefix list untouched. **Shims:** the 8 new `FirstHurewicz.*` aliases and 3 `collapseLift*` names all resolve. **Scope:** only lane-C files touched.

## Lane C — what is not done (numbered, actionable)

1. **The headline is not landed.** `hurewiczLinearEquiv` at general `n` (ledger C10) does not exist; `Hopf/Hurewicz.lean` still holds `ThirdHurewicz` 631 + `FourthHurewicz` 150 + `FifthHurewicz` 135 declarations (9,631 lines) and `Hopf/Recognition.lean` `SixthHurewicz` 140. Either land the C10 assembly the report designs (class-operator boundary relation, `hurewiczMap`/`hurewiczInverse`, both round trips, then delete the per-degree blocks) or record the obstruction as the task's "honest obstruction" clause requires.
2. **No Axis-5 interface receipt.** `Lib/docs/C.md` §20 schedules `C_InterfaceCheck.lean` + consumer probe + `Lib/docs/C-INTERFACE_RECEIPT.md` "when lane A lands" — every C commit is on top of lane A. Produce the receipt at 856e4762. Also rewrite §19 with the signatures that actually landed (`HigherHurewicz.*`, `PeriodTorusHigherHomology.*`, `SphereCube.*`; none of the §19 target names exists) and put the remaining C10/C13 nodes in the protocol's `ChallengeNode` form (signature, visibility, imports, dependencies, commit_boundary, focused_check, return_seam — currently 0 of those fields appear).
3. **FREE-rule violations in `Lib/`:** `PeriodTorusLineBundle.ChernCocycle.{simplexFace_comp, singularSimplex_face_face}` (`Lib/AlgebraicTopology/Hurewicz/HomotopyExtension.lean:265,290`); nine `SixSphereCube.*` declarations on general-`n` content (`Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean:42–116`); the degree-2 theorem `SecondHurewicz.SimplyConnected.hurewiczLinearEquiv` sitting in `Lib/…/PrismOperator.lean:4460`; dimension-general content under `ThirdHurewicz.*` (11 declarations, PrismOperator) and `FourthHurewicz.CubeSubdivision.*` (75, CubeChainDecomposition). Rename with shims; start the `HigherHurewicz → Hurewicz` rename commits.
4. **Docstrings:** 9 of 12 new files have no module docstring (only `CrossProduct`, `CubeChainDecomposition`, `Straightening` do); 11 of 12 have no `/-! ### -/` sections; 1,265 of 1,326 public declarations have no docstring. `CrossProduct.lean` is the model — apply it to the rest.
5. **Report corrections (`Lib/reports/C.md`):** census is 5,170 → 3,893 (not "5,024 → 3,927"); `Hopf/Hurewicz.lean` is 22,910 → 9,631 lines (not "20,871 → 9,632"); Straightening is 30/31 docstringed; say that the SimplexCube range 91–463 is off by one line at both ends (hash irreproducible) and that PrismOperator's hash is of the range minus the cut sub-block; record the non-`module` deviation of `CrossProduct.lean` in the report, not only in the commit.
6. **Commit the Stage-2 review.** `f42b9e6` cites a review file that exists only on the author's machine. Put it under `Lib/docs/` (or `Lib/reports/`) with the reviewer named.
7. Minor: open item 7 (`GenLoop`) resolves in the code's favour — the pinned Mathlib has root `GenLoop`, not `HomotopyGroup.GenLoop`; close it.

## The four packets (docs only) — verdicts

Per the protocol, a packet is `GO` only after (a) a Stage-2 review artifact, (b) an exact typed ledger with no ellipses or prose-for-types, (c) a compiled producer + consumer probe with a durable receipt, and (d) an independent Axis-5 review. None of the four has (c) or (d); none has (a) in the tree.

| Lane | Verdict | Missing |
|---|---|---|
| **E2** | **DRAFT** | Exact signatures (rows give names + prose hypotheses; the 3 immersion/embedding names are written without their `ManifoldImmersion.` namespace and do not resolve as written); probe + receipt; the review file (`E2-review.md`) in tree; open item 5 still says "review scheduled" although the corrections commit exists. Citation check: h-cobordism Thm 9.6 (disc theorem) correct; Hirsch Ch. 2/3/8 correct; "Milnor TDV §2 Lemma" for the disc theorem is not a real pointer (TDV §2 is Sard–Brown). The `2k+1 ≤ n` vs `2k ≤ n` question is well flagged — needs an owner answer. |
| **F** | **DRAFT** | **Two wrong Milnor numbers:** the Whitney lemma is *Theorem 6.6* (6.4 is the Second Cancellation Theorem); the Basis Theorem is *Theorem 7.6* (7.8 is the middle-dimension product-cobordism theorem). Hatcher Prop. 2.30 and Lemma 6.7 are right. Exact signatures (`primitive_row_has_unit_after_column_additions` has a `…` inside its statement; F7/F11 targets are prose; `MorseSurgeryData.beltIntersectionSign` and `RankThreeWhitneyModel.Space` lack their `…` namespaces); probe + receipt; review in tree; open item 6 stale ("scheduled"). F0a/F0b depend only on Mathlib and could land now — do that first. |
| **G** | **NOT GO** | No Stage-2 review at all; the ledger body ("verbatim signatures in `G-map.md` §1") is off-tree — only the headline row is in the packet; no receipt; `exists_two_critical_point_morse_of_homotopySixSphere` / `nonempty_homeomorph_of_homotopySixSphere` are written without their `MorseCancel.` namespace. Citations correct (Smale 1961 Theorem A; Milnor Thm 8.1). By design G waits on C and F, both unfinished. |
| **J** | **DRAFT** (closest to GO) | Headline current + target signatures are exact and match the tree; the Pontryagin and wedge rows use `H₁ G →ₗ[ℤ] Hₙ G` / `⋀[ℤ]^n` notation rather than Lean (note: `exteriorPower` is not an identifier in the pinned Mathlib; the notation `⋀[ℤ]^n M` is); probe + receipt; review in tree. Citations all correct (Ex. 2.48, Example 3.16, §3.C Exercise 11), and the flag that the task file's "Cor. 3.28" is the manifold-torsion corollary is right. The `(p,q)` vs `(1,n)` product question needs an owner answer. |

**Cross-packet items**

8. Each ledger row must carry an exact Lean signature (binders, instances, universes, result), the `ChallengeNode` fields, and namespaces that resolve at the current head — 8 "current" names across the four packets do not resolve as written (all exist under longer names).
9. Produce `Lib/docs/<lane>-INTERFACE_RECEIPT.md` from compiled `<lane>_InterfaceCheck.lean` / `_InterfaceConsumerCheck.lean` at 856e4762 before any Lean for E2, F, G, J. Lanes A, D1, D2 and now C are on the branch; the "after X lands" deferrals no longer apply.
10. Commit the four review files with reviewer identity; write G's.
11. Authorship: all 33 commits carry the repository owner as author. Add an author/co-author line if the contributions are to be attributable.

---

## For GLM (lane A follow-ups and E1)

- **Unblocked by C:** the cross-product cluster is in `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` (`PeriodTorusHigherHomology.crossProductEdge/Triangle/Homology`, boundary laws, naturality, the two local `ℤ`-module instances) and the augmentation is in `Lib/AlgebraicTopology/Hurewicz/PrismOperator.lean` (`SecondHurewicz.SimplyConnected.chainAugmentation*`) and `…/Hurewicz/lean` (`HigherHurewicz.chainAugmentation_boundary*`). **Lane I's Wang sequence is therefore unblocked**; `Hopf/LCP/{CuspFilling,IntegralHomology}.lean` can import `Lib.AlgebraicTopology.SingularHomology.CrossProduct`. The 42 cross-product swap/associator coherence declarations in `Hopf/LCP/Specialization.lean` are lane J's item G-J3 (to be appended to `CrossProduct.lean`).
- **Importable now:** `Lib.AlgebraicTopology.SingularHomology.CrossProduct`, `Lib.AlgebraicTopology.Hurewicz.{SimplexCube, HomotopyExtension, CubeTriangulation, PrismOperator, Subdivision, CubeGluing, Degree, CubeChainDecomposition, Straightening, CubeSphere}`, `Lib.Topology.Homotopy.CellFilling` (all registered in `Lib.lean`).
- **Still yours, unchanged by C:** fixes 1–5 of the lane-A review — provenance receipts for the 27 commits without SHA-256; the `SurgeryWindows.lean` scope decision (now urgent: Kimi's E2 plans a Lib-internal split of it); the 10 unregistered `Lib.lean` imports (still 0/10); the `SpecialPeriods.*` name and 20 stale docstring names in `Lib/`; the 78 `dupNamespace` warnings. Lane B's `simplyConnectedSpace_of_open_cover` is still at `Hopf/Hurewicz.lean:186`.
- **E1:** the web is landed (D2); C did not touch E1. The three E1 probe theorems (`MorseCancel.cancel_of_transverse_level_isotopy`, `MorseRearrangement.exists_morse_rearrangement_of_no_connection`, `MorseCancel.exists_excellent_indexed_morse_birth`) remain in `Hopf/`; E1 is blocked only on committing the `Cubic`/`TimeChange`/`LevelCylinder` drafts to the fork.
- **What C leaves in `Hopf/Hurewicz.lean`:** 9,631 lines / 948 declarations — `ThirdHurewicz.*` 633, `FourthHurewicz.*` 150, `FifthHurewicz.*` 135, `DiskCube.*` 12, `SphereHomology.*` 7, root lane-B theorems 4, `SixSphereCube.*` 3, `Sphere.pi*_subsingleton` 4; plus `SixthHurewicz.*` 140 in `Hopf/Recognition.lean`. All of it is the C10 deletion set.
