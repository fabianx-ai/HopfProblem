# Review of Lib/reports/round-7/packets/RECEIPT-05.md

**Verdict: ACCEPT WITH FINDINGS** — the receipt's structural claims (docstrings only, 385 added,
counts per file, 0 pins, 0 `Type` binders, 0 statements changed, envdiff clean, trailers present)
all verify by direct comparison; one added docstring states the opposite of what the definition
does (`WhitneyPairModel.cornerScale`) and a handful of others are loose, and one textbook section
reference is doubtful.

## Findings

1. `[docstring]` **`WhitneyPairModel.cornerScale` docstring inverts the geometry.**
   `Lib/Geometry/Manifold/Whitney/BigonModel.lean:410` (commit 1ced9927).
   Docstring: "The interpolated distance to the **nearer** corner, `(1 - β t) (1 - t) + β t · t`
   for the transition `β`; it equals `1 - t` near the left corner and `t` near the right one."
   Definition: `cornerScale t = (1 - cornerTransition t) * (1 - t) + cornerTransition t * t`, with
   `cornerTransition t = 0` for `t ≤ 1/3`. Near the left corner (`t ≈ 0`) this is `1 - t ≈ 1`, the
   distance to the *right* corner, and near the right corner it is `t ≈ 1`, the distance to the
   *left* corner. The second half of the sentence is right and the first half contradicts it; the
   quantity is the distance to the opposite (far) corner — it is exactly the factor `1 − arcTime`
   that `leftCornerCoordinates` divides by, which must stay away from `0` at the left corner.
   Fix: "distance to the opposite corner".

2. `[docstring]` **`CleanBigonBoundary` (and the CleanStrips module docstring) overstate the
   cleanliness clause.** `CleanStrips.lean:2744` and module docstring bullet 5 (commit f88440bf).
   Docstring: "… meeting the sheets `S` and `T` only along those edges"; module docstring: "an
   embedded neighbourhood of the boundary of the Whitney bigon which meets the two sheets exactly
   in the two edges of the bigon." The structure's fields only constrain the *bigon side*:
   `interior_avoids : ∀ p ∈ domain ∩ interior (bigon h), map p ∉ S ∪ T` and
   `clean : ∀ p ∈ bigon h ∩ closed_neighborhood, p ∉ frontier (bigon h) → map p ∉ S ∪ T`. Nothing is
   asserted about the part of the neighbourhood outside the bigon, so "the neighbourhood meets the
   sheets exactly in the edges" is not what is proved. (`bigon_boundary_map_avoids_sheets` at
   l.2722 words it correctly: "the bigon meets the two sheets only in its two edges".)

3. `[citation]` **Milnor, *Topology from the differentiable viewpoint*, §7 for `π_m(Sⁿ) = 0`,
   `m < n`.** `AnnularExtension.lean` module docstring and commit message 7c7a8d0f. §7 of that
   book is "Framed cobordism; the Pontryagin construction". The result the file proves
   (`sphereMap_nullhomotopic_of_dim_lt`: smooth representative, not surjective by Sard, complement
   of a point contractible) is the argument of §§2–3 (Sard–Brown) plus §1; §7 only recovers the
   fact indirectly through framed cobordism of the empty manifold. I am not certain Milnor does
   not remark on it in §7, but §2 is the right pointer for the proof actually formalised. Hatcher
   §4.1 (Cor. 4.9, cellular approximation) is correct.

4. `[docstring]` `[nit]` **Hypotheses omitted in "germ realisation" docstrings.**
   `Transversality/Basic.lean:1808` `SupportedGerms.realizes_det_one` and `:2206`
   `SupportedGerms.realizes_local_germ` (commit f2f0ea5a) both carry `[Finite ι] [Nontrivial ι]
   (b : Module.Basis ι ℝ E)`, i.e. `dim E ≥ 2`; the docstrings ("The germ of a linear automorphism
   of determinant one of a finite-dimensional space is realised …", "A germ at the origin of a
   smooth map … of determinant one is realised by a diffeomorphism supported in any prescribed
   neighbourhood") do not say so. The restriction is an artifact of the proof (path-connectedness
   of `SL(n, ℝ)` via transvections needs two coordinates), not of the mathematics, but a reader
   of the docstring will try to apply the lemma to `E = ℝ` and fail on instance search; the
   docstring should say "of dimension at least two". The module-docstring bullet for
   `realizes_local_germ` has the same omission.

5. `[docstring]` `[nit]` **`CleanStripPatch` docstring drops the reversal.** `CleanStrips.lean:2055`.
   "agrees near its two ends with the given corner patches `k₀` and `k₁`", but the field is
   `right_germ : map =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse`. Also "meets the sheet `T`
   exactly in the two ends" means the two vertical lines `t = 0` and `t = 1`
   (`second_sheet : map p ∈ T ↔ p.1 = 0 ∨ p.1 = 1`), not two points.

6. `[docstring]` `[nit]` **`DiskShrinking.exists_chart_disk_shrinking`** (`Basic.lean:2954`):
   "supported near the image of the disc" — the statement gives only `K ⊆ Φ.target`, compact;
   the support is inside the chart, not necessarily near the disc.

7. `[docstring]` `[nit]` **AnnularExtension module docstring.** Bullet 4 says "every continuous map
   from a compact `m`-dimensional manifold … into `Sⁿ` with `m < n` is nullhomotopic"; the theorem
   also needs `[I.Boundaryless]` (the declaration docstring says "compact boundaryless manifold",
   correctly). Bullet 2 says the annular extension needs the two boundary restrictions to be
   "nullhomotopic"; the theorem `exists_continuous_annular_extension` literally asks for
   extensions `F₀ F₁` over the closed unit ball (equivalent via `SphereCone.extension`, but that
   step is the reader's to make).

8. `[incomplete]` `[nit]` **No envdiff artifact for the packet is in the repo.** The receipt quotes
   the `envdiff.py` summary but no `envdiff.json`/`.txt` sits beside `RECEIPT-05.md` (none of the
   ten packet receipts has one; only `Lib/reports/round-7/envdiff-merged-d950428a.*`). The
   receipt's honesty caveat (base dump may have read post-edit `.olean`s) therefore cannot be
   checked against the raw dump; I verified the claim by other means (see below).

Nothing `[unsound]` or `[wrong receipt]`: every numeric and "did X" claim in the receipt checked
out.

## Claims checked

| claim | status | how |
|---|---|---|
| Branch = 5 commits (4 file commits + receipt), 4 Lean files, one commit per file | verified | `git log 9552305f..0564b35f^2`; `git diff --stat 9552305f 0564b35f^2` (4 `.lean` + receipt) |
| "No statement was changed anywhere" / "only docstrings were edited" | verified | Stripped every `/- … -/` block, `--` comment and blank line from base and branch versions of all four files with a small script; the residues are **byte-identical** for all four files |
| Docstrings added: 52 (0→52), 60 (0→60), 140 (0→140), 133 (2→135) | verified | `/--` counts base vs branch: BigonModel 0→52, AnnularExtension 0→60, CleanStrips 0→140, Basic 2→135 |
| "387 / 387 declarations documented" | verified | regex count of top-level `def/theorem/lemma/structure/abbrev/instance/…` = 52, 60, 140, 135 = docstring counts; no `instance`s in these files |
| The two pre-existing docstrings in Basic unchanged | verified | branch diff for Basic.lean contains no `-` lines inside `Diffeomorph.toPartialDiffeomorph'` / `IsLocalDiffeomorph.diffeomorph'` |
| BigonModel module docstring "already complete", not touched | verified | branch diff for BigonModel.lean has no `-` lines at all; module docstring cites Milnor §6 Thm 6.6 (correct: Thm 6.6 is the Whitney lemma) |
| AnnularExtension / CleanStrips old module docstrings were move receipts naming `Hopf/SingularHomology.lean`, integration-4, "families", "file order is the dependency order" | verified | `git show 9552305f:<file>` head; all such sentences gone at branch |
| Basic old module docstring promised `NativeTransversality.Patch`, `WeightedPerturbation`, `GeneralPosition`, `NoExotic`, none declared | verified | `git show 9552305f:…Basic.lean` outline; `grep` for those names in the file: none |
| Every backticked name in the three new module docstrings is declared in its file | verified | script: all names resolve (only `E`, `f`, `m`, `v`, `a` unmatched, which are variables) |
| 0 universe pins, 0 `: Type` binders in the packet | verified | `grep -nE 'Type\b[^*]|\.\{0\}|universe' ` on the four files: only `Type*` binders |
| envdiff "0 lost, 0 added, 0 changed type" | verified indirectly | no packet-level artifact (finding 8); the merged `envdiff-merged-d950428a.json` (all ten packets) has **no** entry in `lost`/`added`/`changed_type_all`/`moves` whose name lies in any of the four modules or their namespaces; and the stripped-source identity above makes any environment change impossible |
| Hygiene: no `sorry`/`axiom`/`maxHeartbeats`/`unsafe`/`native_decide`/`@[simp]`/`noncomputable`/`private` changes, no `import Hopf` | verified | grep of the branch diff for those tokens on `+`/`-` lines: empty; `grep -rn "import Hopf" Lib/` at head: empty |
| Commit trailers `Co-Authored-By` / `Claude-Session` on all 5 commits; messages describe the commits | verified | `git show -s --format=%B` for each |
| Docstring accuracy (sample) | 1 wrong, ~7 loose, rest correct | Read **all 135** docstring/declaration pairs of `Transversality/Basic.lean`, **all 60** of `AnnularExtension.lean`, **all 52** of `BigonModel.lean`, and **all 140** headers of `CleanStrips.lean` (statement bodies read for ~35 of those); unfolded the definitions behind every BigonModel docstring (`bigon`, `arcTime`, `leftCornerCoordinates`, `cornerTransition/Scale/Sign`, `exchangeEdges`, `lower/upperStripCoordinates`, sheets) and checked the corner/strip identities by hand (`leftCornerCoordinates_exchange`, `lowerStripCoordinates_left/right`, derivatives) |
| Dimension/codimension claims in transversality statements | verified | `exists_embedded_disk_isotopy_of_same_center`: `0 < n`, `finrank D + n = finrank E`, `2 ≤ finrank E`, `CompactSpace M`, same centre — matches "positive codimension, dimension ≥ 2, compact"; `dense_native_translations` / `exists_null_exceptional_native_translations`: `finrank D + finrank Z = finrank F`, Lindelöf `X × Y`, boundaryless — matches; `finite_transverse_intersections`: compact `N`, `P`, `M`, injective smooth `F`, `G`, complementary dimension, transverse at every coincidence — matches; `isOpen_surjective_nativeDerivative` / Sard statements: `finrank E = finrank F` — matches "equal dimension" |
| Citations: Hirsch Thm 8.3.1 (disc theorem), Hirsch Ch. 3 (parametric transversality), G–P §1.5/§2.3 (transversality, finiteness), Hatcher §4.1, Milnor h-cob §§5–6 / §6 Thm 6.6 / §3 (belt-sphere neighbourhood) | verified from memory except one | Hirsch 8.3.1 is the disk theorem (Palais/Cerf); Hirsch Ch. 3 = Transversality (parametric transversality Thm 3.2.7); G–P §1.5 and §2.3 are the two transversality sections (the two-map relation `f ⋔ g` is in the exercises); Hatcher Cor. 4.9; Milnor §6 Thm 6.6 = Whitney lemma, §3 = elementary cobordisms/belt spheres. Milnor TDV §7: doubtful (finding 3) |

## Not checked

* No Lean elaboration was run: the stripped-source identity makes the environment provably
  unchanged, so a build would add nothing; the receipt's build/axiom-audit logs are taken as
  reported.
* The receipt's caveat that the base dump may have read post-edit `.olean`s cannot be tested
  (no dump files in the repo); it is moot given the identity above.
* For ~105 of the 140 CleanStrips declarations whose statements run past my extraction window
  (long `letI`/`∃` conclusions) I checked the docstring against the header, hypotheses and the
  first lines of the conclusion only.
* Later branches touched two of the files (`r8/dfiles-a`: `TubularBigon` lost its default
  `n := 4` and its docstring gained a sentence; `r8/dfiles-a` added
  `ContinuousLinearMap.surjective_coprod_comp_left` to `Transversality/Basic.lean`); those changes
  belong to the round-8 receipts and were not reviewed here.

## Tool notes

* The packet receipts should commit the `envdiff.json`/`.txt` they quote (the round-8 branches
  do). For a docstring-only packet a cheaper and stronger check than envdiff is the one used
  here: strip comments and diff — one line in the receipt ("comment-stripped sources identical,
  sha256 …") would have made items 3–4 of the work list verifiable in seconds.
* Docstrings were clearly written from the statement headers; the one real error (finding 1) is
  in a docstring that paraphrases a formula it also quotes correctly. A rule "quote the formula,
  do not gloss it" or a second pass that re-reads each gloss against the unfolded definition
  would catch this class.
* A pairs dump (docstring + declaration header) per file, generated by the packet agent and
  committed alongside the receipt, would let reviewers sample without re-extracting.
