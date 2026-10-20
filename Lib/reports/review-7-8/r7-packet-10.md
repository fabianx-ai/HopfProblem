# Review of Lib/reports/round-7/packets/RECEIPT-10.md

**Verdict: ACCEPT WITH FINDINGS** — every count, every generalisation and the forcing claim check
out against the history and one probe elaboration; the findings are one mis-attributed auxiliary
constant, one non-forced pin miscounted as forced, one module docstring stating a weaker
hypothesis than the theorems carry, and cosmetic damage in four declarations.

## Findings

1. `[wrong receipt]` **The "one extra constant" is not the auxiliary of `sheafification`.**
   Receipt §envdiff: "the one extra constant is the auxiliary of the new `universe`-generalised
   `sheafification` definition". The packet's own `envdiff.json` was not committed (unlike the
   round-8 branches), so I used `Lib/reports/round-7/envdiff-merged-d950428a.json` restricted to
   the three modules packet 10 changed types in (`SingularCochainSheaf.Sheaf`, `.LocalKernels`,
   `StalkwiseSectionRange`): lost-only = ∅, added-only =
   `TopCat.SingularCochainSheaf.unit._proof_1`, 20 names with changed hash on both sides —
   among them `TopCat.SingularCochainSheaf.sheafification._proof_1`, which therefore existed
   *before* the packet. The +1 is a new proof auxiliary of `unit` (`toSheafify … (presheaf X A n)`,
   whose target now elaborates through the `.{u}` `sheafification`), a consequence of the
   generalisation but a different declaration than the receipt names. The receipt should name it;
   the packet-level `envdiff.json` should be committed next to the receipt.

2. `[wrong receipt]` **PrimitivesH1.lean "14 left: forced" — one of the 14 is not downstream of
   the chokepoint.** `PrimitivesH1.lean:162` (branch tip) `variable {K L : CochainComplex
   AddCommGrpCat.{0} ℕ} {f g : K ⟶ L}` scopes the two private lemmas `homotopy_apply_closed_one`
   and `homotopy_apply_closed_zero`, which are statements about an arbitrary `Homotopy f g`
   between maps of cochain complexes in `AddCommGrpCat` and mention no singular chains. Nothing
   in `SingularCochains.chains/complex` forces this `.{0}`; it could be `.{u}` (they are only
   *used* at `.{0}`). The remaining 13 (`Cochains`, `cochainHom`, …, `nullhomotopic_pullback_closed_*`)
   all take `(X : Type)` or `complex X A` and are forced. Still 14 at head `39f1d12b`.

3. `[docstring]` **Vanishing.lean module docstring states a weaker hypothesis than the theorems
   have.** New text (`Vanishing.lean:14`): "On a locally contractible *paracompact* space the
   comparison isomorphism … turns vanishing of singular cohomology into vanishing of constant-sheaf
   cohomology. In particular constant-sheaf cohomology of a contractible space vanishes in every
   positive degree." Both theorems in the file
   (`constantSheafCohomology_subsingleton_iff_singular`,
   `constantSheafCohomology_succ_subsingleton_of_contractible`) require `[MetrizableSpace X]`
   (and `hLC`), not paracompactness; the declaration-level docstrings say "metrizable" correctly.
   `ResolutionPositive.lean`'s module docstring handles the same point honestly ("on a
   paracompact space (here a metrizable one)"); Vanishing's should say the same.

4. `[docstring]` **Non-standard gloss of "hereditarily paracompact".** `OpenRestriction.lean`
   module docstring: "the sheaf `𝒮^n(·; A)` is flabby on a hereditarily paracompact space", and
   `isFlasque_of_open_normal_paracompact`: "On a hereditarily paracompact space — one all of whose
   open subspaces are normal and paracompact". The hypotheses are `[∀ V : Opens X, NormalSpace V]
   [∀ V : Opens X, ParacompactSpace V]` with no `T2Space`; "hereditarily paracompact" in the
   literature means every subspace is paracompact and, without Hausdorff, does not give normality.
   The declaration docstring's dash-clause makes the meaning explicit, so this is a wording issue;
   the module line should say "on a space all of whose open subspaces are normal and paracompact
   (e.g. metrizable)".

5. `[nit]` **Stray blank line inserted inside four declaration signatures** by the docstring
   edits: `GlobalUnit.lean` `theorem globalCochainComparison_f (n : ℕ) :` + blank line;
   `GlobalUnitPositive.lean` `theorem globalCochainComparison_homology_isIso_succ` + blank line
   before `[NormalSpace X]`; `Presheaf.lean` `theorem complex_d … :` + blank line;
   `Pullback/Sheaf.lean` `theorem cochainPullbackComplex_f (n : ℕ) :` + blank line. Compiles,
   but it is visibly an editing accident and all four persist at head `39f1d12b`
   (`GlobalUnit.lean:75-76`, `GlobalUnitPositive.lean:138-139`, `Presheaf.lean:96-97`,
   `Pullback/Sheaf.lean:100-101`).

6. `[nit]` **Internal inconsistencies in the receipt/commit messages.** (a) "Three declarations
   in the packet are *not* downstream of it and were generalised" vs. the totals line "6
   declarations generalised in universe" — three *sites* (Sheaf.lean, LocalKernels.lean,
   StalkwiseSectionRange.lean), six declarations. (b) Commit `ab98de39` says "drop project
   vocabulary from 9 docstrings" for PrimitivesH1.lean; the receipt table says `~11`; the diff has
   11 restated docstrings (Cochains, simplexChain, cochainValue, cochain_ext, pullback_simplex,
   constantCochain_injective, homotopy_apply_closed_one, pullback_closed, cocycle_one_point_zero,
   nullhomotopic_pullback_closed_zero/one). The receipt is right, the commit message is not.
   (c) Totals say "87 docstrings restated"; the diff has 86 `-/-- ` first lines plus one docstring
   changed only on its second line (`unit_app_surjective`), so 87 is right but not reproducible
   from a one-line grep.

7. `[citation]` **Two references I could not confirm; one probably points at the wrong chapter.**
   "Iversen, *Cohomology of Sheaves* II.1" is cited (LocalKernels, StalkwiseSectionLift/Range) for
   "exactness of sheaves is a stalkwise condition"; as far as I recall, Iversen's stalk/exactness
   material is in Chapter I (sheaves), Chapter II being cohomology — not verified, flagging only.
   The Bredon numbers "III Prop. 1.1" (surjectivity of `S^n(X) → Γ(𝒮^n)` for paracompact `X`) and
   "III Thm. 1.1" (the comparison is a quasi-isomorphism on paracompact HLC spaces) are used for
   two different results in different files (GlobalSections vs GlobalUnitH1/Positive/Vanishing);
   at most one of them can be numbered 1.1. Section III.1 is the right place for all of it; the
   item numbers were not checked against the book. Warner 5.31/5.32 are the right neighbourhood
   (singular cochain sheaves in Ch. 5) but Warner's flavour is *fine* sheaves, and
   `resolution_isAcyclic` cites "Warner 5.32" for "each `𝒮^n` is *flasque*" — the flasque
   argument is Bredon's, not Warner's.

## Claims checked

| claim | status | how |
|---|---|---|
| 25 commits, one per file, 24 files + receipt | verified | `git log 9552305f..1f18fae9^2`; every commit touches exactly one file (`git show --stat` loop) |
| Commit trailers on every commit | verified | loop over 25 commits: 2 trailer lines each |
| Commit messages describe the commit | partly | spot-checked 6; `ab98de39` says 9 docstrings, diff has 11 (finding 6b) |
| "19 docstrings added" | verified | 105 `+/-- ` minus 86 `-/-- ` = 19; listed per file: GlobalSections 1, GlobalUnit 1, Presheaf 4, Sheaf 2, Pullback/Presheaf 4, Pullback/Sheaf 2, Pullback/Global 2, FiniteClosedPositive 1, ResolutionPositive 2 — matches the table's `+k` column exactly |
| "87 restated" | verified | 86 first-line changes + `unit_app_surjective` second-line change |
| 24 module docstrings rewritten with a textbook reference | verified | every one of the 24 files has a `/-!` hunk in the diff citing Bredon/Warner/Godement/Hatcher/Hartshorne/Iversen; negated/seat sentences ("This FREE owner", "no quasi-isomorphism claim is made", "No exactness in degree two is used or asserted", H1-pipeline residue) are gone |
| Per-file "pins left" counts (20, 19=25−6, 0, 14, 2, 2, 8, 2, 2, 2, 3, 2, 3, 3, 7, 7, 6, 8, 3, 4, 13, 3, 0, 0) | verified | `grep -o '\.{0}' \| wc -l` per file at base / tip / head: 147 → 133 → 127 (head: three files deleted by round-8 `0d8e2b19`, LocalExactPositive absorbed LocalExactH1 → 3) |
| 6 declarations generalised; statement at `u = 0` unchanged; no hypothesis added | verified | read all three hunks in the diff: only `.{0}`→`.{u}` and explicit `AddCommGrpCat.{u}` where the elaborator previously defaulted; `#check` at head shows the `.{u}` signatures; `#print axioms` on `sheafify_exact_of_local_kernels` and `app_exists_preimage_iff_stalkwise_exists_preimage`: `[propext, Classical.choice, Quot.sound]` |
| The two LocalKernels helpers are `private` | verified | `private theorem presheaf_stalk_exact_of_local_kernels`, `private def sheafificationStalkIso` at tip |
| "Every remaining pin is forced by `SingularCochains.complex (X : Type) (A : AddCommGrpCat.{0})`" | partly | At base `9552305f` `chains (X : Type)`, `complex (X : Type) (A : AddCommGrpCat.{0})` — true for the `X`-side of every pin and the `A`-side at that time. Packet 01 (`c31bbc73`, merged after packet 10) lifted `complex`'s coefficient to `AddCommGrpCat.{w}`, so at the merged state the `A`-pins are no longer forced *by `complex`*. Probe (`r7-packet-10/Probe.lean`, one elaboration): `presheafToSheaf (Opens.grothendieckTopology (TopCat.of Unit)) AddCommGrpCat.{1}` fails with `failed to synthesize HasWeakSheafify …` while `.{0}` succeeds — so for every file that sheafifies, `A : AddCommGrpCat.{0}` *is* still forced by `X : Type` through Mathlib's sheafification universe constraint. Only the presheaf-level `A`-pins (Presheaf.lean `cochainFunctor`/`presheaf`, PrimitivesH1) are now liftable in isolation, to no practical benefit. One pin is not forced at all (finding 2). |
| Consistency with round-8 pins receipt §3 | verified | §3 attributes the obstruction to `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ` / `X : Type` (`ULift ℤ` rewrite breaks four consumer proofs), i.e. exactly the `chains` side packet 10 names; §3's "271 remaining pins stay for exactly this reason" silently includes the `A`-side, which is forced only indirectly (via sheafification, see above) — packet 10's list is consistent with §3; §3 is slightly over-broad, not packet 10's problem |
| `{X Y : Type}` binders in PrimitivesH1 forced | verified | `chains (X : Type)` at base and at head (`SingularCochains.lean:116`) |
| StalkwiseSectionLift: "already `X : TopCat.{v}`; audit's ×1 is `{C : Type u}`" | verified | tip lines 36-40: `universe v u`, `{C : Type u} [Category.{v} C]`, `{X : TopCat.{v}}`; audit log confirms "fully generic … universe-polymorphic"; 0 `.{0}` in the file |
| envdiff "0 source lost, 0 added, 6 changed types = the six generalisations" | partly | packet-level `envdiff.json` not in the repo; merged `envdiff-merged-d950428a.json` restricted to the three modules: lost-only ∅, added-only `unit._proof_1`, 20 changed-hash pairs incl. all six named declarations (finding 1) |
| No deletion, no rename | verified | diff contains no removed `theorem/def/abbrev/instance` line; `git grep` at tip finds every "Main results" name listed in the 24 module docstrings |
| Hygiene: no `sorry`/`axiom`/`maxHeartbeats`/`unsafe`/`native_decide`/`@[simp]`/`noncomputable`/`private` changes | verified | grep over `+`/`-` lines of the branch diff: no hits (existing `set_option maxHeartbeats` lines are context only) |
| `Lib` never imports `Hopf` | verified | `git grep 'import Hopf' 39f1d12b -- Lib/` hits only `.md`/log files |
| Builds green | not re-run | trusted; the built copy at head elaborates the probe |

Docstrings read against their statements (all 105 in the diff were read; explicitly checked: 
`globalCochainUnit_surjective`, `globalCochainComparison_cycle_lift_one`,
`globalCochainComparison_boundary_detect_one`, `…_homology_isIso_one_of_small_chains`,
`globalCochainComparison_homology_isIso_succ`, `sheafify_exact_of_local_kernels`,
`initialComplex_exact`, `complexSheaf_exactAt_one/succ`, `presheaf_map_surjective`,
`isFlasque_of_open_normal_paracompact`, `isFlasque_of_metrizable`, `resolution_isAcyclic`,
`resolutionH1` (checked `AcyclicResolutionH1` fields: exact at `F`, `X₁`, `X₂` only — the docstring's
"`0 → A_X → 𝒮^0 → 𝒮^1 → 𝒮^2` is exact" is the right reading), `constantSheafCohomology_*` (2),
`app_exists_preimage_iff_stalkwise_exists_preimage`, `exists_preimage_of_stalkwise_mem_range`,
`nullhomotopic_pullback_closed_zero/one`, `constantCochain_injective`, `cochainPullback_augmentation`,
`constant_sheafifyPullback`, `globalCochainComparison_naturality`, `preimageMap_inclusion`,
`constantSheafGlobalH1Iso`). Only findings 3–4 arose. Citations checked from memory: Godement
II.4.7 (Théorème 4.7.1, de Rham–Weil) and Bredon II.4.1 (acyclic resolutions compute `H^n`) are
right; Hatcher Thm. 2.10 (homotopic maps, chain homotopy) and Prop. 2.21 (small chains inclusion
is a chain-homotopy equivalence) are right; Hartshorne II Ex. 1.2 (exactness on stalks) is right;
Bredon III.1 as a *section* is right for every use; item numbers and Iversen/Warner see finding 7.

## Not checked

* The packet's own `envdiff.json` (base dump vs after dump): never committed; I reconstructed
  from the merged stage-2 diff, which cannot distinguish packet 10's `_proof_*` churn from other
  packets' in shared modules (there are none in these three modules, so the reconstruction is
  reliable for the changed-type and added constants, less so for the "20 lost / 21 added" totals).
* Builds (`lake build Lib`, `Solution…`, `AxiomAudit`) not re-run (forbidden); relied on the built
  head and one probe file (1 elaboration).
* Whether the presheaf-level `A`-pins (Presheaf.lean, PrimitivesH1, Pullback/Presheaf) elaborate at
  `AddCommGrpCat.{w}` after packet 01's lift: my ad-hoc presheaf example in the probe hit the
  200000-heartbeat limit in `isDefEq` and proves nothing either way; not pursued (no value
  without the sheaf level).
* Exact item numbers in Bredon III.1, Warner 5.31/5.32, Iversen II.1 (no copies at hand).

## Tool notes

* Commit the per-packet `envdiff.json`/`.txt` beside the receipt (round 8 did); a receipt that
  quotes only the summary line lets an attribution like finding 1 slip through unverifiably.
* A receipt that says "forced by X" should distinguish *which binder* is forced by what; here the
  `X : Type` and `A : AddCommGrpCat.{0}` pins have different forcing chains and a sibling packet
  changed one of them in the same round. The coordinator's INTEGRATION-7 does not note the
  cross-packet effect of `c31bbc73` on packets 10 (and 09/others with `SingularCochainSheaf` pins).
* The `## Main results` lists are useful — `git grep` of every listed name at the tip was a
  one-liner and caught nothing wrong; keep doing it.
* Docstring-only edits that change the token stream inside a signature (finding 5) would be
  caught by a `git diff --ignore-blank-lines` vs plain diff comparison in the receipt tooling.
