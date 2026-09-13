# Fresh independent G review after repairs

Reviewer identity: **fresh2-g**, a new Devin subagent, not a prior G reviewer.
Scope: current `/home/ox-alpha/HopfProblem/Lib/docs/G.md`, receipt, live signatures and load-bearing proof mechanisms. Review/report only.

## Snapshot and separate verdicts

Repository branch: `lib/textbook-extraction`.
Beginning and ending HEAD: `fdd2143ee7d33a8aec945a48c4c95c4503c3e38e`.
Beginning and ending status: only `?? AGENTS.md`; tracked-clean, not literally clean.
No concurrent change to the reviewed ledger, receipt or primary source files was observed; their beginning/end SHA-256 values agree below. `git diff --check` passed, and the scoped diff against the initial HEAD was empty.

1. **Scoped Stage-2 mathematical GO for the repaired §§3–5 argument and its recognition conclusion**, relative to the named Morse existence/rearrangement/cancellation, general-position, Whitney and Reeb inputs. The comparison class, (0,1) reduction, trade cut, complement argument and 2→4→3 elimination now agree with the live proof mechanisms. I found no new false mathematical implication in those repairs. This is not a new proof or exhaustive audit of the entire transitive geometric library, nor unconditional certification that the document satisfies every textbook-presentation requirement.
2. **GO for the specific G2a→G3→G2b coarse dependency/placement repair.** This does not certify helper closure.
3. **NO-GO for the exact ledger as currently advertised.** Names and declaration-start coordinates of all 35 rows now agree with live source, but **two G5 signatures are truncated inside their result types**. Only 33 of the 35 displayed signatures are complete textual source signatures. This is a concrete defect beyond the expressly deferred Axis-5 work.
4. **Axis-5 NOT GO / Axis-6 NOT READY.** In addition to those truncations, helper closure, exact production contexts, green boundaries and aggregate provider/consumer certification remain open. The legacy compiled artifacts still expose old namespaces. These facts do not refute the Stage-2 mathematics.

## Method and independence

Read `/home/ox-alpha/collaboration-protocol.md` first, then AGENTS.md, lean-protocol.md (including Stage 2, Axis-5 Challenge/GO and extraction-mode rules), all 1,194 lines of current G.md and its 82-line receipt. Inspected all 35 declaration starts and their source signatures, and read the load-bearing proof bodies and complement/minimum/trade helpers before consulting the prior reviews. The dangling `let p' :=` signatures were identified directly in the current ledger/source comparison, not inherited from a checklist. Subsequently read G-fresh-subagent-review.md, both astra reviews and the superseded self-review to check repair coverage. No previous verdict was adopted as evidence in place of source inspection.

Comparison is a manual source-text review, not machine equality of elaborated types. Selected long proof bodies were followed at their substantive calls; not every transitive helper was audited line by line. I did not fetch the books afresh or claim new page-by-page verification of Milnor/Smale. The cited theorems are treated at the stated standard-input scope; the closed-manifold trade is justified through the actual unique-minimum/source chain, not by silently applying a triad theorem verbatim.

## Numbered actionable findings

### 1. High — exact-ledger defect: two result types end at an internal definition, not the theorem's proof delimiter

**Locations:** `Lib/docs/G.md:819–868` and `870–910`; contrary claims at `G.md:10–11,356–360,816`.

- `AdaptedWindows.exists_primitive_functional_unit` stops at `let p' : Fin n → ... :=` on G.md:868. This is the internal let at **Hopf/Recognition.lean:6007**, not the theorem's outer `:= by` at **6074**. Missing source lines **6008–6074** contain the definition of p', transported basis B', index/completeness/lower-cut properties, the new family Γ, matrix multiplication by transvections, surjectivity, the actual ±1 unit conclusion, and preserved flow-limit/orbit data. In particular the ledger drops the very unit its prose promises.
- `AdaptedWindows.exists_first_middle_pivot` similarly stops at G.md:910, corresponding to **Recognition:2480**. Its source signature continues through **2493**, with p', B', γ', middle-family data, equality of underlying points, matrix equality and surjectivity. These are needed to preserve the unit/family into cancellation.

The source has complete signatures and real proofs. The missing text is in the ledger, not Lean source. The present snippets are not even closed proposition expressions, so no namespace adjustment or stale-artifact explanation repairs them.

**Action:** restore Recognition:6008–6074 and 2481–2493 into their respective rows, preserving all dependent lets and conjunctions. If extraction tooling was used, distinguish a top-level theorem proof delimiter from `:=` inside a result. Recheck all rows after repair and revise the blanket “nothing ... compressed” claim until that comparison is complete. A later receipt must certify the repaired hash, not this one.

### 2. Medium — receipt's final certification language conflicts with its honest DRAFT opening and the current ledger

**Locations:** `Lib/docs/G-INTERFACE_RECEIPT.md:3–7,11–13,30–36,78–82`; `Lib/docs/G.md:356–360`.

The opening now correctly says the checks were historical at 1cc1784, pre-rename, and DRAFT. But the final verdict still says “Ledger surface certified (names + coordinates + design mutations verified)”, while line 36 says all signatures were re-extracted verbatim. Finding 1 invalidates the full-signature claim. The historical 36 checks cannot certify this current 35-distinct-declaration ledger or a production import boundary.

**Action:** distinguish (a) current source name/start census, which passes, (b) completeness of displayed types, which presently fails, and (c) historical artifact name checks. Keep the receipt explicitly historical/DRAFT throughout. Only certify the repaired ledger hash after source-matched, appropriately scoped elaboration and importing-consumer checks. No need to call deferred certification a false mathematical step.

### 3. High for validation, not a source-math finding — source/artifact mismatch persists

**Evidence:** fresh probe below, compared to `Hopf/SphereTopology.lean:9796` and `Hopf/Recognition.lean:8020–8025`.

A probe importing **only Hopf.Recognition** cannot resolve current `Mathoverflow1973.MorseCancellation.exists_one_to_three_handle_trade` or `Mathoverflow1973.homeomorphic_sixSphere_of_homotopySixSphere`; it does resolve the obsolete `MorseCancel` and `Smale` counterparts. This independently reproduces the earlier artifact warning. The current sources visibly define the new names. Unknown-identifier diagnostics here are not evidence of missing current source theorems.

**Action for integration/build owner:** obtain a source-matched green artifact/dependency baseline during an authorized build window, then rerun focused interfaces. Do not revert the repaired names to appease stale oleans. No build or artifact refresh was attempted in this review.

### 4. Medium, acknowledged Axis-4/5 obligations — no certified runnable packet yet

**Locations:** `Lib/docs/G.md:13,339–341,813–814,1144–1163,1169–1187`; receipt:38–76; `lean-protocol.md:325–425`.

The namespace and Type/Type* notes are meaningful source context, but do not supply every node's exact imports, open scopes, public visibility, helper inputs, coherence expressions, consumer and green commit boundary. The designed consolidated headline is still described as a mutation rather than furnished as a complete production Challenge. The needed closure includes the (0,1) helpers, ordered-cut/birth-retention helpers, primitive collapse coordinate, equal-cut coherence, recovery of excellence after cancellation and middle-count equality.

**Action:** after repairing the actual ledger defect, keep G DRAFT while the owning pass closes those dependencies and per-boundary contexts. Perform aggregate production provider and separate importing-consumer checks as required for the designed surface, with hashes/commands/counts recorded. Respect the protocol's extraction-mode alternative for truly unchanged moves; it does not erase certification of designed statement changes. Do not invent a second G2/G3 cycle: the particular grouping defect has been fixed.

### 5. Low, presentation only — advertised ordinary-mathematics text still embeds Lean implementation identifiers

**Locations:** `Lib/docs/G.md:30,88–125,153–167,193–256`.

Line 30 advertises ordinary mathematics with no Lean names, but the narrative intentionally interleaves names, coordinates and `Nat.find` references. These annotations are useful for this review; their existence is not a false implication or an Axis-5 mathematical blocker.

**Action:** when freezing a pure canonical textbook artifact, move implementation annotations to a parallel correspondence layer, or accurately label this document as annotated recovered mathematics. Do not discard the repaired mathematical explanations while doing so.

## All 35 ledger declarations: current census

Every name below has outer prefix **Mathoverflow1973.**. `MC` means MorseCancellation, `AW` AdaptedWindows, `MM` ManifoldMorse, `SW` ManifoldMorse.SurgeryWindows. SH/ST/Rec are Hopf/SingularHomology.lean, Hopf/SphereTopology.lean, Hopf/Recognition.lean. “Complete” means the displayed signature matches the source text through the actual proof delimiter, ignoring appended source comments; it is not a machine elaboration certificate. No mismatch of displayed binders was found in the two incomplete prefixes either.

| # | Declaration (after outer prefix) | G.md start | Source start | Type comparison |
|---|---|---:|---|---|
| 1 | simplyConnectedSpace_of_homotopySixSphere | 365 | SH:14047 | Complete |
| 2 | pathConnectedSpace_of_homotopySixSphere | 369 | SH:14052 | Complete |
| 3 | homotopySixSphere_homology_subsingleton | 373 | ST:14166 | Complete |
| 4 | MC.exists_minimal_excellent_morse_system | 390 | ST:6290 | Complete |
| 5 | MC.exists_index_ordered_morse_system_preserving_critical_points | 404 | ST:6943 | Complete |
| 6 | MC.minimal_excellent_morse_extreme_counts_one | 420 | ST:7014 | Complete |
| 7 | MC.exists_outer_index_minimal_ordered_morse_system | 434 | ST:10005 | Complete |
| 8 | MC.exists_excellent_indexed_morse_birth | 471 | ST:8637 | Complete |
| 9 | MC.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum | 505 | ST:9601 | Complete |
| 10 | MC.exists_one_to_three_handle_trade | 537 | ST:9796 | Complete |
| 11 | MC.exists_one_to_three_handle_trade_at_cut | 561 | ST:9884 | Complete |
| 12 | MC.exists_one_to_three_handle_trade_of_ordered_indices | 583 | ST:9977 | Complete |
| 13 | MC.outer_index_minimal_index_one_count_zero | 606 | ST:10065 | Complete |
| 14 | MC.outer_index_minimality_neg | 627 | ST:10113 | Complete |
| 15 | MC.outer_index_minimal_outer_counts_zero | 650 | ST:10146 | Complete |
| 16 | MC.exists_minimal_ordered_morse_system_without_outer_indices | 677 | ST:10195 | Complete |
| 17 | SW.middleMatrix_surjective_of_homotopySphere | 702 | ST:14278 | Complete |
| 18 | SW.middleMatrix_surjective_of_complete_blocks | 717 | ST:14300 | Complete |
| 19 | MC.exists_middle_index_blocks | 726 | ST:14326 | Complete |
| 20 | AW.exists_ordered_middle_family | 744 | ST:14408 | Complete, including its result's initial let |
| 21 | AW.exists_canonical_middle_family | 760 | Rec:1281 | Complete |
| 22 | MC.canonical_middle_matrix_surjective | 777 | Rec:1958 | Complete |
| 23 | AW.exists_primitive_functional_unit | 819 | Rec:5958 | **Incomplete at internal let, Rec:6007** |
| 24 | AW.exists_first_middle_pivot | 870 | Rec:2440 | **Incomplete at internal let, Rec:2480** |
| 25 | MC.exists_native_belt_cut_family | 912 | Rec:6924 | Complete, including initial lets |
| 26 | MC.cancel_from_preserved_unit_belt_cut | 951 | Rec:7273 | Complete, including letI |
| 27 | MC.cancel_from_complete_middle_family | 994 | Rec:7427 | Complete |
| 28 | MC.minimal_ordered_index_two_count_zero | 1031 | Rec:7550 | Complete |
| 29 | MC.minimal_ordered_index_four_count_zero | 1049 | Rec:7610 | Complete |
| 30 | MC.ordered_no_middle_indices_count_two | 1067 | Rec:7836 | Complete |
| 31 | MC.critical_pair_of_surgery_count_two | 1096 | Rec:7963 | Complete |
| 32 | MM.nonempty_homeomorphSphere_of_two_critical_points | 1103 | Rec:7922 | Complete |
| 33 | MC.exists_two_critical_point_morse_of_homotopySixSphere | 1113 | Rec:7991 | Complete |
| 34 | MC.nonempty_homeomorph_of_homotopySixSphere | 1123 | Rec:8009 | Complete |
| 35 | homeomorphic_sixSphere_of_homotopySixSphere | 1131 | Rec:8020 | Complete |

The separate G-headline prose repeats row 35, not a 36th distinct declaration. Counts by group are 3+4+8+1+6+8+5=35. All source-start entries in the thematic table G.md:306–312 agree. The namespace note correctly retains Mathoverflow1973 outside the displayed dotted prefixes; source namespace starts are SH:89, ST:94 and Rec:87. Type versus Type* has not been silently normalized. Source-polymorphic existence/Reeb signatures remain polymorphic; the homology/Recognition chain's Type binders remain Type. This is meaningful preservation, though exact elaborated universes still require the source-matched Axis-5 context.

## Repairs independently accepted and mathematical checks

### Minimum and ordering

ST:6304–6319 uses Nat.find on all excellent Morse functions. ST:10032–10063 minimizes 1+5 among all excellent functions with minimum total count, only then orders and transports both objectives. The not-necessarily-ordered trade output is therefore an admissible competitor. ST:6943–6994 orders by decreasing index-disorder without changing critical points/indices/counts.

ST:6103–6122 obtains non-Joined attaching ends. ST:1611–1700 realizes minimum branches through placement and flow suspension; ST:6204–6223 chooses the higher minimum. ST:6165–6190 establishes a unique connection, makes the pair consecutive with the same flow, cancels it and obtains excellence from surviving critical germs. ST:6996–7036 contradicts minimality and dualizes. G.md:107–125 now records that mechanism rather than assuming the original flow already has distinct minimum endpoints. Compactness plus the homotopy sphere's nonemptiness supplies an actual minimum; finite Morse critical sets justify natural counts. The extreme-count theorem is genuinely general in finrank E and has no hdim/e assumptions.

### Trade

ST:9796–9882 has original hlow ≤2 and hhigh ≥3, births in f⁻¹(Ioo l u), preserves the old cut/critical germs and unique minimum, then calls the unchanged-cut cancellation and computes total/index counts. ST:9601–9642 has the distinct weaker old hlow ≤3 plus new hnewlow ≤2; the ledger correctly preserves the difference. ST:9884–10003 constructs the band/basepoint and ordered cut. ST:10065–10193 performs the secondary-cost contradiction and negation.

The transverse loop is not obtained merely from two points: ST:7039–7185 transports a transverse belt circle and its basin data; ST:8894–8953 transports the attaching circle and applies equal-level isotopy placement. G.md:153–167 now names this substantive chain. The final cancellation's output does not promise equality of the final cut, correctly acknowledged at G.md:150–152. The corrected trade bookkeeping preserves count2, lowers count1, raises count3, keeps total fixed and leaves count5 unchanged.

### Whitney complement and elimination

G.md:212–250 now distinguishes disk avoidance, circle avoidance, surgery complement transport and regular-cut family transport. ST:5716–5775 starts at the first sublevel disk and inducts across index2/3 handles and regular intervals; ST:5821–5861 specializes to an ordered index2 prefix. SurgeryWindows:684–750 first obtains contractions avoiding the old attaching sphere, using 2+(k−1)<5, then transports the whole contraction through complementHomeomorph. SurgeryWindows:1374–1389 separately recovers arbitrary upper-boundary circle contractions using the belt's normal dimension. The belt of the chosen index2 handle is S³ bounding the four-dimensional cocore, not the descending core.

SH:19932–19961 passes the lower-level hnull through the signed-chart complement theorem (SurgeryWindows:815–844) into the tubular-bigon construction. Thus hnull is a sufficient lower-level hypothesis, not literally the complement-injectivity proposition. Orientability follows here from simple connectivity; the framed Whitney input remains the named substantive geometric theorem, not an unsupported consequence of mere ambient simple connectivity.

Rec:6888–6921 supplies the last index2 collapse functional, primitivity and lower contractions. Rec:6924–7001 transports a family/matrix through a critical-free band above that critical value; it is not the surgery complement map. Rec:6075 onward forms the primitive functional row and applies integer column additions; Rec:7467–7478 consumes the full unit result and makes the selected index3 point first. Rec:7514–7548 proves consecutiveness, transports the unit/forward-flow data, cancels and restores excellence. These are exactly the data lost from the two truncated ledger rows, despite the narrative now being sound.

Rec:7550–7608 eliminates index2; 7610–7653 applies −f to eliminate index4. Only after both vanish does Rec:7836–7855 use complete blocks/middle-count equality to eliminate index3. The H3=0 explanation is mathematically correct: with chain groups C2=C4=0, H3 is free on C3. Surjectivity of the index2/index3 matrix alone does not force C3=0, and current G.md explicitly avoids that error.

### Namespace/sphere/countability/conclusion

The old MorseCancel and Smale prefixes have really been removed in live source. SixSphere at SH:14044–14045 and MetricSixSphere at Rec:322–323 are separate abbreviations with the same unit-sphere body. Hemisphere.Sphere at SurgeryWindows:579–580 expands through Ambient:573–574; SphereHomology.UnitSphere at Lib/AlgebraicTopology/SingularHomology/Sphere.lean:61–62 is the same at 6; SixSphereCube.StandardSphere at Hopf/Hurewicz.lean:395–396 abbreviates the latter. Source reduction therefore supports all five S6 spellings. Attaching domains Hemisphere.Sphere 2 remain S2, not S6.

Rec:7922–7961 obtains the two sublevel disks from signed Morse charts at the unique extrema and glues them through Rec:7867–7920. Rec:7999–8007 assembles G2b→index2→index4→count2. Rec:8009–8018 has no SecondCountableTopology M and uses Reeb followed by finrank=6; Rec:8020–8025 retains the instance only on the thin wrapper. The planned drop is supported directly by the source theorem. Mathematically a compact finite-dimensional manifold has a finite chart subcover, each chart domain second countable, so it is second countable; arbitrary compactness alone would not suffice. No ambient inner product on E is required by the headline; auxiliary signed-chart coordinate spaces can still have inner products. The recognition conclusion is homeomorphism, not a claim about diffeomorphism.

G2a outer minimization does not call trade. G2b at ST:10215–10220 explicitly calls G2a then G3. Placing it with HandleTrade rather than MinimalSystem fixes the identified backward dependency. No new coarse cycle was found.

## Commands, outcomes, limits and changes

Git commands used process-local `GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'`. No config-changing script was sourced.

- `pwd`, `git -C /home/ox-alpha/HopfProblem rev-parse HEAD`, `git ... status --short`, initial ledger `sha256sum`: exit 0, snapshot above.
- `sha256sum` on receipt and five primary Lean files near the beginning, repeated with ledger at the end: exit 0, unchanged hashes below.
- `ls -ld /tmp /home/ox-alpha/s6-notes`: exit 0; verified destinations.
- `git branch --show-current`, `git diff --check`, scoped `git diff fdd2143... --stat -- ...`: exit 0; correct branch, no whitespace errors or scoped changes.
- `/tmp/shared-lean-copy/toolchain-v4.33.0/bin/lean --version`: exit 0, Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Specialized read/grep/find tools performed all file reading/searching and the report-name pre-existence check. The requested report did not exist; no overwrite was needed.

Only temporary probe: `/tmp/G_Fresh2_fresh2_g_fdd2143_names.lean`, with exactly:

```lean
import Hopf.Recognition
#check Mathoverflow1973.MorseCancellation.exists_one_to_three_handle_trade
#check Mathoverflow1973.homeomorphic_sixSphere_of_homotopySixSphere
#check Mathoverflow1973.MorseCancel.exists_one_to_three_handle_trade
#check Mathoverflow1973.Smale.homeomorphic_sixSphere_of_homotopySixSphere
```

Executed from the repository:

```sh
LEAN_PATH=".lake/build/lib/lean:$(printf '%s:' .lake/packages/*/.lake/build/lib/lean)" /tmp/shared-lean-copy/toolchain-v4.33.0/bin/lean /tmp/G_Fresh2_fresh2_g_fdd2143_names.lean
```

**Exit 1:** first two checks unknown identifiers; final two print old signatures. No `-o`, no dependency build, no direct Lib import, no mixed production/legacy probe. This checks stale artifact behavior only, not current theorem validity. No production probe or current axiom audit was claimed. `rm -- /tmp/G_Fresh2_fresh2_g_fdd2143_names.lean` exited 0, removing only my exact temporary path.

Changes made: created this requested external report and the temporary probe (then removed it). **No repository file, AGENTS file, source proof, ledger, receipt, E2 artifact or package was edited.** No builds, package writes/updates/cache/clean, commits, pushes or further agents.

## Snapshot fingerprints

These first seven hashes were taken near the start and again at the end and agree:

| File relative to repository | SHA-256 |
|---|---|
| Lib/docs/G.md | `fc96b671c1f8836dbccc1f067d582b04aadf32f5d3a42a9d4594d219d88bd441` |
| Lib/docs/G-INTERFACE_RECEIPT.md | `fadfc1e53e43a7191447ece4359f1eec7397a0a84f5ed2cac01ae0ef353d28f6` |
| Hopf/Recognition.lean | `024cf257f1be675e83c6cea36a79979a5ab099b4c7d4e0535383a05ab13b4c75` |
| Hopf/SphereTopology.lean | `7c24868a60c897402129566760b4f195084984a62483cabc2cdc592a2cca323b` |
| Hopf/SingularHomology.lean | `ef8c2f21e2b609c87ddbc18430db0224899fff9a8006406a7f09d0ef38104801` |
| Lib/Geometry/Manifold/Morse/SurgeryWindows.lean | `923b0135ca43d743d958860c10fe8b71a0780af8b70d6512a35e927d34b8bf2f` |
| Lib/Geometry/Manifold/Morse/Cancellation.lean | `23160e94e92bde9463d048cc51358dd55cb904714b1d3b97ead29640b00ffefb` |

Additional sphere-definition files inspected later, with end hashes (not misrepresented as beginning hashes): Hopf/Hurewicz.lean `de64dd99e551a59fa6e561024d74e6b2562647a84e8adc902aa98a5adbd6009e`; Lib/AlgebraicTopology/SingularHomology/Sphere.lean `846af0888e49195e998fa45ba4307b61e5a89d470d8e48998f293b7d9327e90b`. HEAD stayed fixed and tracked status remained clean.

## Parent actions

Preserve the positive scoped Stage-2/order verdicts. Have the alignment owner restore the two dependent result tails and correct certification wording, without changing Lean mathematics. Arrange source-matched dependency validation separately, close helper/production contexts, then regenerate and independently review the appropriate receipt before any Axis-6 GO. This report certifies only the exact unchanged snapshot above; subsequent repairs require their own final-hash check.
