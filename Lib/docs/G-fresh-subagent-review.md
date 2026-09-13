# Fresh independent review of Lane G

*Editorial note (Muse seat): absolute host paths in this report were rewritten to repo-relative or `~/` form when the file was brought in-tree; no other content changed.*

Reviewer: **fresh-g-subagent** (Devin subagent).
Scope: review and report only; no ledger repairs, repository edits, commits, package writes, or builds.

## Reviewed snapshot and verdicts

- Repository: `the repository root`, branch `lib/textbook-extraction`.
- Initial observed HEAD: `37fc1de8a74a3b294a54fd9e804c82c074ae9591`.
- HEAD advanced during this review to `7e98c5835863c6b241143dcc9f593ccc855f9fc9` (E2 documentation repairs, by another worker). The six scoped files below have **no diff between those two commits**. This report applies to their identical contents at both HEADs, not an imagined earlier `bd9c393` checkout.
- Initial and latest observed working-tree status: only `?? AGENTS.md`; no tracked modifications. `git diff --check` exited 0. The working tree is therefore tracked-clean, not literally clean.
- Canonical ledger SHA-256: `d1f3cd187c790454ac2a1c30dee4a8ef278873ff7faa364e263e775dbf0ab463`.
- Receipt SHA-256: `db9baebf51bb050696b56b99e36a6a6ae77511cc321881a56dcc5a8ee13e5b1d`.

**Scoped verdicts:**

1. **GO for the repaired central mathematical narrative in §§3–5**, with the precision suggestions below. I independently recovered the comparison classes, unique-minimum cancellation, trade bookkeeping, relative disk avoidance, complement transport, and elimination order from current source bodies. I found no new false mathematical implication in those repairs. This is not certification of every transitive geometric theorem.
2. **GO for the particular G2a → G3 → G2b ordering and four-file coarse placement repair.** No residual cycle was established at that level.
3. **NO-GO for G.md as an exact current-tree typed ledger/source map.** Its namespace and coordinate assertions are stale after actual source renames/extractions. This is a real alignment defect, not evidence against Smale's theorem.
4. **NO-GO for full Axis-5 certification or any Axis-6 handoff.** The receipt is historical, the current compiled artifacts disagree with live sources, helper closure is incomplete, and no aggregate production-module provider/consumer packet has been certified. These are separate certification obligations, already partly acknowledged in G.md, and must not be relabeled false mathematics.

## Method and independence

First read `~/collaboration-protocol.md`, repository `AGENTS.md`, and the full `lean-protocol.md`, including Stage 2 and the certified Axis-5 handoff requirements. Then read all 1,256 lines of G.md and all 68 lines of its receipt. Inspected live source declarations and the load-bearing proof bodies, including helpers outside the suggested ledger coordinates. Formed the findings about the repaired mathematics, stale names/coordinates, stale compiled context, and incomplete ownership before consulting any previous G review. Only afterward read `Lib/docs/G-stage2-astra-review2.md` as a checklist. Its old findings are not substituted for current inspection.

## Numbered findings and specific actions

### 1. Current-source names in the ledger are materially stale (high, Axis 5)

**Locations:** `Lib/docs/G.md:329–346,351–359,373–442,454–679,685–787,801–1140,1158–1198,1208–1225`.

The claim that these are verbatim current-source signatures, and that the stated dotted prefixes are the actual namespaces, is no longer correct. Live source has `Mathoverflow1973.MorseCancellation`, not `Mathoverflow1973.MorseCancel`; the transitional `Smale` prefix has been removed. For example:

- `Hopf/SphereTopology.lean:6290`: `MorseCancellation.exists_minimal_excellent_morse_system`.
- `Hopf/SphereTopology.lean:9796`: `MorseCancellation.exists_one_to_three_handle_trade`.
- `Hopf/SingularHomology.lean:14047,14052`: the two connectivity results directly under `Mathoverflow1973`, not `Mathoverflow1973.Smale`.
- `Hopf/Recognition.lean:8020–8025`: headline directly under `Mathoverflow1973`; its body calls `MorseCancellation.nonempty_homeomorph_of_homotopySixSphere`.
- `Hopf/Recognition.lean:1958–1988,7550–7566,7991–8018`: Recognition uses `MetricSixSphere` where the ledger uses the older local `SixSphere` spelling.

Git history independently identifies `c6e6353` (MorseCancel rename) and `10dc75c` (Smale-prefix removal). This affects binder references too, not merely the heading names. The mathematical signatures inspected retain the ledger's essential hypotheses and results after accounting for these renames/spellings; I did not find a new missing trade hypothesis or invented count result.

**Fix:** re-census all 35 signatures against the live source namespace context, explicitly distinguish source signatures from designed target signatures, and record exact opens/instances/public context. Do not blindly change every `SixSphere` token: there are distinct source abbreviations, and intended sphere consolidation needs its own elaborated representation check. Retain the current Type/Type* distinctions.

### 2. Existing `.olean` files expose the old API, not the current source API (high, validation blocker)

**Evidence:** the focused legacy-only probe described below successfully `#check`ed old `Mathoverflow1973.MorseCancel.exists_one_to_three_handle_trade` and `Mathoverflow1973.Smale.homeomorphic_sixSphere_of_homotopySixSphere`. It then failed to resolve the corresponding names actually declared in current source: `Mathoverflow1973.MorseCancellation.exists_one_to_three_handle_trade` and `Mathoverflow1973.homeomorphic_sixSphere_of_homotopySixSphere`.

This is a source/artifact mismatch. A repeat of the receipt's legacy name checks can misleadingly look green while checking pre-rename interfaces. I did **not** interpret the unknown-current-name diagnostics as absent source proofs. No build was launched to refresh the cone.

**Fix:** the parent/integration owner should first obtain a source-matched green dependency/artifact baseline in an authorized build window. Then rerun focused checks. Do not freeze G against these old artifacts, and do not treat this probe as an aggregate interface certificate or current axiom receipt.

### 3. Coordinates and provider inventory need a current-head refresh (medium, documentary alignment)

**Locations:** `Lib/docs/G.md:285–297,216–241,269,1201–1204,1250–1256`; `Lib/docs/G-INTERFACE_RECEIPT.md:3–10,29–49,66–68`.

The old Recognition coordinates have shifted by 1,407 lines in the inspected declarations: e.g. belt-cut family is now `Hopf/Recognition.lean:6924`, not 8331; complete-family cancellation is 7427, not 8834; count-two is 7836, not 9243; Reeb is 7922, not 9329. The statement that relevant Lean sources are unchanged from `699d1a4` does not describe this HEAD.

Current `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` has 1,838 lines, not the historical 17,556-line inventory. It still lacks a `module` header, but its toolbox has been split; its own lines 33–36 record the split. `AdaptedWindows` is now at 1821, whereas `nativeMorseIndex` is in `Lib/Geometry/Manifold/Morse/Cancellation.lean:4987`. The complement lemmas are SurgeryWindows:708,722,815,1374, not 691,705,798,1357. The historical receipt's geometric module gate is therefore directionally valid but its provider locations are not a current dependency inventory.

**Fix:** replace or unmistakably label historical coordinates and provider sizes, refresh the per-provider module/legacy inventory, and give the receipt a precise historical/draft status. Its 36 old checks do not certify the present 35-row document hash. G.md:5's “present uncommitted amendments” should likewise become a historical statement: the scoped documents were committed at the observed HEADs.

### 4. Helper ownership and production visibility are open obligations, not a new mathematical counterexample (Axis 4/5)

**Locations:** `Lib/docs/G.md:367–369,790–796,1231–1234,1244–1249`; receipt:27–62.

The coarse four-file order is sound, but the 35 public theorem rows are not a complete proof-dependency graph. Specific needed helpers include:

- G2a's joining-components → branch-realization → consecutive-pair → surviving-germs chain (`Hopf/SphereTopology.lean:6103–6223,6996–7036`).
- G3's ordered cut and birth-retention/count helpers (`Hopf/SphereTopology.lean:9644–9882,9936–10003`).
- G5's `last_index_two_collapse_is_primitive`, equal-cut coherence, and recovery of excellence after cancellation (`Hopf/Recognition.lean:6888–6921,7521–7548`).
- The final H3/count chain through `middle_counts_equal` (`Hopf/Recognition.lean:7836–7855`).

The document expressly leaves this census open; that honesty should be preserved. Reeb is explicitly a D1 dependency at G.md:1171–1173, not a reason for G to duplicate D1 ownership. The birth result similarly needs an unambiguous E1/G consumer-versus-owner designation at final decomposition.

**Fix:** assign every helper to its earlier FREE provider or G packet, name actual green dependencies and minimal imports, record public contexts, and produce per-boundary aggregate provider-plus-importing-consumer receipts as required by `lean-protocol.md:302–425`. A legacy `import Hopf.Recognition` test cannot certify a new production `module`, and a production module cannot simply import that legacy file. No new cycle beyond missing certification was demonstrated.

### 5. Small narrative precision improvements (nonblocking mathematical clarifications)

**Locations:** `Lib/docs/G.md:151–160,183–186,229–241`.

The trade's two distinct points on the one-dimensional negative-coordinate sphere support branch selection; they are not by themselves the single-intersection placement theorem. The prose does name the larger transverse-data chain, so I do not read it as asserting the false implication “two points imply transverse placement.” Still, replace “uses the two ... points ... to hit the belt once” by an explicit reference to the loop construction and attaching-circle placement within that chain (`Hopf/SphereTopology.lean:9040–9047,9430–9439`).

For the middle campaign, choose the **last index-two handle's collapse coordinate** explicitly, rather than merely “a primitive coordinate functional.” The source supplies exactly that primitive functional with retained lower-level contractions (`Hopf/Recognition.lean:6888–6921`), then makes the selected index-three point first (`7470–7478`). This directly explains consecutiveness (`7514–7516`). The current prose can be read compatibly, but naming this choice prevents an arbitrary coordinate from being mistaken for already isolated cancellation data.

The Whitney paragraph would also benefit from one ordinary-mathematics sentence about choosing orientations and the framed Whitney move, rather than leaving “orientation hypotheses” implicit. In this setting the manifold is orientable (simply connected), its regular hypersurface inherits an orientation, and the spheres are orientable; this is not a missing assumption on M or a new obstruction. Keep the existing named F Whitney theorem as the substantive geometric input.

## Independent verification of the delicate mathematical points

### Minimality and the unique minimum

`Hopf/SphereTopology.lean:6290–6319` really minimizes over all excellent Morse functions. `10032–10063` minimizes 1+5 among all excellent equal-total-count competitors and only then orders, transporting both count objectives. Thus the not-necessarily-ordered trade output is an admissible competitor. The preliminary ordering at G.md:97 is redundant but harmless.

`6103–6122` finds non-Joined attaching ends, not already distinct flow endpoints. `6204–6223` realizes branches and selects the higher of the two distinct minimum values. `6165–6190` proves the unique connection, makes the pair consecutive with the same flow, cancels, and recovers excellent critical values from surviving germs. `6996–7036` contradicts minimality and applies negation. This matches G.md:105–123. Compactness/nonemptiness supplies an actual minimum; finite Morse critical sets justify natural-number counts. The top-index statement is finrank E and does not need a dimension-six hypothesis.

### Trade cut and index bookkeeping

In the base trade (`Hopf/SphereTopology.lean:9796–9818`), hlow is ≤2, hhigh is ≥3, and the band is `Ioo a u` with `a<l` and a point in `Ioo l u`. This puts **all** original index-two points below the cut. The unchanged-cut wrapper (`9601–9631`) has the intentionally weaker old hlow ≤3 plus the new-function bound ≤2; these are distinct signatures and the ledger preserves that difference.

The birth is supported in `f⁻¹(Ioo l u)` (`9819–9826`), retains critical germs and the lower level (`9831–9837`), preserves the unique minimum (`9847–9853`), and supplies the input cut for cancellation (`9858–9861`). The final function is not promised to preserve that level. Count identities (`9862–9882`) give net total zero, count1 minus one, count3 plus one, and unchanged other counts, including count2. Negation swaps 1 and 5 at n=6 (`10113–10193`). G.md's repaired minimality conclusion is justified.

### Whitney disk avoidance, complement transport, and elimination

For a k-handle in dimension six the old obstacle is S^(k−1), the new belt S^(5−k), in a five-dimensional level. Relative disk/homotopy avoidance uses `2+(k−1)<5`, valid for k=2,3. The separate circle-avoidance inequality is `1+(5−k)<5`. These are not interchangeable.

Current SurgeryWindows:684–750 constructs the old-complement contraction and transports the entire homotopy through `complementHomeomorph`. Lines 1356–1389 subsequently contract arbitrary upper-level circles after belt avoidance. SphereTopology:5716–5775 and 5821–5861 implement the induction/specialization. The belt of the chosen index-two handle is the boundary of its four-dimensional cocore, not its core.

`Hopf/SingularHomology.lean:19932–19961` passes lower-level contractions through the signed-chart complement lemma to the tubular-bigon construction. `Hopf/Recognition.lean:6924–7001` instead transports families/matrices through a regular band above the chosen critical value; this is correctly distinguished in G.md. The cancellation at 7273–7382 transports the unit and geometric data to the retained level and invokes the single-intersection machinery. At 7427–7548 it also restores excellence, making the total-count contradiction legal.

The source eliminates index2 (`7550–7608`), index4 by −f (`7610–7653`), and then index3 using complete blocks and equal middle counts (`7836–7855`). Surjectivity alone is not used to discard residual index3 handles. The H3=0 explanation in G.md:248–251 is mathematically correct; it summarizes the source's complete-block matrix/count implementation rather than claiming a literal one-line chain-complex proof in Lean.

### G2a/G2b and the conclusion

The G2a outer-minimal existence proof does not call the trade. The G2b body at SphereTopology:10215–10220 explicitly calls G2a followed by G3, so placing G2b with HandleTrade breaks the previously problematic grouping. Recognition:7999–8007 calls G2b, index2/index4 elimination and count-two in the stated order. Recognition:8009–8025 proves the inner homeomorphism without `SecondCountableTopology`, then retains it on the thin headline wrapper. Dropping that instance in the designed FREE theorem is supported by the actual inner chain, not merely an informal unused-instance claim.

## All 35 ledger signatures: current source census

The following accounts for every theorem entry (3+4+8+1+6+8+5=35). Rows below give **current declaration starts in ledger order**. Inspection was textual, not a machine equality proof of types. After namespace/spelling normalization, no additional hypothesis/result discrepancy was found in these signatures. Some large proof bodies were sampled at their load-bearing calls, not audited exhaustively.

| Group | Current source starts | Namespace adjustment |
|---|---|---|
| G1 (3) | SingularHomology 14047,14052; SphereTopology 14166 | remove Smale prefix |
| G2a (4) | SphereTopology 6290,6943,7014,10005 | MorseCancel → MorseCancellation |
| G3 (8) | SphereTopology 8637,9601,9796,9884,9977,10065,10113,10146 | same |
| G2b (1) | SphereTopology 10195 | same |
| G4 (6) | SphereTopology 14278,14300,14326,14408; Recognition 1281,1958 | remove Smale / rename MorseCancel as applicable; AdaptedWindows unchanged |
| G5 (8) | Recognition 5958,2440,6924,7273,7427,7550,7610,7836 | AdaptedWindows unchanged; MorseCancel → MorseCancellation |
| G6 (5) | Recognition 7963,7922,7991,8009,8020 | rename MorseCancel; Reeb in ManifoldMorse; headline directly in Mathoverflow1973 |

All these are under `Mathoverflow1973`. The four unchanged AdaptedWindows declaration prefixes do not make their displayed signatures current: the types still contain renamed dependent constants. The separate headline prose row is a duplicate description, not a 36th distinct theorem.

## Commands and actual outcomes

All Git commands used environment `GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'`; no script was sourced and no git configuration was changed.

- `git rev-parse HEAD && git status --short && git diff --stat`: exit 0; initial HEAD and `?? AGENTS.md` as above; no tracked diff.
- `ps -eo pid,etime,args`: exit 0; inspected the process list before considering checks. No running Lean/lake build was identified. No build was subsequently launched.
- `git log -6 --oneline`, `git log -4 --oneline -- Hopf/SphereTopology.lean Hopf/Recognition.lean`: exit 0; observed the concurrent E2 commit and the namespace-rename history.
- `git diff --check`: exit 0.
- `git hash-object Lib/docs/G.md Lib/docs/G-INTERFACE_RECEIPT.md Hopf/Recognition.lean Hopf/SphereTopology.lean`: exit 0; blobs respectively `6f570cf71cda8dce701c9b3fc1cf883cbfbc97f3`, `c91cd3c792636a00e87cb9b2fcdeb9251d5481fe`, `ff46fdc2cfef51e468625632e06e598b67d7b5fe`, `6e5461497e619a7890d8b20eaf42f89d80bbbf0e`.
- `sha256sum` on the six scoped files: exit 0; hashes below.
- `git diff --stat 37fc1de8a74a3b294a54fd9e804c82c074ae9591 7e98c5835863c6b241143dcc9f593ccc855f9fc9 -- Lib/docs/G.md Lib/docs/G-INTERFACE_RECEIPT.md Hopf/Recognition.lean Hopf/SphereTopology.lean Hopf/SingularHomology.lean Lib/Geometry/Manifold/Morse/SurgeryWindows.lean`: exit 0, **empty**.
- `/tmp/shared-lean-copy/toolchain-v4.33.0/bin/lean --version`: exit 0; Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.

Focused probe command, run from the repository:

```sh
LEAN_PATH=".lake/build/lib/lean:$(printf '%s:' .lake/packages/*/.lake/build/lib/lean)" /tmp/shared-lean-copy/toolchain-v4.33.0/bin/lean /tmp/G_Fresh_subagent_37fc1_names.lean
```

The probe imported **only `Hopf.Recognition`**, with no `module` header and no direct Lib import. Its full content was:

```lean
import Hopf.Recognition
#check Mathoverflow1973.MorseCancel.exists_one_to_three_handle_trade
#check Mathoverflow1973.Smale.homeomorphic_sixSphere_of_homotopySixSphere
#check Mathoverflow1973.MorseCancellation.exists_one_to_three_handle_trade
#check Mathoverflow1973.homeomorphic_sixSphere_of_homotopySixSphere
#print axioms Mathoverflow1973.homeomorphic_sixSphere_of_homotopySixSphere
```

Actual exit status **1**: first two checks printed old signatures; lines 4 and 5 reported unknown identifiers; line 6 reported unknown constant. Thus **no current axiom audit was obtained**. No `-o` was supplied and no local olean was requested. The check did not build dependencies.

SHA-256 source fingerprints:

| File | SHA-256 |
|---|---|
| Hopf/Recognition.lean | `024cf257f1be675e83c6cea36a79979a5ab099b4c7d4e0535383a05ab13b4c75` |
| Hopf/SphereTopology.lean | `7c24868a60c897402129566760b4f195084984a62483cabc2cdc592a2cca323b` |
| Hopf/SingularHomology.lean | `ef8c2f21e2b609c87ddbc18430db0224899fff9a8006406a7f09d0ef38104801` |
| Lib/Geometry/Manifold/Morse/SurgeryWindows.lean | `923b0135ca43d743d958860c10fe8b71a0780af8b70d6512a35e927d34b8bf2f` |

## Limits, artifacts, and next owner actions

This is a source-level mathematical/alignment review, not a new build certificate, full transitive proof audit, or independently frozen Challenge. I did not fetch/reverify the cited books page by page or prove all general-position and framed-Whitney dependencies anew. I did not perform a production module negative-import experiment because that known seam does not require repeating an intentionally illegal import. No current-source aggregate provider/consumer certificate was possible from the observed artifact baseline without an authorized rebuild.

Only files created by this reviewer: this requested durable report and `/tmp/G_Fresh_subagent_37fc1_names.lean`. No repository, package, E2, or AGENTS file was edited. The report path was checked for pre-existence and was absent before creation. The temporary source probe remains for the parent to remove using an authorized cleanup operation; no generated probe output artifact was requested. The available specialized filesystem tools have no deletion operation, so I have not used the terminal tool contrary to its file-operation restriction to remove it.

Parent actions: (1) retain the positive scoped mathematical/order verdicts; (2) arrange current-source dependency validation rather than trusting stale oleans; (3) have the owning alignment pass refresh namespaces, coordinates, provider census and receipt; (4) finish helper ownership and per-boundary public module certification before Axis 6; (5) remove only the named temporary probe. Do not repair G or the repository merely as a side effect of delivering this review.
