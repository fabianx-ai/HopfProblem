# E2 fresh second independent review

*Editorial note (Muse seat): absolute host paths in this report were rewritten to repo-relative or `~/` form when the file was brought in-tree; no other content changed.*

Reviewer identity: **fresh2-e2** (new reviewer, not fresh-e2-subagent or astra).
Scope: CURRENT `Lib/docs/E2.md`, all 991 lines, its historical receipt, and direct live-source correspondence. No repository edits.

## Snapshot and scoped verdict

- Start and end HEAD: `fdd2143ee7d33a8aec945a48c4c95c4503c3e38e`.
- Branch at final check: `lib/textbook-extraction`.
- Start and end status: only pre-existing `?? AGENTS.md`; no tracked changes.
- E2 SHA-256: `907209bad0f45ed324a9d1eb6e100021a0286c42b1485344c2c9a01212c29464`.
- Receipt SHA-256: `5b37da9d7d0418ff634d1acc696aab8d736e4a825b043b8b4dd62c1ac940afea`.
- All eight scoped Lean source hashes below were measured before source inspection and again after it; none changed.

**Stage-2 substantive mathematics: accepted.** The requested substantive repairs are present and coherent. I found no remaining counterexample to the stated headline theorems or defect requiring redesign of the rank/collision, relative reduction, supported transport, disc assembly, or arc constructions. Two small literal exposition corrections are listed below; this is not an unconditional assertion that every sentence is already freeze-ready.

**Exact document/ledger freeze: NOT YET.** Two residual pre-split line-number lists still claim to be current; fix those and the local wording issues below. Current source signatures inspected agree with the displayed existing headline types and full structure. This is a source-comparison verdict, not a new machine-elaboration certificate.

**Full Axis-5/6 readiness: NOT GO / DRAFT, correctly declared by E2 itself.** Deferred helper certification is not false mathematics. Missing exact packets, public-module providers, aggregate importing-consumer tests and reviewed-hash receipts remain genuine implementation gates under `lean-protocol.md:89–109,281–297,302–425`.

## Method and independence

Read `~/collaboration-protocol.md` first, then repository `AGENTS.md`, Stage-2 and Axis-5 requirements in `lean-protocol.md`, the entire current E2 and receipt. Independently examined the mathematical implications and live source declarations/proof bodies before reading `Lib/docs/E2-fresh-subagent-review.md` and `Lib/docs/E2-stage2-astra-review.md` as a final checklist. Those older verdicts are not evidence of present failures. Historical receipt names and pre-integration commands were treated as historical, not asserted to be today's API.

No Lean probes were run in this review. Direct source inspection suffices to identify the residual coordinate mistakes without relying on potentially stale oleans. Accordingly there is no new legacy or production elaboration success/failure to report, and no missing-artifact diagnosis is being mistaken for a source type error. I did not invoke a build to create artifacts.

## Numbered actionable findings

### 1. Residual old coordinates in the otherwise repaired source ledger

**Severity: medium for exact provenance/freeze; no substantive mathematical defect.**

`Lib/docs/E2.md:805–806` says:

`Existing sources (Immersion/Relative.lean:1632, 12308, 12352, 12370, 12433 ...)`.

The current file has 4,641 lines. The intended current list is **1632, 1970, 2014, 2032, 2095**:

- `ManifoldImmersion.exists_immersion_on_compact_rel`: `Lib/Geometry/Manifold/Immersion/Relative.lean:1632`.
- `ManifoldImmersion.exists_compact_embedding_of_immersion_within_target`: same file `:1970`.
- `ManifoldImmersion.exists_compact_embedding_of_immersion`: `:2014`.
- `ManifoldImmersion.exists_relative_compact_embedding`: `:2032`.
- `ManifoldImmersion.exists_relative_compact_embedding_twoDimensional`: `:2095`.

`Lib/docs/E2.md:857` likewise gives curve wrappers `2927/13308`; this should be **2927/2970**, with names `ManifoldImmersion.exists_relative_compact_curve_embedding_within_target` and `ManifoldImmersion.exists_relative_compact_curve_embedding` respectively. The affine helper at 2698 is correct.

**Action:** replace these two leftover lists. This is particularly necessary because E2:577 says all coordinates below are current. Most repaired table entries, individual theorem comments, and receipt provider mappings are now right; do not reject the entire provider-location repair because of these two remnants.

### 2. Homogeneity's open-orbit sentence must restrict the partition to U

**Severity: low, local Stage-2 exposition/scope correction; headline T7 remains valid.**

`Lib/docs/E2.md:337–344`, especially 341–342, fixes an arbitrary open U and then says these orbits “partition M into open sets” and a connected manifold has one orbit. That is literally false for the group fixed outside a proper U: points outside U have singleton orbits, generally not open. For example M=R and U=(-1,1).

**Action:** say that the orbits **inside U** are open (move locally around each already-reached y and compose), their complements in U are unions of such open orbits, and the connected path image contained in U lies in one orbit. For global connected homogeneity take U=M. This is exactly the distinction in `Lib/Geometry/Manifold/Immersion/Relative.lean:136–164` (orbit includes y∈U and U minus the orbit is open), `:182–203` (preconnected A⊆U), and `:205–216` (A is the path image). The existing finite-local-ball proof at E2:342–344 already gives the correct desired endpoint motion; no new theorem is required.

### 3. Negation preserves conullness, not every conull set

**Severity: low, literal mathematical wording only.**

`Lib/docs/E2.md:183–185` says “co-null sets are symmetric under negation.” A conull set need not equal its negative; R\{1} is an immediate example.

**Action:** replace with “negation preserves conullness.” The sign change in the translation argument is correct: g(y)-f(x)=a corresponds to f+a transverse to g, then replace a by -a. Live source `Lib/Geometry/Manifold/Transversality/Basic.lean:253–302,304–378` supports this calculation. This does not affect T2.

### 4. Keep historical probe claims and pending production certification unmistakably separated

**Severity: informational/open Axis-5 blocker, not new false mathematics.**

`Lib/docs/E2.md:564–570` starts “probed: every FQN below resolves” but immediately correctly says the receipt does not certify the repaired draft. `Lib/docs/E2-INTERFACE_RECEIPT.md:7–13` explicitly makes its pre-rename/pre-split results historical. Do not upgrade the opening phrase into a current-head probe claim. Prefer “the historical spellings were probed; current spellings below were checked against source.”

E2:583–595,950–968 properly leave exact imports, helper/output census, per-file green boundaries, public providers and aggregate provider/consumer receipts open. The G-E2 incidence/projection/collision and patch interfaces at E2:407–412 are explicitly deferred. Those declarations still require exact Challenge packets before Axis 6, not reinterpretation as a failure of the mathematical existence proof. The historical receipt's E13-placement and D1/D2 caveats at receipt:124–131 are superseded by current E2:557,873–874,950–958; since the receipt labels itself historical, they are not present production instructions.

Minor editorial follow-up: E2:800 refers to “§14's namespace table,” but that placement table has File/Rows/Mathlib-twin columns, not a namespace table. Preserve the actual FQNs and either remove that cross-reference or point to E2:593–595.

## Accepted repairs and independent mathematical checks

### Countability, Sard, translation, ambient and map general position

- E2:34–40 supplies Hausdorff second-countable finite-dimensional boundaryless conventions, while conserving the weaker Lean instances. Countable chart covers and compact exhaustion follow. The critical set is closed for smooth maps, its compact-piece critical images are compact null sets, hence nowhere dense. This justifies the comeager narrative at E2:154–165 under the textbook conventions; the source headline at `Transversality/Basic.lean:227–251` promises the null exceptional set only and explicitly uses a Lindelöf countable subcover.
- E2:601–651 retains `[LindelofSpace X]` or `[LindelofSpace (X × Y)]`, Haar/Borel structure and the equal-dimension equations exactly as the source at Basic:227–235,304–321,354–369.
- The compact ambient patch induction conserves open joint-surjectivity over compact treated-patch × Y and open chart compatibility. The ambient signature at E2:654–666 matches `Morse/Rearrangement.lean:2581–2593`.
- **Requested padding repair accepted:** E2:225–233 now bounds the padded f derivative by dim X and the coproduct by **dim X+dim Y**, strictly below dim N. Compact Y is explicitly imposed for the ambient version at E2:66. The disjunction provider name `MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension` at `Morse/Rearrangement.lean:2609` is correct.
- Map general position uses source cutoffs, lower-dimensional smooth bad-parameter images on the nonzero-cutoff domain, closed obstacle range and compactness to preserve already-clean regions. E2:672–699 matches `Morse/SurgeryWindows.lean:378–425`, including the closed-range version's product Lindelöf instance and the compact-Y version. The source explicitly covers the compact old bad locus at :393–410; no finite obstacle cardinality is needed here.

### Immersion and embedding

- E2:352–364 correctly states Disjoint L C and chooses a compact buffer D inside the immersive open locus containing T∩C in its interior. Then L=T\interior D is compact and disjoint from C. This is exactly the mechanism at `Immersion/Relative.lean:2045–2060`, not an unjustified closure of an immersive neighborhood.
- E2:373–384 correctly computes df+A on the plateau. The parameter direction makes evaluation a submersion; rank-r codimension is (n-r)(k-r), so the projected incidence has dimension at most k+kn-(n-k+1), below kn iff 2k≤n. Countable charts justify the Hausdorff-dimension bound; k=0 is separately immediate. The proposed stronger 2k+1≤n bound is sound, not asserted sharp for immersion alone.
- E2:400–405 correctly explains the stronger collision threshold: for distinct x,y the A(x-y) equation has n independent conditions, giving incidence dimension 2k+kn-n, below kn when 2k<n. `Immersion/Relative.lean:1192–1228` truly removes rank defects and collisions, and :1490–1509 truly returns a closed embedding on the new compact patch as well as immersion on K∪L.
- E2:414–428 correctly uses source-dependent separating cutoffs, not ambient postcomposition to remove double points. Local immersion gives uniform near-diagonal injectivity on compact K; the remaining double-point locus is compact. Fixed-part injectivity guarantees one foot can be perturbed away from C. The finite cover by separating patches appears at `Immersion/Relative.lean:1984–2012`. No false assumption of finitely many double points remains.
- The existing plane headline E2:809–820 matches source :1632–1643. The general-source embedding signature E2:823–835 matches :2014–2026. G-E2:844–855 remains a proposed model-vector-space-source target, not an existing declaration or a certified new proof. Arbitrary-manifold wrappers are explicitly contextual/deferred.

### Supported extension, full structure and disc assembly

- E2:255–265 correctly uses global bijective slices and one compact K⊆U: fixedness outside K forces A_t(K)=K and A_t(U)=U. Glue on V and Y\Phi(K), both open, agreeing on the overlap. The source at `Transversality/Basic.lean:2547–2591` constructs exactly that family; arbitrary local-diffeomorphism surjectivity is not claimed.
- The separate classical submanifold velocity-field argument is explicitly context, not falsely identified with chart transport. `IsotopicToIdentity` at `Morse/Cancellation.lean:3374–3380` has no support witness.
- E2:710–719 faithfully reproduces **all seven** `SupportedRelativeIsotopy` fields at `Morse/Cancellation.lean:3441–3450`, including `d x = family (t,x)` in slices. Compactness of K remains separate. Extension's binders, result and family expression E2:726–738 match Basic:1061–1073. No new machine test was performed.
- **Requested displacement repair accepted:** E2:304–306 now explicitly says displacement h-id=o(r) and d(h-id)=o(1), with cutoff derivative O(1/r). The product-rule estimate is correct.
- Full-disk tubular thickenings are available from `Collar.lean:1514–1528` and applied at Basic:2723–2737. E2 retains compact M and dimension at least two; the latter supplies a nontrivial ambient frame index at Basic:2742–2748.
- The normal correction preserves the zero section and makes determinant exactly one in live code, Basic:2154–2172. E2:307–310 now explicitly distinguishes that route from the compatible sign-plus-scaling narrative. Uniform flow agreement is only on a smaller neighborhood whose trajectories stay in the plateau, correctly stated at E2:299–302.
- Ambient radial shrinking is transported through the thickened, normal-rescaled ellipsoid, not through a lower-dimensional slice. Basic:2593–2645 constructs supported shrinkings. E2:317–328 supplies the appropriate positive radial/tangential eigenvalues, compact support and time convention.
- The final equality **Q inverse composed with R composed with P** is stated at E2:330–333 and directly realized at Basic:2694–2706. The same-center disc type E2:758–771 matches Basic:2708–2721.

### Sphere maps, transverse intersection and finite arcs

- E2:133–145 names the correct providers: Mathlib `Geometry/Manifold/SmoothApprox.lean:82,107` has vector-space target and sigma-compact Hausdorff manifold source; separate `ManifoldSmoothing.exists_smooth_map_homotopicRel` is at `Morse/Existence.lean:2028–2034`. The tubular provider is at Collar:1514. These names and locations are live source, not unlanded mathematics.
- `Hopf/SingularHomology.lean:14144–14160` really approximates a sphere map within distance one as an ambient vector-valued map, normalizes it and uses the nonzero normalized segment homotopy. Its nullhomotopy outputs :14199–14217 agree with E2:865–871. Stereographic contraction and the lower-dimensional omitted-point argument are sound.
- E2:449–460's crossing-chart shear is valid: transverse complementary tangent spaces give the graph, with h(0)=0, and the shear preserves the first sheet. Compactness plus discreteness gives finiteness. The two E13 types at E2:875–902 retain all source hypotheses from SH:11271–11306, including ambient compactness and, for finiteness, both compact sources and injectivity. The stronger textbook ambient scope is not falsely substituted into the exact ledger.
- **Requested E5 arc-route repair accepted:** E2:480–494 identifies `exists_smooth_path_avoiding_finite` at `Immersion/Relative.lean:340–380`, which models S as a zero-dimensional manifold and invokes map general position on the interval, fixing its endpoints, using 1+0<n. Homogeneity in the complement is used by :382–390. The punctured-ball discussion is explicitly an alternative, not claimed live implementation.
- Short-arc construction E2:472–478 matches SH:18380–18439: endpoint-local derivative repair of a constant curve, local injectivity, then small positive rescaling. It does not invoke the n≥3 global curve engine for n=2.
- **Requested endpoint-x repair accepted:** E2:496–500 explicitly handles x∈S via short-arc injectivity and g(0)=x. This exactly matches SH:18502–18505. Endpoints in S are allowed, and injectivity also prevents interior points mapping to y. E14's two complete headline types match SH:18380–18390 and :18441–18452.

## Source hash manifest (identical before and after review)

Paths relative to `the repository root`:

| File | SHA-256 |
|---|---|
| Lib/Geometry/Manifold/Transversality/Basic.lean | c00c6fff5a57d7372c51d4d1483bb57f2bafeec99f73e143b22b054769aa4b21 |
| Lib/Geometry/Manifold/Immersion/Relative.lean | 049a7a2e8bd8db2c4df5d86132852c74aa57da3857ee5153b16e4483885f88ae |
| Lib/Geometry/Manifold/Morse/Cancellation.lean | 23160e94e92bde9463d048cc51358dd55cb904714b1d3b97ead29640b00ffefb |
| Lib/Geometry/Manifold/Morse/Rearrangement.lean | 2c7785c5fb8754482e5d8b97e5a7cb96213a6cd338836f2fdd75a575bffe12aa |
| Lib/Geometry/Manifold/Morse/SurgeryWindows.lean | 923b0135ca43d743d958860c10fe8b71a0780af8b70d6512a35e927d34b8bf2f |
| Lib/Geometry/Manifold/Collar.lean | 95f064b90be9d445ca97aee1029fe67ffbad02f5e965d5b6814d51ffcb0b6a9d |
| Lib/Geometry/Manifold/Morse/Existence.lean | 031b01800f4266b018e505088dd3387d4669744a274ca9fe21923d96a36cebc7 |
| Hopf/SingularHomology.lean | ef8c2f21e2b609c87ddbc18430db0224899fff9a8006406a7f09d0ef38104801 |

## Commands, outcomes, changes and limits

All Git invocations used environment `GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'`. No environment/config-changing script was sourced.

1. `pwd && git -C the repository root rev-parse HEAD && git -C the repository root status --short && sha256sum Lib/docs/E2.md` — exit 0; initial snapshot above.
2. `sha256sum` on receipt and all eight source paths in the manifest — exit 0; initial hashes above. Specialized read/grep/find tools supplied all document/source inspection; no source files were modified or generated.
3. `ls -ld ~/s6-notes /tmp /tmp/shared-lean-copy/toolchain-v4.33.0/bin` — exit 0. Required toolchain directory exists; it was not invoked. Report-name lookup found no existing `E2-fresh2-subagent-review*`, so no overwrite or suffix was necessary.
4. Final combined command: `git -C the repository root rev-parse HEAD && git -C the repository root branch --show-current && git -C the repository root status --short && git -C the repository root diff --check && sha256sum` on E2, receipt, and all eight absolute source paths above — exit 0; HEAD/status/hashes unchanged, diff check clean.
5. Wrote only this new report at `Lib/docs/E2-fresh2-subagent-review.md`; existence is checked after writing. No temporary probes or generated local artifacts need removal.

No repository/source/ledger/AGENTS edits; no G-artifact inspection or changes; no builds, package writes/update/cache/clean, Git configuration changes, commits, pushes or further agents. No new proof stubs, axioms or sorrys. Exact textbook edition/theorem-number verification, full axiom audit, exhaustive helper/consumer census, full compilation and aggregate production interface tests were not performed. Hash stability bounds this verdict to the actual current source snapshot rather than an old repair state.

**Parent action:** accept the substantive repairs, request only the targeted residual coordinate and wording fixes, and retain explicit DRAFT/NOT GO for certified Axis 5/6 until the independently reviewed exact packets and aggregate receipts exist.
