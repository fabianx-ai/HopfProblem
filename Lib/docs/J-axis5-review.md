# Lane J — independent Axis-5 review

**Verdict: NO-GO.** Do not hand this packet to Axis 6.

Reviewer: **Devin, seat `devin-axis5-j`**, independent of Muse's author/probe receipt. Date: 2026-09-12.
Repository: `/home/ox-alpha/HopfProblem`, branch `lib/textbook-extraction`.
Reviewed HEAD: `0216863e9af9306af2b8392a654b6c3ec4a532a4`.
Reviewed `Lib/docs/J.md` SHA-256: `1f794cd26c4f0e564f15fd599b24fda78b5fd61487a8ff67a69ebebbd36f424c`.
Receipt SHA-256: `95784c74c7b64eb63dbad178c25fa26ba71853b352500883c0c092e4d4594cf9`.
This identifies the rejected candidate, not a frozen GO hash.

I read the collaboration protocol, the complete lean protocol (especially lines 281–426), the revised ledger at 0216863, and then Muse's receipt. I did not review the stale f034c13 ledger. The working-tree ledger and sources matched 0216863. This is an interface review, not a second textbook review or proof implementation.

## Numbered findings

1. **BLOCKER — proposed universe generalizations do not elaborate.** `Lib/docs/J.md:382–387` (`Pontryagin.product`) and `415–419` (`Pontryagin.exteriorMap`) use `(G : Type*)`. The actual input API at `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean:853` is `Mathoverflow1973.SingularMayerVietoris.SingularHomology (Y : Type) [TopologicalSpace Y] (n : ℕ) : ModuleCat.{0} ℤ`. The cross product at `CrossProduct.lean:1689` is likewise restricted to `Type`. Independently reproducing the two proposed signatures as temporary axiom declarations, with the missing namespace context and local instances supplied, exits 1: `G : Type u_1` is expected to have type `Type`. This is not a stale-olean/internal-declaration error. The corresponding type expressions with `G : Type` both elaborate. **Fix:** retain explicit universe 0 for this boundary, or separately align and land a genuine universe-generalization of the dependency chain. Do not describe `Type → Type*` as merely cosmetic.

2. **BLOCKER — namespace/elaboration context is omitted.** `Lib/docs/J.md:334–451` presents names such as `SingularMayerVietoris.SingularHomology` and `PeriodTorusHigherHomologyPontryagin.product` without recording the enclosing `Mathoverflow1973` namespace. Source evidence: `MayerVietoris.lean:93` and `Hopf/LCP/Specialization.lean:80`. An independent legacy probe importing only the prescribed two Hopf modules cannot resolve these names at root. Adding `open Mathoverflow1973` resolves all 46 project API checks. `Lattice` is also `Mathoverflow1973.Lattice`. Moreover, the notation `⋀[ℤ]^n M` expands to **`ExteriorAlgebra.exteriorPower ℤ n M`**; spelling it as bare `exteriorPower ℤ n M` needs `open ExteriorAlgebra`. The root namespace `exteriorPower` containing `ιMulti/map/alternatingMapLinearEquiv` is distinct from this declaration. **Fix:** record complete qualified names, opens/scopes, local instances, and production namespace context. Specify whether target names beginning `AlgebraicTopology...` are root-qualified rather than accidentally nested under `Mathoverflow1973`.

3. **BLOCKER — the Axis-5 rows remain a headline census, not exact per-microlemma signatures.** Row-by-row audit:
   - **J-headline, `J.md:334–352`:** the main type is substantially specified once namespace context is supplied, and its source location 14963 is correct. But `binomialModuleSuccEquiv etc.` is not an enumerated typed API; the five seam names have no signatures/hypotheses in the ledger. For example, `connectedHomologyZeroEquiv` requires `[PathConnectedSpace X]`, and `totallyDisconnected_homology_subsingleton` requires `[TotallyDisconnectedSpace X]` and `hn : n ≠ 0`.
   - **J-pontryagin, `354–387`:** current `product` and `tripleProduct` have matching displayed types. `product11/12` are only value abbreviations; `product11_skew`, `product11_self`, and the naturality suite omit full binders/results and some source locations. The sole proposed product signature fails as in finding 1. Destination signatures for the remaining promised product API are absent.
   - **J-wedge, `389–431`:** current `homologyWedgeTwo` and `latticeWedgeTwo` types match after supplying context. The apply lemma lacks all its binders, including `v : Fin 2 → SingularHomology G 1`; degree-three variants are described by analogy; `coordinateTorusMapAlong/ClassAlong/BasisAlong` is slash shorthand rather than three declarations; surjectivity and four equivs have names but no signatures. The proposed general-n map fails as in finding 1. The torus exterior-equiv type is explicit, but the typed basis-image/rank/Orzech steps that construct it are absent.
   - **J-exterior, `433–438`:** the current basis type is supplied, but the minor theorem has no proposition or matrix/subset binders. The target is only names, including the literal **`…_map_coefficient`**. This is expressly prohibited by Stage 5.
   - **J-charged, `440–445`:** prose-only row with **`squareA₁ …`** and `etc.`; no declaration-by-declaration signatures or consumer substitutions. The four `LocalSystemMatrices` APIs are named, not typed. Source inspection confirms they are currently rank-4-specific (`FiniteCore.lean:328–338`), not already arbitrary-rank signatures.
   - **Local instances, `447–451`:** another literal **`…`** appears in the required attribute wrapper; the exact local-instance context and signatures of the two instance-reducible definitions are not recorded per boundary.
   **Fix:** enumerate every in-scope declaration, exact current and proposed signature, namespace/context, source location, and consumer. Explicitly exclude unchanged charged declarations if they are only background; otherwise give their actual adapter signatures. Do not treat unnamed families or `etc.` as a finite Challenge packet.

4. **BLOCKER — general-n descent has no complete green dependency interface.** `J.md:420–430` proposes arbitrary-n alternating multiplication using swap/associator coherence and `product11_self`, but supplies no typed recursive n-fold product, zero-degree unit, adjacent-swap lemma, repeated-entry vanishing lemma, or basis-image statement. The named existing `crossProductHomology_swap` at `Specialization.lean:4172` is only degrees `(1,1)`. The named `crossProductHomology_associative` at `5949–5956` takes three degree-one classes and concludes in degree 3; it is not arbitrary-degree associativity. These facts exist, but checking their names does not supply the missing general-n step. **Fix:** return this changed statement to the owning decomposition/alignment seam: enumerate the additional general-degree inputs and their owners, or explicitly narrow the first boundary. State exact green dependency commits; do not ask Axis 6 to discover the missing induction/coherence interface.

5. **BLOCKER — required ChallengeNode fields and independently green packets are absent.** `J.md:269–316,328–451`, against `lean-protocol.md:323–347`: broad IDs J1–J8, textbook sections, FREE/CHARGED labels, destinations and consumer files exist, but not a node-level handoff. Missing or incomplete fields are: exact `source` sentence for each microlemma; complete `signature`; `visibility`; minimal `imports`; exhaustive typed green `dependencies`; explicit `representation` equations; exact public `destination`; exact next-node/theorem `consumer`; `commit_boundary`; implemented-boundary `focused_check`; and `return_seam`. There is no exact public-output list per boundary. **Fix:** split the work into independently green packets and fill all thirteen fields for every node, with a node/output census. The extraction-mode exception in protocol lines 178–195 does not exempt the newly designed arbitrary-n and changed-universe statements.

6. **BLOCKER — receipt does not certify this proposed aggregate interface.** `Lib/docs/J-INTERFACE_RECEIPT.md:12–16` lists nine outputs but omits the central new `Pontryagin.exteriorMap`. Its output names such as `pontryaginProduct` do not identify the exact proposed fully qualified outputs. Lines 70–76 expressly report **legacy** probes importing Hopf, not providers with the production `module`/public context required by `lean-protocol.md:353–364`. The listed 34 API checks also omit ledger-cited names, e.g. `totallyDisconnected_homology_subsingleton`, `product_natural`, `tripleProduct_natural`, `latticeWedgeThree`, and the swap/associativity laws. The receipt lacks the ledger hash, boundary list, per-boundary/node census, exact import-visible output count, and clean-tree result required by protocol lines 370–372. Its HEAD is f034c13, not the revised-ledger commit; the source code is unchanged between these commits, so this alone is not a source-code discrepancy, but no hash ties its tests to the revised signatures. **Fix:** after correcting the ledger, regenerate the full aggregate provider/consumer receipt with every promised output and every dependency. Resolve the production-module dependency boundary rather than using legacy visibility as a substitute. This review's exploratory probes do not replace that receipt.

7. **Ownership contradiction.** `J.md:292–301` correctly says the 42 G-J3 coherence declarations are GLM-owned; `J-INTERFACE_RECEIPT.md:87–88` agrees. But `J.md:309` still says **“lane C file; J appends G-J3.”** The J5 source ranges at `279` also overlap that suite without a precise exclusion manifest. **Fix:** remove the J-owned append instruction, enumerate the GLM-owned exclusion/dependency list, and name its future green boundary. I verified the cited homology-level coherence declarations remain in Specialization, not a landed Lib coherence suite. The document does not enumerate all 42, so I do not certify an exact 42-member ownership census.

8. **Dependency order is not the claimed backward-only order.** `J.md:271` says row order is dependency order, but J7 at `281` needs the exterior basis/rank input of later J8; `288–291` explicitly acknowledges this use, as does the proof at `215–218`. The file build order at `315–316` calls MinorCoordinates independent but does not place its needed public outputs before TorusExterior. **Fix:** put the requisite J8 basis/rank packet before J7 and give exact declaration edges. Resolve general-n coherence prerequisites from finding 4 before declaring this graph runnable.

9. **Current-head source locations still contain stale coordinates.** `J.md:434–435` gives standardExteriorBasis/minor theorem at 6636/6640, but their declaration starts are **Specialization.lean:6637/6641**. `J.md:460` cites singularHomologyMap at 857, but its declaration starts at **MayerVietoris.lean:856**. Outside §Axis-5, `J.md:477–482` cites rightTranslation at 17021 (actual **BoundaryTopology.lean:14298**) and formalMap_comp/formalMap_comp_apply/succ_pair at 3770/4450/6438 (actual **3771/4451/6439**). **Fix:** regenerate file:line coordinates at the reviewed head; retain historical coordinates only when clearly marked historical. Namespace-start locations such as ExteriorPower/Basic.lean:47 should not stand in for declaration locations: ιMulti is 56, alternatingMapLinearEquiv 212, map 260.

## Independently verified positives and limits

- Pontryagin product is genuinely `(1,n)`, with result degree `n+1`: `Specialization.lean:3190–3197`, matching `CrossProduct.lean:1689–1693`. The general `(p,q)` product is correctly deferred in the ownership decision.
- The cited A/C seams exist under Lib at **f034c13 itself** and at 0216863: SingularHomology (MayerVietoris:853), singularHomologyMap (:856), circleProductHomologyEquiv (CircleProduct:798), circleSectionHomology (:562), circleProjectionHomology (:569), circleBoundaryCoordinates (:700), homeomorphHomologyEquiv (HomotopyInvariance:164), connectedHomologyZeroEquiv (:223), totallyDisconnected_homology_subsingleton (:233), crossProductHomology (CrossProduct:1689). The f034c13→0216863 diff changes only J.md and its receipt; the working tree has no tracked source differences.
- All **49 named API checks** in my main probe resolve after opening Mathoverflow1973 and ExteriorAlgebra: nine A seams, four cross-product/module-plumbing APIs, seventeen torus/coherence APIs, fourteen Pontryagin APIs, two exterior-coordinate APIs, and three Mathlib exterior-power APIs. This includes all fully spelled mathematical APIs in §Axis-5's principal rows; the four LocalSystemMatrices definitions were source-inspected separately. Ellipses and unnamed families cannot be exhaustively certified.
- Exterior-power notation is real pinned-Mathlib syntax. I independently proved `(⋀[ℤ]^n M) = ExteriorAlgebra.exteriorPower ℤ n M` by `rfl`; the three named exteriorPower APIs resolve with their genuine universes and typeclass binders. The notation itself is not a defect; missing qualification/context is.
- No claim of a full library build, axiom audit, proof correctness review, or aggregate production-module consumer certification is made. Existing compiled APIs were checked; source comparison establishes where their declarations live. No stale-olean collision occurred, so no rebuild was necessary.

## Checks actually run

All shell commands were run from `/home/ox-alpha/HopfProblem` unless specified. File reads and regex searches used the read/grep tools.

1. `git status --short && git rev-parse HEAD && git show 0216863:Lib/docs/J.md` — exit 0; HEAD matches the requested review commit; only pre-existing untracked `AGENTS.md` was shown.
2. `git diff 0216863 -- Lib/docs/J.md Lib/docs/J-INTERFACE_RECEIPT.md Lib/ Hopf/` — exit 0, empty. `git diff f034c13 0216863 --stat` — only two documentation files changed. `git branch --show-current` — `lib/textbook-extraction`.
3. `ps -eo pid,comm,args` — exit 0; another seat was running `lake build Lib Hopf.Final Solution S6Shortcuts Challenge`. I did not start a broad build.
4. Source read/grep census of `Lib/AlgebraicTopology/SingularHomology/{MayerVietoris,CircleProduct,CrossProduct,HomotopyInvariance}.lean`, `Hopf/LCP/{CuspFilling,Specialization,BoundaryTopology}.lean`, `Hopf/FiniteCore.lean`, and pinned Mathlib's ExteriorAlgebra/Basic and ExteriorPower/Basic. Outcomes and exact locations are given above. A first overly broad regex was narrowed; a first unqualified declaration regex missed names because declarations carry namespace prefixes.
5. `git grep -n -E '(abbrev SingularMayerVietoris.SingularHomology|def SingularMayerVietoris.singularHomologyMap|def SingularHomology.(circleProductHomologyEquiv|connectedHomologyZeroEquiv|homeomorphHomologyEquiv)|theorem SingularHomology.totallyDisconnected_homology_subsingleton|def PeriodTorusHigherHomology.crossProductHomology)' f034c13 -- Lib/AlgebraicTopology/SingularHomology` — exit 0, seam declarations present. This regex used `def` for singularHomologyMap, which is actually an `abbrev`; its existence/type were verified by direct source read and the successful Lean probe.
6. `sha256sum Lib/docs/J.md Lib/docs/J-INTERFACE_RECEIPT.md` — exit 0, hashes above. `git -c safe.directory='*' -C .lake/packages/mathlib rev-parse HEAD` — exit 0, `db584cd6d46c92f209a44c0f1c829460d327499d`.
7. Lean commands used this environment, without changing git configuration:

   ```sh
   export PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH
   export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
   lean --version
   lake env lean /tmp/J_review_devin_axis5.lean
   lake env lean /tmp/J_review_devin_universes.lean
   ```

   `lean --version`: exit 0, Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17.
   Both files were legacy probes importing **only** `Hopf.LCP.CuspFilling` and `Hopf.LCP.Specialization`.
   Main-probe progression: initial exit 1 for missing namespace context; after adding `open Mathoverflow1973 ExteriorAlgebra`, all 49 API checks resolve but the two Type* expressions fail; after changing only the two G binders to Type, exit **0**, with 49 API checks, two type-expression checks and the exterior-notation `rfl` check.
   Dedicated signature-only probe: exit **1**, reproducing both proposed Type* declaration failures with namespace and local-instance context already supplied. It used temporary `axiom product`/`axiom exteriorMap` signatures, not substantive proofs; nothing was added to the repository.

   Minimal reproduction of the first universe failure:

   ```lean
   import Hopf.LCP.CuspFilling
   import Hopf.LCP.Specialization
   open Mathoverflow1973
   namespace JReviewDevin
   attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
     PeriodTorusHigherHomology.integerTensorModule
   axiom product (G : Type*) [TopologicalSpace G] [AddCommGroup G]
     [IsTopologicalAddGroup G] (n : ℕ) :
     SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
     SingularMayerVietoris.SingularHomology G n →ₗ[ℤ]
     SingularMayerVietoris.SingularHomology G (n + 1)
   end JReviewDevin
   ```

8. Closeout: `rm /tmp/J_review_devin_axis5.lean /tmp/J_review_devin_universes.lean && git status --short && git diff --check && git rev-parse HEAD && sha256sum Lib/docs/J.md` — exit 0. Both reviewer-created probes removed; no oleans were emitted by these commands. HEAD and ledger hash remained unchanged; `git diff --check` was clean, and status still showed only the pre-existing untracked AGENTS.md.

No `lake update`, `lake exe cache get`, `lake build`, repo edit, commit, or push was performed. The pre-existing untracked AGENTS.md is left untouched.

## Return decision

Return to Axis 5 for exact signatures, namespace/visibility context, per-boundary ChallengeNodes and aggregate certification; return the general-n dependency gap to its owning earlier decomposition seam. The corrected `(1,n)` and GLM ownership decisions, real exterior-power syntax, and landed A/C base seams are useful progress, but they do not satisfy the protocol's GO criteria. Regenerate and independently review the corrected ledger hash before freezing any Axis-6 handoff.
