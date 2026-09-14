# Lane J — third Axis-5 review and uncommitted repairs

**J-A verdict: GO for the amended 15-node Mathlib-only interface.**
**Whole-lane verdict: NO-GO. J-B, J-C, J-D and J-E are not certified.**

Reviewer/fixer: **Devin, seat `devin-axis5-j`** (same reviewer as passes 1 and 2).
Base HEAD: `15bd5f7a6f482881fc47e6d5e933409cae101690`, branch `lib/textbook-extraction`.
Reviewed amended `Lib/docs/J.md` SHA-256:
**`d4b3724ec6d2edece110470e091ef8124be0581bd959bb6e89eea722b0ba646a`**.

This verdict concerns the working-tree amendments, not the original receipt at 15bd5f7. Muse should review and commit the documentation; I made **no commit or push**. A subsequent change to the J-A packet requires updating its hash/certification. No Lean implementation or package files were edited.

## Review basis

I read the collaboration protocol, the Stage-5/GO requirements, both prior reports in-tree, the current Axis-5 ledger and the new J-A receipt. HEAD matched the requested commit; the tree initially had only the pre-existing untracked AGENTS.md. I independently reconstructed J-A rather than relying on the reported probe results. I inspected source proofs for the J-B split and scripted the G-J3 declaration-start census.

## Numbered findings, repairs and limits

1. **J-A construction passes; its incomplete handoff was repaired.**
   `Lib/docs/J.md:422–653`; receipt `Lib/docs/J-INTERFACE_RECEIPT.md:197–259`.
   The repaired forward reindex direction and `.equivFun` codomain are correct. I reconstructed the actual SortedSubset/Lex linear order, finite-cardinality equivalence, `powersetCardFinEquiv_lt_iff`, basis, coordinate map, rectangular exteriorMinorMatrix/exteriorPowerMap, and finrank proof in a Mathlib-only module. The order characterization and finrank statements have actual proofs in that probe. The three substantive theorem signatures use temporary axiom shells, as appropriate to interface checking, not invented mathematical proofs.

   The original new receipt still lacked a separate importing consumer and a complete node manifest. I added explicit instance names, the exact destination namespace, a 15-row inherited ChallengeNode manifest, and an aggregate consumer check. **All 15 outputs, including both instance outputs, resolve from the separately compiled consumer.** The final provider checks 37 named external APIs. This closes the J-A portions of the receipt, representation and metadata findings. GO is scoped to this library interface only.

2. **J-A coordinate pinning is mathematically sound; premature adapter deletion was contradictory.**
   `J.md:477–653`.
   The lex-on-sorted-subsets characterization fixes the enumeration rather than allowing an arbitrary basis permutation. The order-theoretic rank-four compatibility recipe is appropriate: the explicit pair/triple index enumerations are lex-ordered, and a strictly monotone endomap of the corresponding Fin type is the identity. No kernel computation of the noncomputable enumeration is needed.

   However, the ledger simultaneously said pairSubset/tripleSubset stay as charged adapters and said to delete them at J-A landing. I repaired the disposition: **retain the old Hopf subset/coordinate adapters until their compatibility equations and consumer reroutes land**. They are not outputs of the Mathlib-only J-A packet. I did not prove those downstream compatibility adapters. I also clarified that J-D's agreement with LocalSystemMatrices needs those compatibility equations, not just the generic minor formula.

3. **Shim-only names were replaced; a real module-provider blocker remains.**
   `J.md:389–420`; source `Hopf/LibShims.lean:37–45,69–71`, `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean:6–9` and `PathClass.lean:6–18`.
   Removed all FirstHurewicz references from J.md. The degree-one target interface is now AlgebraicTopology.SingularH1, AlgebraicTopology.SingularH1.map and AlgebraicTopology.Hurewicz.loopHomologyClass. Chain-complex references use SingularChains.singularComplex. The context explicitly opens SingularHomology for its real circle/point/equivalence APIs and records Matrix/BigOperators/TensorProduct scopes and the noncomputable section. Twenty-one real API checks resolve with **Lib imports alone**, and the chosen degree-one type/map bridges to SingularMayerVietoris are `rfl`.

   A production module probe nevertheless rejects importing CrossProduct: it is a **legacy file even though its path begins Lib/**. PathClass is also legacy. I recorded **M-C**, the public-module provider seam, instead of misdiagnosing this as stale oleans or attempting a package-affecting rebuild. J-C1 cannot be called production-green merely because its source mathematical API exists. The later provisional module copied the exact two instance-reducible definitions into an isolated support namespace; that checks types, not availability of the real provider.

4. **J-B's split now follows proof closure; the Torus/Pontryagin cycle is removed from the plan.**
   `J.md:322–328,655–1074`.
   J-B1 now contains only the recursive torus/Pascal/homology/top-class core. I recorded its source proof inputs, not merely its statement types. Coordinate maps/bases/Along work moved to **J-B2a**, and the rank-general H1 identification work to **J-B2b**. J-B1 is a candidate, not a certified aggregate packet.

   The concrete missed edge is:
   `coordinateTorusBasis_apply` (Specialization 6498) → `productTorusHomologyEquiv_coordinateTorusClass` (6459) → `circleCoordinates_coordinateTorusClass_take` (6428) → `circleProductHomologyEquiv_naturality` (CuspFilling 14480).
   The full **S-nat** closure is 14325–14505, not the separate cross-product naturality trio. **S-path** reaches 13348–13698, including translation and later section lemmas. **S-cross** is the cross-product naturality closure at 14509–14576. All are now explicit blocked seams.

   `productTorusTopClass_succ_product` at Specialization 3646 mentions Pontryagin.product in its type. It and the product-dependent helpers are assigned to **J-C3 in Pontryagin**, after Torus; Torus never imports Pontryagin. I wrote its canonical target signature and the previously untyped public helper signatures. The early torusMatrixMap definition/dependency cluster at 2464/2481/2488 is now recorded rather than mistaken for the later matrix recursion.

5. **The rank-general H1 gap is explicit, typed, and still a real gap.**
   `J.md:833–956`.
   The desired naturality statement now names a real map API. But `torusMatrixMap_coordinatePeriodHomology` alone does not identify the loop class of an arbitrary matrix column with coordinateH1 of that column. I added exact, provisionally elaborated missing-input signatures:
   - `coordinateH1_basis_hit`: every degree-one coordinateTorusClass lies in the coordinateH1 image;
   - `coordinateH1_apply`: coordinateH1 of an arbitrary integer vector equals the canonical coordinate-loop homology class.

   Natural transformation and surjectivity recipes are conditional on these inputs, not falsely labelled green. The general loop identity and basis-hit proof require earlier mathematical/representation alignment; simply using `map_zsmul` does not prove them. The old/public loop-class proof interface also needs alignment. I did not construct those substantive proofs in an Axis-5 repair task. They gate J-B2b and J-D.

6. **The missing degree-three public signatures are now explicit.**
   `J.md:1312` onward and `1448–1598`.
   Wrote the complete de-pinned wedgeThreeAlong_natural declaration and all eleven previously commented degree-three J-D declarations, with binders, instances, result types, source locations and stated dependencies. Their signature shapes passed the provisional module probe together. Preserved the source's `[Add G]` generality for coordinateTorusMapAlong_add rather than unnecessarily strengthening it to a topological abelian-group assumption.

   I also fixed a fresh integration error caused by J-A's rectangular API: the degree-two matrix law now calls **exteriorMinorMatrix r r 2 A**; degree three uses **r r 3**. Both signatures elaborate. These results remain blocked by the real J-B2b/J-C3 providers; provisional axiom inputs are not evidence that the mathematical proofs already exist.

7. **GLM manifest regenerated: 110 declarations, including the omitted extensionality lemma.**
   `J.md:1705–1767`.
   The scripted declaration-start census confirms **110** PeriodTorusHigherHomology declarations in Specialization 3771–5987, excluding the interleaved Pontryagin namespace. Added chainTrilinearMap_ext:4434 and its call sites 5094/5447/5478; corrected integerTrilinearPostcompose_apply to 4314 and integerTrilinearPrecompose_apply to 4350. The trilinear helpers' non-self call sites are indeed confined to the associator machinery, so GLM ownership remains correct. No J implementation is authorized to absorb this suite.

8. **J-E transport errors are fixed, without claiming the deferred mathematics.**
   `J.md:1600–1703`.
   Added an actual representation-only noncomputable homologyDegreeCast and its reflexive identity. The swap uses the real coercion of Homeomorph.prodComm to a continuous map and transports q+p to p+q. Associativity transports p+(q+r) to (p+q)+r. Both repaired coherence statements elaborate in a module over a signature-only general cross product. J-E still needs the general product, unit/recursion, alternation and basis-image interfaces/proofs; its metadata explicitly says deferred NOT GO.

9. **Known source locations corrected; historical ranges distinguished.**
   Corrected the requested declaration starts: 14986; 3417; 15016/15020/15025/15030/15035; 14325; 6031/6039/6047; 6189; 7009/7037/7051; 4314/4350; 2488. Also corrected the degree-two apply-ιMulti source to 6964 and gave degree three's actual 6976 location. FiniteCore's relevant range is 328–338. The earlier Axes-2/3 broad ranges are now explicitly historical pre-extraction ranges, not claimed current source locations. No stale FirstHurewicz, toContinuousMap, ~90 or requested incorrect declaration-coordinate strings remained in the final targeted scan.

10. **The remaining handoff limits are explicit rather than hidden behind GO.**
    `J.md:342–350`; receipt `:306–315`.
    J-A has the complete amended manifest and aggregate provider/consumer result. J-B1 still needs its full helper/node signature census and aggregate core consumer. J-B2/C/D need public/green seam providers and substantive H1 alignment; J-E remains deferred. The source-closure inventory for blocked implementation helpers is not a complete frozen Challenge. I therefore do not certify that the whole remaining lane is executable from the ledger. The receipt now records those per-boundary distinctions, and says certification precedes implementation rather than being “landing work.”

## Checks actually run

All project commands ran from `/home/ox-alpha/HopfProblem`. Environment:

```sh
export PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
```

- `git status --short`, `git rev-parse HEAD`, `git diff 15bd5f7 -- Lib/docs/J.md Lib/docs/J-INTERFACE_RECEIPT.md`, and `git diff bdbbb02 15bd5f7 --stat`: expected HEAD, initially no tracked changes; Muse's repair was documentation only.
- Source read/grep tools: prior reports, ledger/receipt, Hopf/LibShims, CuspFilling recursive torus and circle closures, Specialization matrix/coordinate/Pontryagin dependencies, Lib module headers and Mathlib sorting APIs. The proof closures and source coordinates above are independently checked, not copied from Muse's summary.
- Scripted census, exit 0:

  ```sh
  git show 15bd5f7:Hopf/LCP/Specialization.lean | python3 -c 'import sys,re; rows=[(i,re.match(r"^(?:noncomputable )?(?:theorem|def|lemma|instance|abbrev) (PeriodTorusHigherHomology\.[^\s({:]+)",s)) for i,s in enumerate(sys.stdin,1) if 3771<=i<=5987]; rows=[(i,m.group(1)) for i,m in rows if m]; print("count",len(rows)); print("\n".join(f"{i} {n}" for i,n in rows))'
  ```

  Result: 110 excluded declarations, exact declaration lines.
- `lake env lean /tmp/J3A.lean`: first reconstruction exit 1 for Lex-cardinality simplification and unresolved proof arguments; corrected concrete construction exit 0. These failed attempts are recorded in the receipt.
- `lake env lean -R /tmp -o /tmp/J3A.olean /tmp/J3A.lean`: **final exit 0**, 15 public outputs, 37 external API checks. The provider has a module header, imports Mathlib only, and uses the exact landing namespace. Three substantive theorem bodies are temporary axiom shells; representation constructions/order/finrank have real terms.
- `LEAN_PATH=/tmp lake env lean /tmp/J3AConsumer.lean`: **exit 0**, separate module import, 15/15 fully qualified public outputs checked. The final provider and consumer were rerun together after the final API census. No same-file-only visibility shortcut.
- `lake env lean /tmp/J3Interfaces.lean`: initial actual-provider attempt **exit 1** on legacy CrossProduct import. The revised **provisional** Lib-only module, with isolated copies of the module-instance support and **46 typed axiom prerequisites/outputs**, eventually **exited 0**, including 21 real public API checks and three rfl/representation checks. An intermediate transport definition needed `noncomputable`; that failure and correction are recorded. This probe does not certify the missing production providers.
- `lake env printenv LEAN_PATH`: confirmed the seeded project/package search path. The /tmp consumer path was added process-locally.
- `git -c safe.directory='*' -C .lake/packages/mathlib rev-parse HEAD`: db584cd6d46c92f209a44c0f1c829460d327499d. `lean --version`: Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17.
- `git diff --check`: passed during editing and at closeout. `git diff --name-only`: only Lib/docs/J.md and Lib/docs/J-INTERFACE_RECEIPT.md. HEAD stayed at 15bd5f7; AGENTS.md remains pre-existing and untouched.

All probe results were recorded in the receipt before cleanup. Removed exactly these reviewer-created files/artifacts:

```sh
rm /tmp/J3A.lean /tmp/J3AConsumer.lean /tmp/J3Interfaces.lean /tmp/J3A.olean \
  /tmp/J3A.olean.private /tmp/J3A.olean.server /tmp/J3A.ir /tmp/J3A.ir.sig
```

Cleanup exited 0. No lake build was started (so no shared-box build load), and no lake update, cache get, clean, package write, commit or push was performed. The final documentation tree is deliberately dirty as requested. The last post-compile ledger change merely clarified J-D's rank-four compatibility comment; no signature or J-A interface changed.

## Deliverables and next boundary

Uncommitted tracked edits:
- `Lib/docs/J.md`: J-A manifest and scoped GO, canonical API context, proof-derived boundary split, explicit degree-three/H1/transport signatures, corrected GLM census and source coordinates.
- `Lib/docs/J-INTERFACE_RECEIPT.md`: aggregate J-A producer/consumer certification, per-boundary provisional results, failed-check history, hashes and cleanup.

Recommended next step after Muse reviews these amendments: execute **J-A only** from the exact 15-node packet. Separately obtain owner-approved public providers for M-C/S-path/S-nat/S-cross/G-J3, and align the missing rank-general H1 identities. Do not start J-D or general-n J-E on the strength of the J-A GO.
