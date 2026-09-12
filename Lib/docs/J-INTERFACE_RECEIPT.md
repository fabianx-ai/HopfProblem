# Lane J — Interface Receipt

Seat: **Muse**. Head: `f034c13` (`lib/textbook-extraction`, = `upstream/lib/textbook-extraction`).
Toolchain: `leanprover/lean4:v4.33.0` via `/tmp/shared-lean-copy/toolchain-v4.33.0`,
mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## What was probed

Producer probe `Lib/AlgebraicTopology/SingularHomology/J_InterfaceCheck.lean`
(temporary, deleted after receipt — do not commit):

- 9 promised output signatures elaborated as `def`/`theorem` shells (`sorry` bodies):
  `productTorusHomologyEquiv`, `pontryaginProduct` (at `(1, n)` per the settled owner
  decision), `pontryaginTripleProduct`, `homologyWedgeTwo`, `latticeWedgeTwo`,
  `homologyWedgeThree`, `productTorusExteriorEquiv` (rank `r`, the 4→r generalization),
  `standardExteriorBasis`, `standardExterior_map_coefficient`.
- 34 `#check` commands resolving every external API name cited in the `J.md` ledger:
  `SingularMayerVietoris.{SingularHomology,singularHomologyMap}`,
  `SingularHomology.{circleProductHomologyEquiv,circleSectionHomology,
  circleBoundaryCoordinates,connectedHomologyZeroEquiv,homeomorphHomologyEquiv}`,
  `PeriodTorusHigherHomology.{crossProductHomology,integerBilinearPostcompose,
  productTorusHomologyEquiv,productTorusSuccHomeomorph,coordinateTorusBasis,
  productTorusTopClass,positiveCircleCross,circleBoundary_positiveCircleCross,
  coordinateTorusWedgeTwoEquiv,coordinateTorusH2ExteriorEquiv,
  surjective_of_coordinateTorusClassAlong_mem_range}`,
  `PeriodTorusHigherHomologyPontryagin.{product,product11,product11_skew,product11_self,
  tripleProduct,homologyWedgeTwo,latticeWedgeTwo}`,
  `PeriodTorusHigherHomologyExterior.{standardExteriorBasis,
  standardExterior_map_coefficient}`,
  `exteriorPower.{ιMulti,map,alternatingMapLinearEquiv}`,
  `Module.Basis.exteriorPower`, `Set.powersetCard.ofFinEmbEquiv`,
  `Pi.basisFun`, `Matrix.mulVecLin`.
- 2 representation-only composite checks: the `T^{r+1} ≃ₜ S¹ × T^r` homeomorph composed
  with the Künneth splitting `circleProductHomologyEquiv`
  (`H_{n+1}(S¹ × X) ≅ H_{n+1}(X) × H_n(X)`), and the `(1,n)` Pontryagin product as
  `integerBilinearPostcompose (crossProductHomology G G n) (singularHomologyMap
  (additionMap G) (n+1))` under the `integerLinearMapModule`/`integerTensorModule`
  `instance_reducible` local instances the implementation activates.

Consumer probe `Lib/AlgebraicTopology/SingularHomology/J_InterfaceConsumerCheck.lean`
(temporary, deleted after receipt — do not commit): exercises the promised signatures in
downstream call shapes — applying `productTorusHomologyEquiv 2 1` (`H₁(T²) ≅ ℤ²`),
evaluating `homologyWedgeTwo`/`latticeWedgeTwo` on `exteriorPower.ιMulti` decomposables,
using `productTorusExteriorEquiv 2 2` with the torsion-free hypothesis discharged by the
landed `productTorus_homology_torsionFree`, reading `standardExteriorBasis 4 2`
coefficients, and applying the minor formula `standardExterior_map_coefficient 4 2`.

## Commands and results

```text
$ lake env lean Lib/AlgebraicTopology/SingularHomology/J_InterfaceCheck.lean
exit 0 — 0 errors, 9 warnings (the 9 intentional `sorry` signature shells),
34 #check outputs all resolved, 163 output lines total.

$ lake env lean -o .lake/build/lib/lean/Lib/AlgebraicTopology/SingularHomology/J_InterfaceCheck.olean \
    Lib/AlgebraicTopology/SingularHomology/J_InterfaceCheck.lean
exit 0 (emits the producer olean so the consumer probe can import it).

$ lake env lean Lib/AlgebraicTopology/SingularHomology/J_InterfaceConsumerCheck.lean
exit 0 — 0 errors, 0 warnings.
```

## Environment notes discovered while probing

- The seeded `.lake/build` predates lanes A and C: `lake build Lib` (2 m 31 s, 8786 jobs)
  and `lake build Hopf.LCP.Specialization` were needed once to produce fresh oleans. The
  stale `Hopf.DifferentialTopology.olean` still carried pre-extraction
  `SmallChainBiprod.*` internals, which collided with `Lib.Algebra.Homology.
  MayerVietorisShortExact` under `lake env lean` until `Hopf` was rebuilt at head.
- `Lib` files are `module` files; `Hopf` files are legacy. A `module` probe cannot
  `public import` the legacy `Hopf.LCP.*` chain, and a legacy probe must not additionally
  import `Lib` modules already reached transitively through legacy Hopf imports (internal
  `_proof_*` decls double-arrive). The probes therefore import only
  `Hopf.LCP.CuspFilling` + `Hopf.LCP.Specialization`, whose transitive closure already
  contains every `Lib` module the ledger cites. Once the J targets land in `Lib`, the
  production files (pure `Lib`/`Mathlib` imports) do not have this constraint.
- `opaque` requires a `Nonempty` instance on the result type, so the `≃ₗ`/`Basis`/Prop
  signature shells use `sorry`-bodied `def`/`theorem` instead.
- `attribute [local instance] … in` cannot precede `example` or `section` directly;
  use a `section` wrapper as in the probe.

## Seam status at `f034c13`

- A (`Lib.Topology.Homotopy.*`, `Covering`, `SingularHomology` core) and C
  (`CrossProduct`, `CircleProduct`, `MayerVietoris`, `HomotopyInvariance`): **landed**,
  names verified above.
- The 42 cross-product coherence declarations in `Hopf/LCP/Specialization.lean`:
  **GLM-owned** (G-J3), not part of this lane's surface.
- General `(p, q)` Pontryagin product: deferred follow-up once C's general cross product
  lands; this lane ships `(1, n)` only.

## Axis-5 review

Stage-2 review of `Lib/docs/J.md` exists off-tree at `~/s6-notes/J-review.md`
(origin: kimi's review of the pre-revision ledger).

**First Axis-5 review — NO-GO** (seat `devin-axis5-j`, GPT-6 Astra, report at
`~/s6-notes/J-review-devin-axis5-j.md`, to be committed as
`Lib/docs/J-axis5-review.md`). Nine findings, all confirmed against the sources and
addressed by the second-pass `J.md` ledger:

1. The two proposed signatures used `G : Type*` against the universe-0
   `SingularMayerVietoris.SingularHomology`/`crossProductHomology` API → both now
   `G : Type`, and the ledger records the convention explicitly.
2. Namespace/elaboration context missing → new "Context and elaboration conventions"
   block records `namespace Mathoverflow1973`, the `ExteriorAlgebra` notation, the
   `integerLinearMapModule`/`integerTensorModule` local-instance requirement, the
   universe-0 convention, and the CHARGED-abbreviation exclusion.
3. ChallengeNode fields missing → every boundary J-A…J-E now carries
   `commit_boundary`/`imports`/`visibility`/`source`/`destination`/`focused_check`/
   `return_seam`.
4. General-`n` wedge descent lacked a typed dependency interface → narrowed to
   deferred boundary J-E with the missing inputs (`crossProductHomology'` at `(p,q)`,
   general-degree `swap'`/`associative'`) written out exactly.
5. The receipt did not certify `exteriorMap`/production `public` visibility → J-E
   carries the `exteriorMap` signature; `visibility` fields now state `module` +
   `public` per boundary; second-pass probes in the production context are landing
   work per boundary.
6. Ownership wording ("J appends G-J3") and the "42" count → corrected; ~90-decl
   exclusion manifest is now exact and includes the `integerTrilinear*`/
   `chainTrilinearLift` cluster (used only by the associator machinery).
7. Dependency order → J8 before J7; build order updated.
8. Source coordinates → off-by-ones fixed (singularHomologyMap :856, rightTranslation
   BoundaryTopology:14298, `formalMap_comp` 3771, `succ_pair` 6439, etc.).
9. Literal `…`s in promised signatures → all public outputs now carry complete
   signatures (binders, instances, universes, codomains); internal movers are
   name+line manifests.

**Second Axis-5 review — NO-GO** (same seat, report at
`~/s6-notes/J-review2-devin-axis5-j.md`, committed as
`Lib/docs/J-axis5-review2.md` alongside the first). Eleven findings; the J-A-relevant ones were: wrong
`reindex` direction, `.repr`/function-space mismatch, and no second-pass
aggregate receipt. Both de-pinned wedge constructors passed the reviewer's own
probes.

This receipt documents the **first-pass** probes only for boundaries
J-B…J-E; J-A now has its own second-pass certification below.

## Second-pass certification — Boundary J-A (J-A only)

Probe: temporary file `/tmp/JA_Probe.lean` (deleted after this receipt —
do not commit). Production context: `module` header, `public` visibility on
every promised output, Mathlib imports only:

```lean
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Hom.PowersetCard
public import Mathlib.Data.List.Lex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fintype.Pi
```

Probe namespace `HopfLib.JA` (signatures are namespace-independent; the ledger
lands them under `Mathoverflow1973.PeriodTorusHigherHomologyExterior`).

Command: `lake env lean /tmp/JA_Probe.lean` → **0 errors**, 2 warnings
(the two remaining `sorry` bodies `exteriorPowerMap_toMatrix` and
`cauchyBinet_minors`, which are Axis-6 proof obligations with stated recipes —
their *statements* elaborate).

**Compiled, fully proved (no `sorry`):**

- `SortedSubset`, its `Fintype` and `LinearOrder` instances (lex-on-sorted-
  tuple order via `LinearOrder.lift'` to `List`'s computable lex order);
- `sortedSubset_card` (`Fintype.card = m.choose n`);
- `powersetCardFinEquiv` — concrete construction `toLex.trans
  ((subtypeUnivEquiv mem_univ).symm.trans (orderIsoOfFin univ h).symm.toEquiv)`;
- `powersetCardFinEquiv_lt_iff` — the pinning characterization
  `e s < e t ↔ List.Lex (sorted s) (sorted t)`, **proved**;
- `standardExteriorBasis`, `standardExteriorBasisFin` (correct reindex
  direction: `.reindex (powersetCardFinEquiv m n)`, no `.symm`),
  `standardExteriorCoordinates` (`.equivFun`, not `.repr`);
- `exteriorPower_finrank_choose` — **proved** via Mathlib's
  `exteriorPower.finrank_eq` + `Module.finrank_fintype_fun_eq_card`;
- `exteriorMinorMatrix` (rectangular `p m n`), `exteriorPowerMap`,
  statements of `exteriorPowerMap_toMatrix` and `cauchyBinet_minors`.

**Failed checks (recorded honestly):**

- `by decide` does **not** evaluate `powersetCardFinEquiv` (the
  `orderIsoOfFin` inverse threads through `List.Sorted.getIso`/`Equiv`
  machinery the kernel cannot reduce); `native_decide` is blocked because
  `Set.powersetCard.ofFinEmbEquiv` is not `meta`-accessible in module context.
  Consequence written into the ledger: the `pairSubset`/`tripleSubset`
  compatibility equation is proved *order-theoretically* — via
  `powersetCardFinEquiv_lt_iff`, `pairSubset_ordered`, and strict-mono
  uniqueness on `Fin k` — not by `decide`.
- `Decidable (s ∈ Set.powersetCard (Fin m) n)` is not an instance; test
  terms use `Set.powersetCard.ofCard`/`mem_iff.mpr`.

**Scope:** certifies J-A's interface only. J-B, J-C, J-D, J-E are **not**
certified by this probe — the reviewer's findings there (proof-dependency
boundary splits, `FirstHurewicz` shim aliases, degree-three completeness,
GLM manifest count, J-E transports) remain open until each boundary gets its
own probe.

### J-A landing (Axis 6)

`Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean` landed after the
review-3 GO, with **all 15 manifest nodes and real proofs** — including
`standardExterior_map_coefficient` (ported verbatim from Specialization:6641),
`exteriorPowerMap_toMatrix` and `cauchyBinet_minors` (proved via the recorded
recipes: `toMatrix_apply` + `basis_apply`/`map_apply_ιMulti_family`/
`ιMultiDual_apply_ιMulti` + `det_transpose`; and `map_comp` + `mulVecLin_mul` +
`toMatrix_comp` respectively). The source copies of `standardExteriorBasis`/
`standardExterior_map_coefficient` were deleted from `Hopf/LCP/Specialization.lean`
(which now imports the Lib module — same FQN, seamless reroute for
`BoundaryTopology` consumers). The rank-4 `pairSubset`/`squareBasis`/etc.
adapters remain in Hopf pending their order-theoretic compat proofs, per the
review-3 amendment.

M-C seam repair in the same change: `CrossProduct.lean`, `PathClass.lean` and
`CrossInsert.lean` converted to `module` + `public import` +
`@[expose] public noncomputable section`; `PathClass`'s stale `CylinderHEP`
import dropped (unused — `CylinderHEP`'s legacy cone stays for the Morse lanes).
`lake build Lib ... Hopf.LCP.Specialization Hopf.LCP.BoundaryTopology`:
8811 jobs, green.

## Review-3 certification and repairs — devin-axis5-j

**J-A: GO for the amended 15-node Mathlib-only packet. J-B..J-E: NOT GO.**
The earlier historical claims that every boundary was fully aligned, or that
certification could wait until landing, are superseded by this section.

Base HEAD: `15bd5f7a6f482881fc47e6d5e933409cae101690`, branch
`lib/textbook-extraction`. This receipt covers **uncommitted reviewer amendments**
to J.md, not the original file at that commit. Reviewed ledger SHA-256:
`d4b3724ec6d2edece110470e091ef8124be0581bd959bb6e89eea722b0ba646a`.
Toolchain: Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`;
Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.

All commands used:

```sh
export PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
```

### J-A aggregate provider and consumer

Provider `/tmp/J3A.lean`: real `module`, `public import Mathlib`, public declarations
in **Mathoverflow1973.PeriodTorusHigherHomologyExterior**, noncomputable section.
It reconstructs the concrete SortedSubset/Lex order, cardinality equivalence, its
strict-order characterization, basis reindexing, equivFun coordinates, finrank,
rectangular minor matrix and exterior map. It has **15 nodes / 15 public outputs**,
including named `sortedSubsetFintype` and `sortedSubsetLinearOrder` instances.
The three substantive theorem interfaces (`standardExterior_map_coefficient`,
`exteriorPowerMap_toMatrix`, `cauchyBinet_minors`) use temporary **axiom shells**;
no proof of those results is claimed by the interface probe. All other constructors
and the order/finrank representation results have actual terms. **37 external API
#checks** resolved. The consumer imports only J3A and checks **all 15 outputs by
fully qualified name**, including the instance outputs.

```sh
lake env lean /tmp/J3A.lean
# final construction check: exit 0
lake env lean -R /tmp -o /tmp/J3A.olean /tmp/J3A.lean
# final aggregate provider: exit 0
LEAN_PATH=/tmp lake env lean /tmp/J3AConsumer.lean
# separate module consumer: exit 0; 15/15 public names import-visible
```

The last provider/consumer pair was rerun together after the final API census;
both exited 0. `LEAN_PATH=/tmp` is a process-local addition; `lake env` adds the
project/package paths. All emitted artifacts were under /tmp, not package directories.

Provider SHA-256: `6ed3ba129a664fbe8383cb3a44e51b3871c255ef7f69b7e6726a296a9f4659a9`.
Consumer SHA-256: `35c9cea9a8a6cccd7b67c5edbf2a67c6532c5a273c5c79a1d9fdd02c9bbfcaa5`.
Boundary list: **J-A only**. Node/dependency/consumer metadata is now in J.md's
J-A ChallengeNode manifest. The two instances have explicit landing names.
The old rank-four subset/coordinate adapters are retained in Hopf until their
order-theoretic compatibility proofs and consumer reroutes land; they are not
part of this Mathlib-only output packet. No kernel evaluation of the enumeration
or native_decide was used in review 3.

Failed reconstruction attempts, not hidden: the first provider attempt exited 1
because a direct simp did not identify Fintype.card across Lex, and the attempted
`change` left orderIsoOfFin cardinality proofs unresolved. The successful construction
uses `Fintype.card_congr toLex.symm` and unfolds powersetCardFinEquiv before applying
OrderIso.lt_iff_lt. Those concrete recipes are reflected in J.md. These were probe
construction errors, not counterexamples to the pinned enumeration.

### J-B/J-C/J-D/J-E changed-signature checks

`/tmp/J3Interfaces.lean` initially tried the advertised production imports, including
CrossProduct, and **exited 1**: `cannot import non-module
Lib.AlgebraicTopology.SingularHomology.CrossProduct from module`.
Source inspection confirmed `CrossProduct.lean:6–9` has no module header;
PathClass is also legacy. This is the new **M-C** seam, not a stale-olean diagnosis.
No rebuild, package update, cache fetch or clean was attempted.

The final **provisional** module instead imports Mathlib, MayerVietoris,
CircleProduct, HomotopyInvariance and Hurewicz.Degree1. It uses the real public
SingularChains/SingularHomology/AlgebraicTopology APIs, reproduces the two
instance-reducible module definitions in an isolated support namespace, and uses
**46 temporary axiom signatures** for proposed/unlanded prerequisites and outputs.
This is explicitly **not** certification of those production providers.

```sh
lake env lean /tmp/J3Interfaces.lean
# final provisional module check: exit 0
```

It checks **21 real external API names with Lib imports alone**, and proves by rfl
that AlgebraicTopology.SingularH1 and its map agree with the chosen degree-one
SingularMayerVietoris type/map. Changed/new signature shapes checked together:

- J-B2: canonical H1 definition/basis/single/apply/basis-hit/surjective/natural/
  bijective/equiv types; public torusMatrixMap, coordinatePeriodLoop, torusTailMap/add,
  coordinateTorusMapAlong_add (only `[Add G]`, preserving the source's generality),
  canonical matrix-on-loop and top-class-one types; chain-complex references in
  positiveCircleCross_arcSum_cycleClass use SingularChains, not a shim alias.
- J-C3: complete de-pinned wedgeThreeAlong_natural; the product-valued successor
  top-class signature now assigned to Pontryagin rather than Torus.
- J-D: all eleven formerly prose-only degree-three declarations; the corrected
  degree-two coordinate matrix signature uses exteriorMinorMatrix **r r 2**, and
  degree three uses **r r 3**. No rank-four PeriodDomain input is introduced.
- J-E: actual homologyDegreeCast term and reflexive rfl law; corrected homeomorphism
  coercion, swapped-degree transport and associator-degree transport. The two
  general coherence propositions elaborate over an abstract general cross product.

An intermediate run after adding homologyDegreeCast exited 1 because the definition
needed `noncomputable`; adding that qualifier produced the final exit 0. The
substantive H1 basis-hit/apply proofs and general coherence proofs were not built.
Provisional-probe SHA-256:
`5ca04adc645c75cd40d8b0d48ae2b7dfc2a0f6d02f51d47f68ba19235bf09fbd`.

| Boundary | Certification status |
|---|---|
| J-A | GO, amended 15-node provider/consumer packet at the ledger hash above |
| J-B1 | NOT GO: source proof-closure census repaired; complete helper/node census and aggregate core consumer still needed |
| J-B2a | NOT GO: coordinate/circle signature repairs checked provisionally; S-path, S-nat, S-cross and M-C not public/green |
| J-B2b | NOT GO: canonical H1 signatures checked; basis-hit, arbitrary-vector loop identity and old/public loop-class alignment remain mathematical/representation seams |
| J-C1/J-C2 | NOT GO: M-C/S-cross; source APIs exist, but not in the advertised production module context |
| J-C3 | NOT GO: new wedge/top-class signatures checked provisionally; G-J3, J-B2a and public provider dependencies remain |
| J-D | NOT GO: new degree-three and rectangular-matrix signatures checked provisionally; depends on J-B2b/J-C3 |
| J-E | Deferred NOT GO: corrected transport signatures checked; general cross product, unit/recursion, alternation and basis-image inputs remain unimplemented |

### Source census and working-tree receipt

The GLM census was scripted rather than inferred from prose families:

```sh
git show 15bd5f7:Hopf/LCP/Specialization.lean | python3 -c 'import sys,re; rows=[(i,re.match(r"^(?:noncomputable )?(?:theorem|def|lemma|instance|abbrev) (PeriodTorusHigherHomology\.[^\s({:]+)",s)) for i,s in enumerate(sys.stdin,1) if 3771<=i<=5987]; rows=[(i,m.group(1)) for i,m in rows if m]; print("count",len(rows)); print("\n".join(f"{i} {n}" for i,n in rows))'
```

Exit 0: **110 declarations**, including chainTrilinearMap_ext:4434. The manifest's
postcompose/precompose apply locations are 4314/4350. Source proof reads and searches
also established the wider circle naturality closure 14325–14505 and path closure
13348–13698, the torusMatrixMap definition at 2488, and the product-type dependency
at Specialization 3646. Every J-B1 output was reclassified against its source proof
closure; coordinate/loop work no longer rides on the recursive core's green claim.

All requested known source-coordinate errors were corrected. `git diff --check`
passed. Only J.md and this receipt are intended tracked edits; pre-existing untracked
AGENTS.md is untouched. No Lean implementation, committed axiom/sorry, package write,
commit or push is part of this work. The working tree is intentionally **not clean**:
Muse requested uncommitted documentation repairs.

Closeout command:

```sh
rm /tmp/J3A.lean /tmp/J3AConsumer.lean /tmp/J3Interfaces.lean /tmp/J3A.olean \
  /tmp/J3A.olean.private /tmp/J3A.olean.server /tmp/J3A.ir /tmp/J3A.ir.sig
git diff --check
git status --short
git rev-parse HEAD
sha256sum Lib/docs/J.md
```

Exit 0: all reviewer-created probes and emitted provider artifacts removed; HEAD
unchanged at 15bd5f7. Tracked edits are only J.md and this receipt; the pre-existing
untracked AGENTS.md remains. The final ledger hash is the one recorded above.
The final change after the last producer/consumer compile only clarified J-D's
rank-four compatibility comment; it did not alter any signature or J-A packet.
