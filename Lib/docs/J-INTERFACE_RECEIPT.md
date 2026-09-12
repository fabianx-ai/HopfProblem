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
