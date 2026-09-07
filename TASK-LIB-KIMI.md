# TASK LIB-KIMI — generalize-then-move lanes C, J, E2, F, G

**TruthSeed:** `lib-extraction:generalize-the-pinned-dimensions`
**For:** Kimi, working on a fork of github.com/fabianx-ai/HopfProblem, branch
`lib/textbook-extraction` (base commit 721fc82; toolchain
leanprover/lean4:v4.33.0; Mathlib pinned in lake-manifest.json).
**Nature:** GENERIC library extraction, upstream-shaped. Mathematics for the
commons: Mathlib-shaped paths and names, a docstring on every public
declaration, no project vocabulary inside `Lib/`. Read `lean-protocol.md`
(repository root) and `Lib/README.md` FIRST and follow them. Your lanes are
*generalize-then-move*: a hand-unrolled or dimension-pinned proof becomes one
theorem at textbook generality. That is new mathematics in the sense of the
protocol, so the full seven-axis cycle applies: Axis 1 textbook file with the
complete proof of the general statement (`Lib/docs/<lane>.md`, ordinary
mathematics, no Lean names), Axis 2–3 additive decomposition in dependency
order, Axis 4 placement, Axis 5 exact typed ledger with the disposable
`*_InterfaceCheck.lean` producer/consumer probes and their receipt, and only
then Axis 6 Lean. `Lib/EXTRACTION_PLAN.md` §2 has every source line range on
721fc82 and every target file; §3 the validation recipe; §7 the hazards.

## Your lanes, in execution order

### Lane C — the Hurewicz theorem in every degree (Hatcher Thm 4.32) — starts when GLM's lane A has landed
- Source: `Hopf/Hurewicz.lean` 85–540, 1479–2144, 2152–3818, 3840–8301 (degree 2),
  8306–14990 (degree 3), 15000–23314 (general-n machinery and degrees 4, 5),
  23444–23654; `Hopf/Recognition.lean` 112–1550 (degree 6), 1737–1955 (cube → sphere),
  2334–2579 (cell filling), 3816–4044 (Hopf degree theorem).
- Targets: `Lib/AlgebraicTopology/Hurewicz/{SimplexCube,HomotopyExtension,
  PrismOperator,Straightening,CubeTriangulation,CubeGluing,Subdivision,
  CubeChainDecomposition,Degree,HopfDegree,CubeSphere}.lean`,
  `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`,
  `Lib/Topology/Homotopy/CellFilling.lean`.
- Textbook statement: for n ≥ 2 and an (n−1)-connected space X (simply connected
  with π_k(X) = 0 for 2 ≤ k < n), the Hurewicz homomorphism π_n(X, x) → H_n(X; ℤ)
  is an isomorphism (Hatcher Thm 4.32). Supporting textbook results moved at
  full generality: Δⁿ ≅ Iⁿ carrying boundary to boundary; the homotopy
  extension property of (Δⁿ, ∂Δⁿ) (Prop 0.16); the prism operator for a
  face-compatible family of simplex homotopies (Thm 2.10 in family form); the
  Freudenthal–Kuhn triangulation of Iⁿ into n! simplices indexed by
  permutations; the decomposition [p] = Σ_e sign(e)·[p ∘ σ_e] of a based n-cube
  in π_n; the chain identity [Iⁿ] = Σ_e sign(e)·σ_e; the Hopf degree theorem
  (Cor 4.25); the singular cross product H₁ ⊗ H_n → H_{n+1}.
- What is pinned today and must be generalized: the theorem exists as five
  independent copies (`SecondHurewicz`, `ThirdHurewicz`, `FourthHurewicz`,
  `FifthHurewicz`, `SixthHurewicz`) at n = 2, 3, 4, 5, 6 with identical shape
  `hurewiczLinearEquiv (x) [SimplyConnectedSpace X] [Subsingleton (π_ k X x) for
  2 ≤ k < n] : Additive (π_ n X x) ≃ₗ[ℤ] SingularHomology X n`. The general-n
  machinery already exists (`HigherHurewicz.*`, about 7,700 lines). The two
  missing general pieces are `cubeChain_eq_sum_simplices` for all n (now only
  n = 4 in `FourthHurewicz.CubeSubdivision` and n = 5 in `FifthHurewicz`) and the
  recursive construction of the normalization homotopy tower (now unrolled per
  degree). Expect to delete about 14,000 of the 25,000 lines.
- Consumers: `Hopf.Recognition` (the six-sphere instances `Degree.Sphere.pi*_subsingleton`,
  `SpecialPeriods.Threefold.Homotopy*`, `Degree.threefoldHomotopyEquiv` — its
  statement is unchanged; only its proof re-routes), `Hopf.LCP.IntegralHomology`.
- Axiom probe: the general `hurewiczLinearEquiv` and its n = 6 instance.
- Hazards: the two `@[instance_reducible]` local instances
  `PeriodTorusHigherHomology.integerLinearMapModule` / `integerTensorModule`
  (Hurewicz 2153, 2159) are re-attached to about 100 declarations of the cross
  product block; reproduce them or fix the ℤ-module diamond first and say which.

### Lane J — homology of tori, Pontryagin product, exterior-power coordinates (Hatcher Ex 2.48, Cor 3.28, §3.C) — after A (and your C if the rank-4 block uses the cross product)
- Source: `Hopf/LCP/CuspFilling.lean` `PeriodTorusHigherHomology.*` 13745–15977;
  `Hopf/LCP/Specialization.lean` `PeriodTorusHigherHomology.*` 2463–8499 (rank 4),
  `PeriodTorusHigherHomologyPontryagin.*` 3142–6154,
  `PeriodTorusHigherHomologyExterior.*` 6636–6882; `Hopf/FiniteCore.lean` 339–392.
- Targets: `Lib/AlgebraicTopology/SingularHomology/{Torus,TorusExterior,Pontryagin}.lean`,
  `Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean`.
- Textbook statement: H_n((S¹)ʳ; ℤ) ≅ ℤ^{C(r,n)}, by induction on r with the
  S¹ × Y splitting; the Pontryagin product on H_*(G) of a topological abelian
  group and the induced map ⋀ⁿ H₁(G) → H_n(G) (Thm 3C.5); the standard basis of
  ⋀ⁿ(Fin m → ℤ) and the minor-determinant formula for the induced map of a
  matrix; for a torus, H_n(Tʳ) ≅ ⋀ⁿ H₁(Tʳ).
- Generalize: the Specialization block is pinned to rank 4 through
  `Lattice := Fin 4 → ℤ`; restate for arbitrary r. An equivalent formalization of
  the minor formula exists outside this tree (decision Q4); move as-is, note it.
- Consumers: `Hopf.LCP.IntegralHomology`, `Hopf.LCP.BoundaryTopology`,
  `Hopf.LCP.Specialization`, `Hopf.FiniteCore`, `Hopf.Recognition`.
- Axiom probe: `PeriodTorusHigherHomology.productTorusHomologyEquiv`.

### Lane E2 — transversality, general position, isotopy extension, Whitney immersion/embedding (Hirsch Ch. 2–3, 8; Guillemin–Pollack Ch. 2; Milnor TDV §2–3) — after GLM's D1
- Source: `Hopf/DifferentialTopology.lean` 9043–9396, 9974–10223, 17206–17544,
  20996–22206, 22263–23890, 23903–27168, 27462–28240, 30435–30589, 30616–30888;
  `Hopf/SingularHomology.lean` 4359–5310, 15299–16000, 19058–19220, 23000–24933.
- Targets: `Lib/Geometry/Manifold/Transversality/{Basic,Sard,Parametric,Ambient,
  GeneralPosition}.lean`, `Lib/Geometry/Manifold/Isotopy/{Supported,Germs,
  Linearization,DiskTheorem,Homogeneity}.lean`,
  `Lib/Geometry/Manifold/Immersion/{Relative,Arc,FrameChart}.lean`,
  `Lib/AlgebraicTopology/SphereMaps/Nullhomotopic.lean`.
- Textbook statements: Sard's theorem on manifolds and parametric transversality
  (Hirsch Ch. 3 Thm 2.1); transversality and disjunction by an ambient
  diffeomorphism isotopic to the identity (Thm 2.5); general position when
  dim X + dim Y < dim N; the compactly supported isotopy extension theorem
  (Ch. 8 Thm 1.3); the disc theorem and homogeneity of manifolds (Thm 3.1;
  Milnor h-cobordism Thm 9.6); the relative Whitney immersion and embedding
  theorems for 2k < n (Ch. 2 Thm 1.1, 1.3); a smooth map from a compact manifold
  of dimension < n into Sⁿ is nullhomotopic; finitely many transverse
  intersections of compact complementary submanifolds.
- Generalize: the immersion/embedding chain is pinned to a 2-dimensional source
  (`Smale.PlaneImmersion.Plane := ℝ × ℝ`, `finrank ℝ E = 2`, `5 ≤ finrank ℝ G`
  at DifferentialTopology 24665, 24879–25924) — restate for a k-manifold with
  2k ≤ n; the 1-dimensional curve chain (`3 ≤ finrank ℝ G`) is the case k = 1.
  Everything else in the lane is already at full generality (general
  `ModelWithCorners`, `[Boundaryless]`) and is a pure move.
- Consumers: `Hopf.DifferentialTopology`, `Hopf.SingularHomology`,
  `Hopf.SphereTopology`, `Hopf.Recognition`.
- Axiom probe: `Smale.NativeTransversality.exists_ambient_transverse_diffeomorph`,
  `Smale.ManifoldImmersion.exists_compact_embedding_of_immersion`,
  `MorseCancel.exists_isotopic_pointMoving_of_path`.

### Lane F — the Whitney trick, intersection numbers, handle slides, integer-matrix reduction (Milnor h-cobordism §6–7, Thm 6.4 and 7.8; Smale 1961 §4–5; Hatcher Prop 2.30) — after A, D1, D2, E1, E2
- Source: `Hopf/SingularHomology.lean` 16000–28261; `Hopf/SphereTopology.lean`
  2680–2967, 9532–9878, 14839–15295, 18068–18588; `Hopf/DifferentialTopology.lean`
  27220–27329, 28344–28604, 28935–30219; `Hopf/Recognition.lean` 4078–10476.
- Targets: `Lib/Geometry/Manifold/Whitney/{IntersectionNumber,StripNormalData,
  BigonModel,Framing,Filling,GraphMotion,Trick,BeltCancellation,ArcTube,
  LongitudinalMotion}.lean`, `Lib/Geometry/Manifold/Morse/{AttachingClass,
  IntersectionMatrix,HandleSlide,SingleIntersection}.lean`,
  `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean`,
  `Lib/Algebra/Module/IntegerPresentation.lean`.
- Textbook statements: the signed intersection number of two transverse
  complementary submanifolds and its expression as a sum of local degrees;
  Whitney's lemma: two intersection points of opposite sign joined by an
  embedded bigon in a manifold of dimension ≥ 5 are removed by a compactly
  supported ambient isotopy (h-cobordism Thm 6.4); handle slides change the
  intersection matrix by elementary column operations and every such operation
  is realized geometrically (§7); a unimodular row of integers is reduced to
  contain ±1 by column operations, and a finitely presented abelian group has a
  presentation matrix that is surjective iff the group is trivial (Thm 7.8).
- Generalize: the Whitney trick is written only for sheets of dimensions 3 and 2
  inside a 6-manifold (`Smale.RankThreeWhitneyModel` with model space
  ℝ³ × ℝ², `Smale.WhitneyPairModel.Plane = EuclideanSpace ℝ (Fin 2)`,
  `TubularBigon` with normal rank defaulted to 4, `PlanarFrame` with 2×2
  determinants, `exists_signed_belt_cancellation_step` requiring
  `finrank ℝ E = 6` and index 2); the handle-slide blocks in `Recognition`
  carry `finrank ℝ E = 6` at 37 sites and `Smale.Hemisphere.Sphere 2`, index 3,
  degree 2 throughout. Restate for sheets of dimensions p + q = n, n ≥ 5, with
  3 ≤ k ≤ n − 3 or π₁-trivial levels, handle index k, homology degree k − 1.
  Land the transvection / integer-presentation algebra (pure move, no topology:
  Recognition 6367–6385, 9042–9189; SphereTopology 18429–18588) first.
- Consumers: `Hopf.SingularHomology`, `Hopf.SphereTopology`, `Hopf.Recognition`.
- Axiom probe: `Smale.TubularBigon.exists_rankThree_relative_cancellation` (in
  its generalized form), `MorseCancel.primitive_row_has_unit_after_column_additions`.

### Lane G — Smale's recognition theorem (Smale 1961 Thm A; h-cobordism Thm 9.1) — after C, D1, D2, E1, E2, F; last
- Source: `Hopf/SphereTopology.lean` 3778–4876, 8709–8882, 10489–13361, 18589–18831;
  `Hopf/Recognition.lean` 10477–11148, 11255–11317; `Hopf/SingularHomology.lean`
  19048–19058, 19220–19302.
- Targets: `Lib/Geometry/Manifold/Morse/{MiddleBlocks,HandleTrade,MinimalSystem}.lean`,
  `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean`.
- Textbook statement: a compact smooth manifold homotopy equivalent to S⁶ is
  homeomorphic to S⁶ (Smale's generalized Poincaré conjecture in the smooth,
  compact case, at n = 6). Decision Q1 (DEFAULT, flippable): keep n = 6 and
  generalize only the model space — the theorem already takes an arbitrary
  finite-dimensional real normed space E with `finrank ℝ E = 6`; consolidate the
  five spellings of S⁶ on `Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`, drop
  the vestigial `[SecondCountableTopology M]`, and record in the file docstring
  the precise relation to Mathlib's `proof_wanted
  ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` (topological,
  every n, Euclidean model, no compactness). The generalization to n ≥ 5 is the
  follow-up lane G′; do not start it.
- The chain to preserve (statement unchanged, proof re-routed):
  `Smale.homeomorphic_sixSphere_of_homotopySixSphere` ←
  `MorseCancel.nonempty_homeomorph_of_homotopySixSphere` ←
  `exists_two_critical_point_morse_of_homotopySixSphere` ←
  `exists_minimal_ordered_morse_system_without_outer_indices` (SphereTopology
  13361) ← `cancel_from_complete_middle_family` ← `exists_primitive_functional_unit`
  ← … ← Reeb (`nonempty_homeomorphSphere_of_two_critical_points`, lane D1).
- Consumers: `Hopf.Recognition`, `Hopf.Final`.
- Axiom probe: `Smale.homeomorphic_sixSphere_of_homotopySixSphere`.

## OUT OF SCOPE (binding)
- Lanes A, B, D1, D2, E1, H, I (the GLM task): do not move singular-homology
  core, Morse theory I, rearrangement/cancellation, complex analysis, quotient
  and mapping-torus blocks; if you need one of their declarations before it has
  landed, import the `Hopf` module as today and record the dependency.
- Anything under `Hopf/LCP/` not named above by prefix and range.
- Changing the statement of any declaration under `Hopf/`, including
  `mathoverflow_1973`, `Degree.threefoldHomotopyEquiv`,
  `Smale.homeomorphic_sixSphere_of_homotopySixSphere`.
- Lane G′ (n ≥ 5); editing `lean-protocol.md`, `scripts/lib_stock_prefixes.txt`
  (except to remove an entry whose declarations are all gone), Mathlib,
  `lakefile.toml`.

## Cross-model ordering
- C waits for GLM's A. E2 waits for GLM's D1. F waits for GLM's A, D1, D2, E1 and
  your E2. G waits for your C and F. J waits for GLM's A (and your C only if the
  rank-4 block needs `CrossProduct.lean`).
- While blocked, write the Axis-1 textbook files and the Axis-5 ledgers of the
  next lane (they need no landed code), then take the next unblocked lane:
  order C → J → E2 → F → G.

## Build discipline (the box is shared — `ps` first)
- `lake exe cache get` before anything; never build Mathlib from source; never
  `lake clean`.
- Build only the touched modules and their consumers: `lake build Lib.<Module>`,
  then `lake build Hopf.<Consumer>`; once per lane `lake build Hopf.Final` then
  `lake build Solution` (hours; schedule it). Record wall-clock time of every
  `lake build` in the lane report.
- Axis-5 probes: `*_InterfaceCheck.lean` / `*_InterfaceConsumerCheck.lean` in the
  tree, compiled with `lake env lean`, deleted before the commit; the receipt
  goes in `Lib/docs/<lane>-INTERFACE_RECEIPT.md`.
- `python3 scripts/lib_stock_census.py --check` before every commit; `--update`
  after every extraction commit; commit the lowered baseline.
- Axiom probe: append the lane's top theorems to `Lib/AxiomAudit.lean` and run
  `lake env lean Lib/AxiomAudit.lean`.
- Comparator: `lake exe comparator comparator/config.json` once per lane.

## Commit conventions
- Branch `lib/<lane>-<slug>`; message prefix `lib(<lane>):`; one commit per
  `Lib` file or per green unit; the rename commit separate.
- No trailers; attribution is handled by the repository owner's instructions.
- NEVER git push.

## Report (per lane, committed)
`Lib/reports/<lane>.md`: the generalized statement and where its textbook proof
lives, what moved (source ranges → target files, declaration counts, lines
deleted), consumers re-routed, census number before / after, the
`#print axioms` output verbatim, build wall times, the interface receipt, open
items. An honest obstruction (the generalization needs mathematics the textbook
proof does not supply; a statement under `Hopf/` would have to change) is a
valid deliverable: stop at the last isomorphic boundary, leave the pinned
version in `Hopf/`, and record the exact seam.
