# TASK LIB-GLM — pure-move extraction lanes A, D1, D2, E1, H, I, B

**TruthSeed:** `lib-extraction:pure-moves-textbook-before-lean`
**For:** GLM-5.3-Flash, working on a fork of github.com/fabianx-ai/HopfProblem,
branch `lib/textbook-extraction` (base commit 721fc82; toolchain
leanprover/lean4:v4.33.0; Mathlib pinned in lake-manifest.json).
**Nature:** GENERIC library extraction, upstream-shaped. Mathematics for the
commons: Mathlib-shaped paths and names, a docstring on every public
declaration, no project vocabulary inside `Lib/`. Read `lean-protocol.md`
(repository root) and `Lib/README.md` FIRST and follow them: Axis 1 (the
textbook file) before any Lean is touched, then decomposition, then Lean.
`Lib/EXTRACTION_PLAN.md` is the plan; its §2 table gives every source line
range on 721fc82 and every target file; its §3 gives the validation recipe;
its §7 the hazards. This task file only sequences your lanes.

## Your lanes, in execution order

Each lane: create `lib/<lane>-<slug>` off `lib/textbook-extraction`; write the
Axis-1 file `Lib/docs/<lane>.md` (correspondence table block → textbook theorem
with citation → target `Lib` file → declaration names; for a pure move that IS
the textbook file, because the proofs already exist and are not redesigned);
then cut the declarations by declaration boundary (never by raw line) from the
census ranges, paste into the target file with the file-level pragmas of the
source (`set_option maxSynthPendingDepth 3`, the `open`/`open scoped` lines,
`noncomputable section`, `universe u v`, the local notations, every
`attribute [local instance …] … in` wrapper), delete them from `Hopf/`, add
`import Lib.…` to each consumer, and — if a consumer references the old dotted
name more than about fifty times — leave an `export`/`alias` shim in `Hopf/`
(transitional namespace rule, `Lib/README.md`). Statements never change in
your lanes; if a statement must change to compile, stop and record it as an
open item for the Kimi task instead.

### Lane A — singular homology core (Hatcher §2.1–2.2, 2.B) — first, nothing waits on you
- Source: `Hopf/SingularHomology.lean` 85–3835, 3835–4359, 30894–31281;
  `Hopf/SphereTopology.lean` 85–2571, 6624–7310, 13388–13962, 15326–16127,
  16147–18066; `Hopf/Hurewicz.lean` 15792–15994, 23324–23422;
  `Hopf/LCP/CuspFilling.lean` declarations `SingularMayerVietoris.*` 15076–15346;
  `Hopf/DifferentialTopology.lean` 30922–31117 (`SmallChainBiprod`).
- Targets: `Lib/AlgebraicTopology/SingularHomology/{Chains,ModuleHomology,
  MayerVietoris,Subdivision,SmallChains,HomotopyInvariance,Sum,Coproduct,
  CircleProduct,Suspension,Sphere,Naturality,LocalContributions,
  LinearSphereAction,LocalDegree,Augmentation}.lean`,
  `Lib/Topology/Homotopy/Suspension.lean`, `Lib/Topology/OnePointCollapse.lean`,
  `Lib/Algebra/Homology/MayerVietorisShortExact.lean`.
- Mathematics (in words): the singular chain complex of a space, with its free
  basis of singular simplices; the short exact sequence of chain complexes
  0 → C(U ∩ V) → C(U) ⊕ C(V) → C^{U,V}(X) → 0 for two open sets covering X,
  and the resulting Mayer–Vietoris long exact sequence (Hatcher §2.2); the
  barycentric subdivision operator with its chain homotopy and the small
  simplices theorem (Hatcher Prop 2.21); homotopy invariance (Thm 2.10); H₀ of
  a path-connected space is ℤ and detects path components (Prop 2.7); homology
  of disjoint unions and finite coproducts (Prop 2.6); the unreduced suspension
  and the suspension isomorphism, hence H_n(Sⁿ) ≅ ℤ and H_k(Sⁿ) = 0 otherwise
  (Cor 2.14); Künneth for S¹ × X; naturality of the connecting homomorphism and
  its localization over a disjoint family of opens; a linear automorphism acts
  on H_n(Sⁿ) by the sign of its determinant (Prop 2.32–2.33); local degree data
  (Prop 2.30).
- Move type: pure move. Namespaces to rename in the second commit:
  `PeriodTorusHigherHomology` → `SingularHomology`, `CuspCentralHomology` →
  `Suspension`, `ThreefoldHomologyStarCoproduct` → `Coproduct`, `SixSphereCube`
  → `OnePointCollapse`, `FirstHurewicz` → `SingularChains`.
- Consumers to re-route and build: `Hopf.SingularHomology`, `Hopf.SphereTopology`,
  `Hopf.Hurewicz`, `Hopf.LCP.CuspFilling`, `Hopf.LCP.Specialization`,
  `Hopf.LCP.BoundaryTopology`, `Hopf.LCP.IntegralHomology`, `Hopf.Recognition`.
- Top theorems for the axiom probe: `SingularMayerVietoris.exact_at_ambient`,
  `SphereHomology.unitSphere_homology_subsingleton`,
  `Smale.LinearSphereAction.homology_eq_sign_smul`.
- Hazards: `(X : Type)` universe 0 everywhere (keep it); the local instance
  `ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts` is attached to
  every declaration of its block; `CuspCentralHomology.instLocal1` supplies the
  quotient topology on the suspension.

### Lane D1 — Morse theory I (Milnor, Morse Theory §2–3; h-cobordism Thm 2.5; Lee Thm 4.5, Cor 5.14, Thm 9.12) — independent of A
- Source: `Hopf/DifferentialTopology.lean` 85–9042, 14780–14981, 18259–19186,
  19195–20129, 30241–30355; `Hopf/SphereTopology.lean` 2595–2680, 7318–8708;
  `Hopf/SingularHomology.lean` 5310–5859; `Hopf/Recognition.lean` 1612–1640,
  2090–2333, 3197–3453, 11149–11254.
- Targets: `Lib/Analysis/Calculus/MorseLemma.lean`, `Lib/Analysis/ODE/SmoothFlow.lean`,
  `Lib/Geometry/Manifold/{InverseFunction,ChartedSpace/Transport,Flow/Compact,
  Flow/HeightTranslating,RegularLevel}.lean`, `Lib/Geometry/Manifold/Morse/{Basic,
  Existence,GradientLike,Handle,HandleAttachment,SublevelSets,Index,
  SurgeryWindows,Reeb}.lean`, `Lib/Topology/Homotopy/{DiskCylinder,CylinderHEP,
  HandleRetraction}.lean`.
- Mathematics: the Morse lemma (a nondegenerate critical point has a chart in
  which f = f(a) + Σ ±yᵢ²; Milnor Morse Theory Lemma 2.2); every compact smooth
  manifold admits a Morse function (h-cobordism Thm 2.5) and a gradient-like
  vector field; a C¹ field on a compact manifold generates a global flow, and a
  C^∞ field has a C^∞ flow (Lee Thm 9.12); a regular level set is a manifold of
  one lower dimension (Lee Cor 5.14); the Morse index is well defined; across a
  band without critical values sublevel sets are homeomorphic and homotopy
  equivalent (Morse Theory Thm 3.1); passing a critical point of index λ attaches
  a λ-handle, up to homotopy equivalence and up to homeomorphism with control on
  the level (Thm 3.2); the handle-attachment exact sequence in homology; Reeb's
  theorem: a closed manifold with a Morse function with two critical points is a
  sphere (Thm 4.1); the disc cylinder I × Dⁿ ≅ D^{n+1} and the homotopy extension
  property of (Dⁿ, S^{n−1}) (Hatcher Prop 0.16); transport of a manifold
  structure along a homeomorphism.
- Move type: pure move. Hazards: `Smale.RegularLevel.chartedSpace` is
  `@[instance_reducible]` and appears as `letI := …` inside theorem statements —
  keep that idiom exactly; `Fact (Module.finrank ℝ … = n + 1)` instances; the
  `Classical.propDecidable` wrappers.
- Consumers: `Hopf.DifferentialTopology`, `Hopf.SingularHomology`,
  `Hopf.SphereTopology`, `Hopf.Recognition`, `Hopf.Final`.
- Axiom probe: `Smale.ManifoldMorse.exists_morse_function`,
  `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn`,
  `Smale.ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits`,
  `Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points`.

### Lane D2 — Whitney embedding, tubular neighbourhoods, collars, finite cell structures (Lee Thm 6.15, 6.24, Ch. 10; Morse Theory Thm 3.1, 3.5; h-cobordism Thm 3.4) — after D1 (and A for the cell-attachment homology rows)
- Source: `Hopf/DifferentialTopology.lean` 10392–14114;
  `Hopf/SingularHomology.lean` 28353–29652; `Hopf/Recognition.lean` 2580–2903,
  2904–3162, 3538–3809.
- Targets: `Lib/Geometry/Manifold/{WhitneyEmbedding,VectorBundle/ProjectionBundle,
  Tubular,Collar}.lean`, `Lib/Geometry/Manifold/Morse/CellStructure.lean`,
  `Lib/Topology/Homotopy/CellAttachment.lean`.
- Mathematics: every compact smooth manifold embeds in some ℝᴺ with injective
  differential; a smooth family of idempotents of constant rank defines a smooth
  vector bundle; the tubular neighbourhood theorem and a smooth retraction onto
  the submanifold; collars of regular levels and compactly supported ambient
  diffeomorphisms moving one level to a nearby one; a handle deformation-retracts
  to its core cell, so attaching a handle is attaching a cell up to homotopy; the
  cell-attachment Mayer–Vietoris cover; every compact smooth manifold has the
  homotopy type of a finite cell complex with one cell per critical point
  (Morse Theory Thm 3.5).
- Consumers: `Hopf.DifferentialTopology`, `Hopf.SingularHomology`,
  `Hopf.SphereTopology`, `Hopf.Recognition`.
- Axiom probe: `Smale.NativeEuclideanEmbedding.exists_tubularNeighborhood`,
  `Degree.MorseCells.built_of_compact_smooth_manifold`.

### Lane E1 — rearrangement, cancellation, births (h-cobordism Thm 4.1, 4.8, 5.4, 8.1) — after D1, D2
- Source: `Hopf/SingularHomology.lean` 5859–15299, 28261–28353;
  `Hopf/DifferentialTopology.lean` 14132–14773, 14992–18213, 20179–20983,
  28637–28926; `Hopf/SphereTopology.lean` 3008–3717, 5000–6556, 8943–9512,
  9887–9960, 10017–10431, 11026–11878.
- Targets: `Lib/Geometry/Manifold/Morse/{Cubic,CubicFlow,BandLyapunov,Cancellation,
  Rearrangement,IndexOrdering,SuperfluousMinima,Birth,Duality}.lean`,
  `Lib/Geometry/Manifold/Flow/{TimeChange,PhaseChart,LevelCylinder,
  FieldChartGluing}.lean`, `Lib/Analysis/Calculus/IntervalTranslation.lean`.
- Mathematics: time change of a flow by a positive factor; the flow cylinder of a
  regular level and realization of a level isotopy by a modified gradient-like
  field; the cubic model x³/3 + t·x + Σ σᵢyᵢ² and the complete analysis of its
  flow; a smooth Lyapunov function on a band; the First Cancellation Theorem
  (two critical points of adjacent index joined by a unique transverse orbit
  cancel; h-cobordism Thm 5.4); the Rearrangement Theorem (critical values of
  non-interacting critical points can be reset; Thm 4.1) and self-indexing
  Morse functions (Thm 4.8); cancellation of superfluous minima and maxima
  (Thm 8.1) and the duality f ↦ −f; birth of a pair of critical points of
  prescribed adjacent indices.
- Consumers: `Hopf.SingularHomology`, `Hopf.SphereTopology`, `Hopf.Recognition`.
- Axiom probe: `Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection`,
  `MorseCancel.cancel_of_transverse_level_isotopy`,
  `MorseCancel.exists_excellent_indexed_morse_birth`.

### Lane H — complex analysis (Ahlfors Ch. 3–6; Rudin RCA 13.11, 14.8, 14.18–14.20; Forster §5, §13–14; Hörmander Ch. I) — independent; do it while blocked on D1/D2
- Source: `Hopf/LCP/AnalyticFillings.lean` `RiemannMapping.*` 4369–5578 with the
  `_root_.Complex.*` steps 4711–5413 (STOP at 5579: from `triangleDomain` on it is
  project code), `RiemannBoundary.*` and `SchwarzReflection.*` (4409–9121,
  interleaved with project declarations — cut by name), `RiemannSphere.*`
  3581–4019, `TriangleRiemannNormalization.*` 4149–4266, and exactly three
  lemmas of `TriangleUniformizationGluing`: `contMDiff_of_continuous_of_finite`,
  `contMDiff_symm_of_contMDiff`, `biholomorphOfHomeomorph`;
  `Hopf/LCP/PeriodConstruction.lean` `HolomorphicCousin.*` 15593–17278,
  `AnalyticRootCover.*` and `AnalyticRootCoverContinuation.*` 12060–13206,
  `RiemannSphere.*` 8012–8082.
- Targets: `Lib/Analysis/Complex/{RiemannMapping,RiemannMapping/Steps,
  SchwarzReflection,BoundaryExtension,Mobius,DBar,Cousin,SquareRoot}.lean`,
  `Lib/Geometry/Manifold/Instances/RiemannSphere.lean`,
  `Lib/Geometry/Manifold/Complex/Biholomorph.lean`.
- Mathematics: the Riemann mapping theorem via normal families and the Koebe
  derivative maximization (Ahlfors Ch. 6 §1; Rudin 14.8); Schwarz reflection
  across a line and across an arc of the unit circle; Carathéodory-style
  extension of a disc homeomorphism to the closed disc; Möbius transformations
  of the Riemann sphere, three-point maps, cross-ratio, disc ↔ half-plane; the
  solution of ∂̄u = f by the Cauchy–Green transform and the additive Cousin
  problem on an open cover of ℂ (Forster §13–14; Hörmander I §1.2–1.4);
  holomorphic square roots on simply connected domains when all zeros have
  even order (Rudin 13.11).
- Consumers: `Hopf.LCP.AnalyticFillings`, `Hopf.LCP.PeriodConstruction`,
  `Hopf.LCP.BoundaryTopology`, `Hopf.LCP.IntegralHomology`.
- Axiom probe: `RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`,
  `HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution`,
  `AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros`.
- Note: two of the 31 `_root_` steps duplicate `private` lemmas in Mathlib's
  `Analysis/Complex/RiemannMapping.lean`; keep them (decision Q6) and list them
  in the report as the upstream follow-up.

### Lane I — quotient manifolds, coverings, mapping torus, Wang sequence, split extensions (Forster §1–5; Hatcher §1.3, Ex 2.48) — Wang part after A, the rest independent
- Source (by prefix; ranges in `Lib/EXTRACTION_PLAN.md` §2): `Hopf/LCP/PeriodConstruction.lean`
  `LocalOrbitQuotient`, `OnePointAtlas`, `TwoAffineCharts`, `FreeActionLocus`,
  `BranchedQuotientAtlas`; `Hopf/LCP/LocalModels.lean` `CoveringQuotient`,
  `DiscreteQuotient`, `MappingTorus` 6899–8395, `ThreefoldHomologyFinitenessRetraction`
  8731–8924; `Hopf/LCP/CuspFilling.lean` `InvariantSubsetQuotient`, `CoveringOrthant`,
  `ProductRestriction`, `CuspRetraction.Patching` 490–631; `DiagonalQuotient` in
  `AnalyticFillings` and `BoundaryTopology`; `Hopf/LCP/BoundaryTopology.lean`
  `TwoOpenTransition`, `SplitGroupExtension`, `MappingTorusHomology` 3988–4609,
  `TwistGroup`; `Hopf/LCP/IntegralHomology.lean` `MappingTorusHomology` 7576–8688.
- Targets: `Lib/Geometry/Manifold/Quotient/{LocalOrbit,Atlas,Covering,Lattice}.lean`,
  `Lib/Geometry/Manifold/{OnePoint,ProjectiveLine}.lean`,
  `Lib/Topology/Algebra/FreeActionLocus.lean`,
  `Lib/Topology/Covering/{Quotient,DiagonalQuotient}.lean`,
  `Lib/AlgebraicTopology/FundamentalGroup/DiagonalQuotient.lean`,
  `Lib/Topology/FiberBundle/TwoOpenTransition.lean`,
  `Lib/GroupTheory/{SplitExtension,PresentedGroup/CentralTwist}.lean`,
  `Lib/Topology/MappingTorus/{Basic,HomologyCover,WangAlgebra,Wang}.lean`,
  `Lib/Topology/Homotopy/{SublevelRetraction,LocalCollapse}.lean`.
- Mathematics: charts on quotients by properly discontinuous and free actions,
  the free locus, one-point compactification of a Riemann surface, ℙ¹ from two
  affine charts, E/L for a discrete lattice as a Lie group; a covering quotient
  with holomorphic deck action is a manifold; the diagonal quotient (B × F)/G
  as a fibre bundle and its π₁ exact sequence; a principal bundle glued from two
  opens by one transition function and its monodromy; a split extension is a
  semidirect product; the mapping torus, its two-open cover, and the Wang exact
  sequence (Hatcher Ex 2.48); deformation retraction onto a sublevel set and
  patching of local collapses.
- Consumers: `Hopf.LCP.LocalModels`, `Hopf.LCP.CuspFilling`, `Hopf.LCP.Specialization`,
  `Hopf.LCP.PeriodConstruction`, `Hopf.LCP.AnalyticFillings`, `Hopf.LCP.GlobalAssembly`,
  `Hopf.LCP.BoundaryTopology`, `Hopf.LCP.IntegralHomology`.
- Axiom probe: `MappingTorusHomology.wang_exact_at_mappingTorus`,
  `SplitGroupExtension.mulEquiv`.
- Rename: `ThreefoldHomologyFinitenessRetraction` → `SublevelRetraction`,
  `CuspRetraction.Patching` → `LocalCollapse`, `CoveringOrthant` → `CoveringChart`.

### Lane B — fundamental group, van Kampen, simply connected spheres (Hatcher Thm 1.20, Prop 1.14) — after A; last
- Source: `Hopf/Hurewicz.lean` 545–1348, 1353–1466; `Hopf/SingularHomology.lean`
  18734–19048; `Hopf/LCP/BoundaryTopology.lean` `FundamentalGroupVanKampen.*`
  (114 declarations) and `TriangleRegularBaseFundamentalGroup.*` 8622–8767.
- Targets: `Lib/AlgebraicTopology/FundamentalGroup/{VanKampen,SimplyConnectedCover,
  TwoSimplyConnectedCover}.lean`, `Lib/Topology/Homotopy/{SuspensionSimplyConnected,
  LoopSubdivision}.lean`, `Lib/AlgebraicTopology/FundamentalGroupoid/SimplyConnectedSphere.lean`.
- Mathematics: a space covered by simply connected open sets through a common
  point with path-connected pairwise intersections is simply connected; the
  Seifert–van Kampen theorem for a two-open cover in pushout form, including the
  uniqueness half; a loop is homotopic to a concatenation of loops each inside
  one member of an open cover; the unreduced suspension of a path-connected
  space, hence every sphere of dimension ≥ 2, is simply connected.
- Consumers: `Hopf.Hurewicz`, `Hopf.SingularHomology`, `Hopf.LCP.BoundaryTopology`,
  `Hopf.Recognition`.
- Axiom probe: `simplyConnectedSpace_of_open_cover`,
  `FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv`.
- Note: the sphere and loop-subdivision blocks are adapted from Mathlib PR #28246;
  say so in the docstrings; an equivalent formalization of the van Kampen block
  exists outside this tree (decision Q4) — move as-is and note it in the report.

## OUT OF SCOPE (binding)
- Lanes C, E2, F, G, J (the Kimi task): do not touch `*Hurewicz.*` blocks
  other than the two listed under lane A, nothing in `Hopf/SingularHomology.lean`
  16000–28261, nothing in `Hopf/Recognition.lean` other than the ranges listed
  above, no `PeriodTorusHigherHomology` torus/Pontryagin/exterior blocks.
- Anything under `Hopf/LCP/` that is not named above by prefix and range.
- Changing the statement of any declaration under `Hopf/`, including
  `mathoverflow_1973`, `Degree.threefoldHomotopyEquiv`,
  `Smale.homeomorphic_sixSphere_of_homotopySixSphere`.
- Editing `lean-protocol.md`, `scripts/lib_stock_prefixes.txt` (except to
  remove an entry whose declarations are all gone), Mathlib, `lakefile.toml`.

## Cross-model ordering
- Kimi's lane C starts as soon as your lane A has landed on
  `lib/textbook-extraction`; Kimi's F waits for your A, D1, D2, E1 (and its own
  E2); Kimi's J waits for your A. Land A first and announce it in
  `Lib/reports/A.md`.
- While blocked (D2 waits for D1; E1 waits for D2; I's Wang part waits for A),
  take the next independent lane: order A → D1 → H → D2 → I → E1 → B.

## Build discipline (the box is shared — `ps` first)
- `lake exe cache get` before anything; never build Mathlib from source; never
  `lake clean`.
- Build only the touched modules and their consumers: `lake build Lib.<Module>`,
  then `lake build Hopf.<Consumer>` for the consumers listed per lane; once per
  lane `lake build Hopf.Final` then `lake build Solution` (hours; schedule it).
- Record wall-clock time of every `lake build` in the lane report.
- `python3 scripts/lib_stock_census.py --check` before every commit;
  `--update` after every extraction commit; commit the lowered baseline.
- Axiom probe: append the lane's top theorems to `Lib/AxiomAudit.lean` and run
  `lake env lean Lib/AxiomAudit.lean`.
- Comparator: `lake exe comparator comparator/config.json` once per lane.

## Commit conventions
- Branch `lib/<lane>-<slug>`; message prefix `lib(<lane>):`; one commit per
  `Lib` file or per green unit; the rename commit separate (`lib(<lane>): rename …`).
- No trailers; attribution is handled by the repository owner's instructions.
- NEVER git push.

## Report (per lane, committed)
`Lib/reports/<lane>.md`: what moved (source ranges → target files, declaration
counts), consumers re-routed (with shims listed), census number before / after,
the `#print axioms` output verbatim, build wall times, open items (statements
that would have to change, declarations left behind, upstream follow-ups). An
honest obstruction (a block that does not move without a statement change) is a
valid deliverable: leave it in `Hopf/`, record the exact declaration and reason.
