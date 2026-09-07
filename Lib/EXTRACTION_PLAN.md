# Extraction plan — moving the generic mathematics of `Hopf/` into `Lib/`

Measured on commit `721fc82ddbb6cb4d2221bacec0c030636a276f3e` (branch
`refactor/v10-section6-lib`; toolchain `leanprover/lean4:v4.33.0`; Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`). All line ranges below refer to that commit.

## 1. What the census found

The sixteen `Hopf/*.lean` modules are exact byte slices of one 248,818-line `Solution.lean`
(see `PROVENANCE.md`, `SPLIT_MANIFEST.json`). They carry no `section`/`namespace` structure,
no docstrings and no `variable` blocks; every file is one `namespace Mathoverflow1973`. The
only block marker is the dotted prefix of each declaration name, so the census works with
*runs of consecutive declarations sharing a top-level name prefix*. Namespace names are
systematically misleading: `PeriodTorusHigherHomology` is generic singular-homology API
(homotopy invariance, disjoint sums, S¹ × X Künneth, H_*(Tʳ)); `CuspCentralHomology` in the
recognition tail is the unreduced suspension; `ThreefoldHomologyStarCoproduct` is H_*(∐ Xᵢ);
`SixSphereCube` is a generic one-point collapse; `FirstHurewicz` in the tail is the
singular-chains API; `Smale`, `Morse`, `Degree`, `NoExotic` are just namespaces.

| file | lines | generic (textbook) | generic but pinned to a dimension | project |
|---|---:|---:|---:|---:|
| Hopf/Hurewicz.lean | 23,665 | 7,723 | 15,490 | 0 |
| Hopf/SingularHomology.lean | 31,352 | 22,923 | 8,252 | 92 |
| Hopf/SphereTopology.lean | 18,879 | 13,374 | 4,307 | 0 |
| Hopf/Recognition.lean | 11,322 | ≈2,020 | ≈8,570 | ≈640 |
| Hopf/DifferentialTopology.lean | 31,136 | ≈23,680 | ≈5,780 | 0 |
| Hopf/LCP/*.lean, FiniteCore, Final, Shortcuts | 133,804 | ≈14,140 | ≈3,750 | ≈115,800 |
| **total** | **250,158** | **≈83,860** | **≈46,145** | **≈116,540** |

About 130,000 lines (52%) are textbook mathematics; the five recognition-tail files are
99.4% generic. Pinned-dimension material is the Hurewicz theorem unrolled at n = 2, 3, 4, 5,
6; the Morse/handle assembly at dimension 6 with indices 2, 3; the Whitney trick for sheets of
dimensions 3 + 2 in a 6-manifold; and torus homology at rank 4.

**Stock baseline: 9,408 declarations** matched by `scripts/lib_stock_prefixes.txt` (57
entries) out of 20,657 declarations under `Hopf/`, measured on `721fc82`. Known imprecision:
the prefix `RiemannMapping` counts its 131 project (triangle-boundary) declarations because
the generic core and the project part share one namespace; `Smale`/`MorseCancel`/
`AdaptedWindows` include about thirty six-sphere glue wrappers. Neither is corrected in the
setup commit (decision Q8).

## 2. Lanes

Citations: Milnor, *Lectures on the h-cobordism theorem* (1965): Thm 2.5 existence of Morse
functions; Thm 3.4, Cor 3.5 collars; Thms 3.12–3.14 elementary cobordisms; Thm 4.1, Thm 4.8
rearrangement; Thm 5.4 first cancellation; Thm 6.4 second cancellation (Whitney); Thm 7.8 basis
theorem; Thm 8.1 elimination of index 0, 1; Thm 9.1 h-cobordism; Thm 9.6 disc theorem.
Milnor, *Morse Theory* (1963): Lemma 2.2 Morse lemma; Thm 3.1 regular bands; Thm 3.2 handle
attachment; Thm 3.5 CW structure; Thm 4.1 Reeb. Hatcher, *Algebraic Topology* (2002): Thm 1.20
van Kampen; Prop 1.14 π₁(Sⁿ) = 0; Prop 2.6 disjoint unions; Prop 2.7 H₀; Thm 2.10 homotopy
invariance; Prop 2.21 small simplices; Cor 2.14 H_*(Sⁿ); Prop 2.30 local degree; Ex 2.48 Wang
sequence; Thm 2A.1 H₁ = π₁ᵃᵇ; §3.B cross product; Thm 3C.5 Pontryagin product; Thm 4.5
Whitehead; Thm 4.32 Hurewicz; Cor 4.25 Hopf degree theorem. Hirsch, *Differential Topology*
(1976): Ch. 2 Thm 1.1/1.3 immersion/embedding; Ch. 3 Thm 2.1/2.5 transversality; Ch. 8 Thm 1.3
isotopy extension, Thm 3.1 disc theorem. Lee, *Introduction to Smooth Manifolds* (2nd ed.):
Thm 4.5, Cor 5.14, Thm 6.15, Thm 6.24, Thm 9.12. Ahlfors, *Complex Analysis*: Ch. 3 §3, Ch. 4
§6.5, Ch. 6 §1. Rudin, *Real and Complex Analysis*: 13.11, 14.8, 14.18–14.20. Forster,
*Lectures on Riemann Surfaces*: §1–5, §13–14. Hörmander, *An Introduction to Complex Analysis
in Several Variables*: Ch. I §1.2–1.4. Smale, *Generalized Poincaré's conjecture in dimensions
greater than four*, Ann. Math. 74 (1961).

| id | lane / textbook chapter | source blocks on 721fc82 (file: lines) | target `Lib/` files | move type | size (lines) | after | model |
|---|---|---|---|---|---:|---|---|
| **A** | Singular homology core — Hatcher §2.1–2.2, 2.B | SingularHomology: 85–3835 (chains API, MV short/long exact sequences, cycle calculus, barycentric subdivision, small simplices, homotopy invariance), 3835–4359 (punctured spaces, linking relation), 30894–31281 (radial cylinder, local-degree data); SphereTopology: 85–2571 (suspension, disjoint sums, S¹×X, H₀, H_*(S¹), top class of Sⁿ), 6624–7310 (cell-attachment exact sequence, H₀ detects components), 13388–13962 (one-point collapse, two-hemisphere cover, MV naturality), 15326–16127 (coproducts, disjoint opens, local contributions, H_k(Sⁿ) = 0), 16147–18066 (linear sphere action = sign det, local degree); Hurewicz: 15792–15994, 23324–23422 (homology descent, augmentation, normalized cycles); LCP/CuspFilling: `SingularMayerVietoris` 15076–15346 (MV naturality); DifferentialTopology: 30922–31117 (`SmallChainBiprod`) | `Lib/AlgebraicTopology/SingularHomology/{Chains,ModuleHomology,MayerVietoris,Subdivision,SmallChains,HomotopyInvariance,Sum,Coproduct,CircleProduct,Suspension,Sphere,Naturality,LocalContributions,LinearSphereAction,LocalDegree,Augmentation}.lean`, `Lib/Topology/Homotopy/Suspension.lean`, `Lib/Topology/OnePointCollapse.lean`, `Lib/Algebra/Homology/MayerVietorisShortExact.lean` | pure move | ≈14,000 | — | GLM |
| **B** | π₁, van Kampen, simply connected spheres — Hatcher Ch. 1 | Hurewicz: 545–1348 (simply connected from an open cover; two-open-cover van Kampen setup and uniqueness half), 1353–1466 (suspension simply connected, Δⁿ contractible); SingularHomology: 18734–19048 (loop subdivision over an open cover, `EuclideanSphere.simplyConnectedSpace`); LCP/BoundaryTopology: `FundamentalGroupVanKampen` (114 decls, pushout form), `TriangleRegularBaseFundamentalGroup` 8622–8767 | `Lib/AlgebraicTopology/FundamentalGroup/{VanKampen,SimplyConnectedCover,TwoSimplyConnectedCover}.lean`, `Lib/Topology/Homotopy/{SuspensionSimplyConnected,LoopSubdivision}.lean`, `Lib/AlgebraicTopology/FundamentalGroupoid/SimplyConnectedSphere.lean` | pure move (the sphere and loop-subdivision blocks are adapted from Mathlib PR #28246 and are upstream follow-ups) | ≈2,800 | A | GLM |
| **C** | Hurewicz theorem in every degree — Hatcher Thm 4.32; Kuhn triangulation of the cube; homotopy extension for (Δⁿ, ∂Δⁿ); prism operator | Hurewicz: 85–540, 1479–2144, 2152–3818 (cross product H₁ ⊗ Hₙ), 3840–8301 (degree 2), 8306–14990 (degree 3), 15000–23314 (general-n machinery, degrees 4, 5), 23444–23654; Recognition: 112–1550 (degree 6), 1737–1955 (cube → sphere), 2334–2579 (cell filling), 3816–4044 (Hopf degree theorem) | `Lib/AlgebraicTopology/Hurewicz/{SimplexCube,HomotopyExtension,PrismOperator,Straightening,CubeTriangulation,CubeGluing,Subdivision,CubeChainDecomposition,Degree,HopfDegree,CubeSphere}.lean`, `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`, `Lib/Topology/Homotopy/CellFilling.lean` | generalize-then-move: one theorem `(n ≥ 2) [SimplyConnectedSpace X] (∀ 2 ≤ k < n, Subsingleton (π_ k X x)) : Additive (π_ n X x) ≃ₗ[ℤ] H_n X` replaces the five copies; missing general pieces: `cubeChain_eq_sum_simplices` for all n (now n = 4, 5) and the recursive normalization tower | ≈25,000 → ≈11,000 | A | Kimi |
| **D1** | Morse theory I: Morse lemma, Morse functions, gradient-like fields, flows, regular levels, handle attachment — Milnor *Morse Theory* §2–3; h-cobordism Thm 2.5; Lee Thm 4.5, Cor 5.14, Thm 9.12 | DifferentialTopology: 85–9042, 14780–14981, 18259–19186 (smooth dependence of flows), 19195–20129 (Morse index), 30241–30355; SphereTopology: 7318–8708 (handle-attachment exact sequence, ordered critical points, minimum disc, Reeb two-disc decomposition, regular sublevel sets), 2595–2680; SingularHomology: 5310–5859 (handle/disc retractions); Recognition: 1612–1640 (atlas transport), 2090–2333, 3197–3453 (cylinder ball, HEP), 11149–11254 (Reeb) | `Lib/Analysis/Calculus/MorseLemma.lean`, `Lib/Analysis/ODE/SmoothFlow.lean`, `Lib/Geometry/Manifold/{InverseFunction,ChartedSpace/Transport,Flow/Compact,Flow/HeightTranslating,RegularLevel}.lean`, `Lib/Geometry/Manifold/Morse/{Basic,Existence,GradientLike,Handle,HandleAttachment,SublevelSets,Index,SurgeryWindows,Reeb}.lean`, `Lib/Topology/Homotopy/{DiskCylinder,CylinderHEP,HandleRetraction}.lean` | pure move (hazards: `letI := RegularLevel.chartedSpace` inside statements; `Fact (finrank = n+1)` instances; `Classical.propDecidable` wrappers) | ≈15,000 | — | GLM |
| **D2** | Morse theory I′: Whitney embedding, projection bundles, tubular neighbourhoods, collars, finite cell structures — Lee Thm 6.15, 6.24, Ch. 10; Milnor *Morse Theory* Thm 3.1, 3.5; h-cobordism Thm 3.4 | DifferentialTopology: 10392–14114 (Euclidean embedding, projections, `ProjectionBundle`, tubular neighbourhood, collars, level diffeomorphisms, `SurgeryWindows`/`AdaptedWindows` structures); SingularHomology: 28353–29652 (handle core ≃ cell, cell-attachment cover); Recognition: 2580–2903 (core attachment), 2904–3162, 3538–3809 (finite cells, compact manifold ≃ finite cell complex) | `Lib/Geometry/Manifold/{WhitneyEmbedding,VectorBundle/ProjectionBundle,Tubular,Collar}.lean`, `Lib/Geometry/Manifold/Morse/CellStructure.lean`, `Lib/Topology/Homotopy/CellAttachment.lean` | pure move | ≈12,000 | D1; A for the cell-attachment homology rows | GLM |
| **E1** | Morse theory II: rearrangement, cancellation, births — h-cobordism Thm 4.1, 4.8, 5.4, 8.1 | SingularHomology: 5859–15299 (field rescaling, time change, level flow cylinder, isotopy realization, phase charts, transverse germs, field-chart gluing, cubic model, band Lyapunov function, `remove_morse_band_pair`, `cancel_of_transverse_level_isotopy`), 28261–28353; DifferentialTopology: 14132–14773, 14992–18213 (cubic model and its flow, model cancellation, isotopy suspension), 20179–20983, 28637–28926 (interval translation); SphereTopology: 3008–3717, 5000–6556 (plateau weights, **Rearrangement Theorem**, index ordering, first cancellation), 8943–9512 (superfluous minima, minimal systems, duality f ↦ −f), 9887–9960, 10017–10431 (self-indexing, disc isotopy), 11026–11878 (Morse birth) | `Lib/Geometry/Manifold/Morse/{Cubic,CubicFlow,BandLyapunov,Cancellation,Rearrangement,IndexOrdering,SuperfluousMinima,Birth,Duality}.lean`, `Lib/Geometry/Manifold/Flow/{TimeChange,PhaseChart,LevelCylinder,FieldChartGluing}.lean`, `Lib/Analysis/Calculus/IntervalTranslation.lean` | pure move (all stated for general dimension m and general model space E) | ≈20,000 | D1, D2 | GLM |
| **E2** | Transversality, general position, isotopy extension, Whitney immersion/embedding — Hirsch Ch. 2–3, 8; Guillemin–Pollack Ch. 2; Milnor TDV §2–3 | DifferentialTopology: 9043–9396, 9974–10223, 17206–17544, 20996–22206, 22263–23890, 23903–27168 (immersion/embedding; generalize `Plane := ℝ × ℝ`, `5 ≤ finrank G`, `finrank E = 2`), 27462–28240, 30435–30589, 30616–30888; SingularHomology: 4359–5310, 15299–16000, 19058–19220, 23000–24933 | `Lib/Geometry/Manifold/Transversality/{Basic,Sard,Parametric,Ambient,GeneralPosition}.lean`, `Lib/Geometry/Manifold/Isotopy/{Supported,Germs,Linearization,DiskTheorem,Homogeneity}.lean`, `Lib/Geometry/Manifold/Immersion/{Relative,Arc,FrameChart}.lean`, `Lib/AlgebraicTopology/SphereMaps/Nullhomotopic.lean` | mostly pure move; generalize the 2-manifold-in-dimension-≥ 5 immersion chain to `2k ≤ n` | ≈12,000 | D1 | Kimi |
| **F** | Whitney trick, intersection numbers, handle slides, integer-matrix reduction — h-cobordism §6–7 (Thm 6.4, 7.8); Smale 1961 §4–5; Hatcher Prop 2.30 | SingularHomology: 16000–28261 (signed intersection numbers, strip/normal data, Whitney bigon model, framings, filling lemma, graph motion, rank-3 Whitney model, belt cancellation step); SphereTopology: 2680–2967, 9532–9878, 14839–15295, 18068–18588 (handle chain complex, `IntegerPresentation`); DifferentialTopology: 27220–27329, 28344–28604, 28935–30219 (arc tubes, `LongitudinalTubeMotion`); Recognition: 4078–10476 (attaching-sphere classes, sublevel exactness, intersection matrix, surgery cut transport, sheet passage / handle slides / transvection algebra, local degree = sum of signs, single intersection) | `Lib/Geometry/Manifold/Whitney/{IntersectionNumber,StripNormalData,BigonModel,Framing,Filling,GraphMotion,Trick,BeltCancellation,ArcTube,LongitudinalMotion}.lean`, `Lib/Geometry/Manifold/Morse/{AttachingClass,IntersectionMatrix,HandleSlide,SingleIntersection}.lean`, `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean`, `Lib/Algebra/Module/IntegerPresentation.lean` | generalize-then-move: sheets of dimensions p + q = n (now 3 + 2 = 6), handle index k (now 2/3), `finrank E = 6` (37 sites in Recognition) → n ≥ 5 with 3 ≤ k ≤ n − 3 or π₁-trivial levels; the transvection / integer-presentation algebra is a pure move and lands first | ≈22,000 | A, D1, D2, E1, E2 | Kimi |
| **G** | Smale's recognition theorem (generalized Poincaré, smooth, compact) — Smale 1961 Thm A; h-cobordism Thm 9.1 | SphereTopology: 3778–4876, 8709–8882, 10489–13361 (embedded discs in a homotopy sphere, index-1/2 cancellation, handle trade, minimal ordered system without outer indices), 18589–18831; Recognition: 10477–11148, 11255–11317 (`homeomorphic_sixSphere_of_homotopySixSphere`); SingularHomology: 19048–19058, 19220–19302 | `Lib/Geometry/Manifold/Morse/{MiddleBlocks,HandleTrade,MinimalSystem}.lean`, `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` | per decision Q1: keep n = 6, generalize only the model space (the theorem already takes an arbitrary `E` with `finrank ℝ E = 6`); move into `Lib/` with the six-sphere abbreviations consolidated on `Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`; the relation to Mathlib's `proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` (topological, all n, Euclidean model) is recorded in the file docstring | ≈4,500 | C, D1, D2, E1, E2, F | Kimi |
| **H** | Complex analysis: Riemann mapping, Schwarz reflection, boundary extension, Möbius transformations, ∂̄ / Cousin problem, holomorphic square roots — Ahlfors Ch. 3–6; Rudin 13–14; Forster §5, §13–14; Hörmander Ch. I | LCP/AnalyticFillings: `RiemannMapping` core 4369–5578 with the 31 `_root_.Complex.*` steps 4711–5413 (the triangle part 5579–9750 stays), `RiemannBoundary` + `SchwarzReflection` (4409–9121, interleaved), `RiemannSphere` 3581–4019, `TriangleRiemannNormalization` 4149–4266, three generic lemmas of `TriangleUniformizationGluing` (`contMDiff_of_continuous_of_finite`, `contMDiff_symm_of_contMDiff`, `biholomorphOfHomeomorph`); LCP/PeriodConstruction: `HolomorphicCousin` 15593–17278, `AnalyticRootCover(+Continuation)` 12060–13206, `RiemannSphere` 8012–8082 | `Lib/Analysis/Complex/{RiemannMapping,RiemannMapping/Steps,SchwarzReflection,BoundaryExtension,Mobius,DBar,Cousin,SquareRoot}.lean`, `Lib/Geometry/Manifold/Instances/RiemannSphere.lean`, `Lib/Geometry/Manifold/Complex/Biholomorph.lean` | pure move (two of the 31 steps duplicate `private` lemmas of Mathlib's `Analysis/Complex/RiemannMapping.lean`; keep them until an upstream PR de-privatizes them — decision Q6) | ≈4,900 | — | GLM |
| **I** | Quotient manifolds, coverings, two-chart bundles, mapping torus and Wang sequence, split extensions — Forster §1–5; Hatcher §1.3, Ex 2.48; Bredon III.3 | LCP/PeriodConstruction: `LocalOrbitQuotient`, `OnePointAtlas`, `TwoAffineCharts`, `FreeActionLocus`, `BranchedQuotientAtlas`; LCP/LocalModels: `CoveringQuotient`, `DiscreteQuotient`, `MappingTorus` (6899–8395), `ThreefoldHomologyFinitenessRetraction` 8731–8924 (a generic sublevel retraction, misnamed); LCP/CuspFilling: `InvariantSubsetQuotient`, `CoveringOrthant`, `ProductRestriction`, `CuspRetraction.Patching` 490–631; LCP/AnalyticFillings + BoundaryTopology: `DiagonalQuotient`; LCP/BoundaryTopology: `TwoOpenTransition`, `SplitGroupExtension`, `MappingTorusHomology` 3988–4609, `TwistGroup`; LCP/IntegralHomology: `MappingTorusHomology` 7576–8688 | `Lib/Geometry/Manifold/Quotient/{LocalOrbit,Atlas,Covering,Lattice}.lean`, `Lib/Geometry/Manifold/{OnePoint,ProjectiveLine}.lean`, `Lib/Topology/Algebra/FreeActionLocus.lean`, `Lib/Topology/Covering/{Quotient,DiagonalQuotient}.lean`, `Lib/AlgebraicTopology/FundamentalGroup/DiagonalQuotient.lean`, `Lib/Topology/FiberBundle/TwoOpenTransition.lean`, `Lib/GroupTheory/{SplitExtension,PresentedGroup/CentralTwist}.lean`, `Lib/Topology/MappingTorus/{Basic,HomologyCover,WangAlgebra,Wang}.lean`, `Lib/Topology/Homotopy/{SublevelRetraction,LocalCollapse}.lean` | pure move (`TwistGroup`: exponents 3, 4 may stay pinned) | ≈5,700 | A (Wang sequence only) | GLM |
| **J** | Homology of tori, Pontryagin product, exterior-power coordinates — Hatcher Ex 2.48, Cor 3.28, §3.C | LCP/CuspFilling: `PeriodTorusHigherHomology` 13745–15977 (H_n(Tʳ) ≅ ℤ^{C(r,n)}); LCP/Specialization: `PeriodTorusHigherHomology` 2463–8499 (rank 4), `PeriodTorusHigherHomologyPontryagin` 3142–6154, `PeriodTorusHigherHomologyExterior` 6636–6882; FiniteCore 339–392 | `Lib/AlgebraicTopology/SingularHomology/{Torus,TorusExterior,Pontryagin}.lean`, `Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean` | pure move (torus, Pontryagin, exterior basis) + generalize rank 4 → r (`Lattice := Fin 4 → ℤ` is the only obstacle) | ≈5,600 | A; C (`CrossProduct.lean`) if the rank-4 block uses the cross product | Kimi |

### Dependency DAG

```
A ──┬──> B
    ├──> C ──────────────────────────┐
    ├──> I (Wang only)               │
    ├──> J                           │
    └──> D2 (cell-attachment rows)   │
D1 ─┬──> D2 ──> E1 ──┐               │
    └──> E2 ─────────┼──> F ──> G <──┘
H  (independent)     │
```

Independent from the start: A, D1, H. GLM order: A → D1 → D2 → E1 → H → I → B. Kimi order:
C (after A) → J → E2 (after D1) → F (after A, D1, D2, E1, E2) → G (after C, F). While blocked,
each model takes its next independent lane.

## 3. Validation recipe (every lane, every commit)

1. `git diff --check`; `python3 scripts/lib_stock_census.py --check` passes; after a move,
   `python3 scripts/lib_stock_census.py --update` lowers the baseline and the new baseline is
   committed with the code.
2. Build only what changed, in order: the new `Lib` modules (`lake build Lib.<Module>`), then
   every consumer of the moved prefixes (`lake build Hopf.<Consumer>`; the consumers per prefix
   are: `SingularMayerVietoris` → IntegralHomology, Specialization, Hurewicz, BoundaryTopology,
   Recognition; `FirstHurewicz` → Specialization, IntegralHomology, Recognition,
   BoundaryTopology; `PeriodTorusHigherHomology` → IntegralHomology, Recognition, LocalModels,
   FiniteCore; `MappingTorus` → IntegralHomology, BoundaryTopology; `CoveringQuotient` →
   GlobalAssembly, AnalyticFillings, PeriodConstruction; `RiemannMapping` → BoundaryTopology;
   `Smale`/`Degree`/`ManifoldAtlasTransport` → Final; the `*Hurewicz` prefixes → Recognition),
   then once per lane `lake build Hopf.Final` and `lake build Solution`.
3. Axiom probe: add the lane's top theorems to `Lib/AxiomAudit.lean`; `lake env lean
   Lib/AxiomAudit.lean` must show `[propext, Classical.choice, Quot.sound]` for each. Top
   theorems: A `SingularMayerVietoris.exact_at_ambient`,
   `SphereHomology.unitSphere_homology_subsingleton`,
   `Smale.LinearSphereAction.homology_eq_sign_smul`; B `simplyConnectedSpace_of_open_cover`,
   `FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv`; C the general
   `hurewiczLinearEquiv` and its n = 6 instance; D1 `Smale.ManifoldMorse.exists_morse_function`,
   `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn`,
   `Smale.ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits`,
   `Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points`; D2
   `Smale.NativeEuclideanEmbedding.exists_tubularNeighborhood`,
   `Degree.MorseCells.built_of_compact_smooth_manifold`; E1
   `Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection`,
   `MorseCancel.cancel_of_transverse_level_isotopy`,
   `MorseCancel.exists_excellent_indexed_morse_birth`; E2
   `Smale.NativeTransversality.exists_ambient_transverse_diffeomorph`,
   `Smale.ManifoldImmersion.exists_compact_embedding_of_immersion`,
   `MorseCancel.exists_isotopic_pointMoving_of_path`; F
   `Smale.TubularBigon.exists_rankThree_relative_cancellation` (generalized),
   `MorseCancel.primitive_row_has_unit_after_column_additions`; G
   `Smale.homeomorphic_sixSphere_of_homotopySixSphere` (statement unchanged); H
   `RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`,
   `HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution`,
   `AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros`; I
   `MappingTorusHomology.wang_exact_at_mappingTorus`, `SplitGroupExtension.mulEquiv`; J
   `PeriodTorusHigherHomology.productTorusHomologyEquiv`.
4. The Comparator verdict is unchanged: `lake exe comparator comparator/config.json`. No lane
   changes the statement of any `Hopf/` declaration; lanes C and G change only the *proofs*
   of `Degree.threefoldHomotopyEquiv` and `Smale.homeomorphic_sixSphere_of_homotopySixSphere`.
5. Definition of done per lane: `Lib/README.md`.

## 4. Decisions (defaults; each is DEFAULT, flippable by the repository owner)

- **Q1 — DEFAULT, flippable.** Lane G keeps n = 6 and generalizes only the model space.
  Generalization to n ≥ 5 (Smale) or n ≥ 6 (Milnor Thm 8.1 as written) is the follow-up lane
  G′.
- **Q2 — DEFAULT, flippable.** Transitional `namespace Mathoverflow1973` with `export` shims
  is allowed on first landing; the rename is a second commit per lane.
- **Q3 — DEFAULT, flippable.** The subdivision / small-chains part of lane A
  (SingularHomology 2088–3466) is moved as-is.
- **Q4 — DEFAULT, flippable.** Lanes B, I, J are full moves from the public tail. An
  equivalent formalization of the two-open-cover van Kampen theorem, of barycentric
  subdivision / small chains, of the mapping-torus basics and of the exterior-power minor
  formula exists outside this tree; a later de-duplication is the owner's call.
- **Q5 — DEFAULT, flippable.** Lane D is split into D1 and D2.
- **Q6 — DEFAULT, flippable.** The 31 Riemann-mapping steps go to `Lib/` now; a Mathlib PR
  against `leanprover-community/mathlib4#33505` is a named follow-up.
- **Q7 — DEFAULT, flippable.** `Hopf/FiniteCore.lean` 214–320 is treated as project code and
  left out.
- **Q8 — DEFAULT, flippable.** No `Hopf/` namespace is touched in the setup commit; the
  131-declaration `RiemannMapping` imprecision stays in the baseline.

## 5. Follow-up lanes (not assigned)

- **G′** — Smale's theorem for n ≥ 5 (or n ≥ 6): replace the n = 6 coincidence "middle indices
  = {2, 3, 4} and index 4 is index 2 of −f" by the range 2 ≤ k ≤ n − 2; needs lane F at full
  generality.
- **Mathlib PRs.** Template of a finished extraction: `github.com/fabianx-ai/mathlib4` PR #4
  (`Mathlib/AlgebraicTopology/Hurewicz/{CycleClasses,SimplexPaths,PeriodicLoop,H1Character,
  Degree1}.lean`, the degree-one Hurewicz theorem). Candidates in order of readiness: Morse
  lemma (D1); smooth dependence of flows (D1); `ProjectionBundle` and the tubular neighbourhood
  theorem (D2); Mayer–Vietoris and H_*(Sⁿ) (A); Kuhn triangulation and the Hurewicz theorem
  (C); Wang sequence and H_*(Tʳ) (I, J); Riemann-mapping steps against #33505 and the
  simply-connected-sphere block against #28246 (H, B); Cousin problem (H).
- **Universe lift.** All singular-homology statements use `(X : Type)`; lifting to `Type u`
  is a separate pass after lane A.
- **Sphere consolidation.** Five spellings of the same sphere (`SphereHomology.UnitSphere n`,
  `Smale.Hemisphere.Sphere n`, `Smale.SixSphere`, `SixSphere`, `SixSphereCube.StandardSphere`)
  and two circle models (`Circle` ⊂ ℂ, `AddCircle 1`) are unified in lane G.

## 6. Honest limits of the census

Classification is at the level of statements read, never elaborated; line totals for
`Recognition` and `DifferentialTopology` are ±300; six long Morse/Whitney interiors were
classified from their declaration lists and one or two statements each (DifferentialTopology
4439–4781, 5337–5908, 15336–16914, 18106–18213, 20698–20983, 28935–30219; Recognition
6234–9470). Mathlib status is grep-based on the pinned checkout. `Hopf/FiniteCore.lean`
214–320 (26 root-level declarations) and the `(root)` singletons inside `Hopf/LCP` are
unclassified. Milnor's h-cobordism theorem numbers were verified against the printed text;
Hatcher's Thm 4.32 / 4.37 were verified; other Hatcher numbers are from the 2002 edition.

## 7. Structural hazards every lane must respect

1. Import chain is linear: `DifferentialTopology → SingularHomology → SphereTopology →
   Hurewicz → FiniteCore → Shortcuts → LCP.LocalModels → CuspFilling → Specialization →
   PeriodConstruction → AnalyticFillings → GlobalAssembly → BoundaryTopology →
   IntegralHomology → Recognition → Final`.
2. File-level pragmas that must travel with moved code: `set_option maxSynthPendingDepth 3`;
   `open Set Function Filter Manifold Topology`; the `open scoped …` list; `noncomputable
   section`; `universe u v`; the local notations `≫ₚ` (`Path.trans`) and `∣[k]`.
3. Per-declaration `attribute [local instance …] … in` wrappers (about 150 per tail file;
   mostly `Classical.propDecidable` at priority 100, plus load-bearing
   `@[instance_reducible]` definitions such as `Smale.RegularLevel.chartedSpace`,
   `PeriodTorusHigherHomology.integerLinearMapModule/integerTensorModule`,
   `ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts`). Many theorem statements
   contain `letI := Smale.RegularLevel.chartedSpace hf hreg`.
4. Blocks interleave every few hundred lines (`AdaptedWindows`/`MorseCancel`/`Degree` in
   SphereTopology and Recognition); cut by declaration, not by line, and re-check boundaries
   with the regex in `scripts/lib_stock_census.py`.
5. About 250 auto-named `*_mo1973_NNNN` private helpers and about 40 `instLocalN` anonymous
   instances need real names in the rename commit.
6. Consumers with hundreds of references (`SingularMayerVietoris.` ≈1,450 in IntegralHomology,
   ≈1,333 in Specialization; `PeriodTorusHigherHomology.` ≈1,657 in IntegralHomology;
   `MappingTorus.` ≈653 in IntegralHomology; `Smale.` ≈3,000 in SphereTopology) are re-routed
   through `export` shims first (Q2).
